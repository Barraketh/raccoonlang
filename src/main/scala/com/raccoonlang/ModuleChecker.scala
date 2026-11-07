package com.raccoonlang

import com.raccoonlang.ModuleLoader.{LoadFailure, LoadedSource, Loader, Module}

import java.nio.file.Path
import scala.collection.mutable
import scala.util.control.NonFatal

/**
 * Checks entries module by module, and keeps each module's results for later entries and runs (docs/namespaces.md,
 * "Imports").
 *
 * A module means what it means standalone: it is elaborated and checked against exactly its import closure, assembled
 * in its own depth-first import order, so its results are the same in every importer, and are computed once. A module
 * begins where its first import ended, with the rest of its closure's effects replayed in its order
 * (`Elaborator.declare`, `TypecheckEnv.withEffect`): the first import's closure, then the import, is a prefix of its
 * own closure (`Module.closure`). A redeclared name is a clash there, as it is when the closure is checked afresh.
 *
 * An entry is checked as a standalone run checks its program: the modules of its closure, in depth-first order, then
 * the entry, elaborate; their declarations pass the trust checks; they check; then the entry's body runs. Each step
 * reports the first failure in that order, so an entry is rejected with the error a fresh check of it meets first. A
 * module that fails fails every entry whose closure holds it, with its own error, located in it.
 *
 * Results are kept by module key (`Module.key`) in one session per configuration (`SessionKey`), at most one per
 * canonical path, the latest; `sweep` drops those whose imports' results are gone. The evaluator is single-threaded,
 * so one thread at a time uses a checker.
 */
final class ModuleChecker(maxSessions: Int = 4) {
  import ModuleChecker._

  private val sources = new ModuleLoader.Sources
  private val sessions = mutable.LinkedHashMap.empty[SessionKey, Session]
  /** Each custom prelude read, by name, the latest version, with its source's digest. */
  private val preludeFiles = mutable.HashMap.empty[String, (String, Prelude.Config)]

  /** A run of the CLI under `options`, which reads each file at most once. */
  def run(options: Options): Run = new Run(options)

  /** Drops the results no current result depends on (`Session.sweep`). */
  def sweep(): Unit = sessions.valuesIterator.foreach(_.sweep())

  final class Run private[ModuleChecker] (options: Options) {
    private val snapshot = sources.snapshot()
    private val loaders = mutable.HashMap.empty[SessionKey, Loader]

    /**
     * The run's prelude and what identifies it, a custom prelude by its file's path and source: it is parsed and
     * elaborated once per version of the file, and a file that fails to read, parse or elaborate fails here.
     */
    lazy val prelude: (Prelude.Config, String) =
      options.prelude match {
        case PreludeSource.Bundled => (Prelude.default, "bundled")
        case PreludeSource.Absent  => (Prelude.none, "none")
        case PreludeSource.Given(name, config) => (config, s"given\u0000$name")
        case PreludeSource.File(path) =>
          val (name, source) = Prelude.read(path)
          val digest = ModuleLoader.sha256(source)
          val config = preludeFiles.get(name) match {
            case Some((read, config)) if read == digest => config
            case _ =>
              val config = Prelude.fromSource(name, source)
              preludeFiles(name) = (digest, config)
              config
          }
          (config, s"$name\u0000$digest")
      }

    /**
     * The entry at `entry`, written `shown`, checked with its imports over the run's source roots, or, with none, the
     * entry's directory. `listener` hears its steps. The prelude must have been read (`prelude`).
     */
    def check(entry: Path, shown: String, listener: Listener = Listener.silent): EntryResult = {
      val roots =
        (if (options.roots.isEmpty) Vector(entry.toAbsolutePath.normalize.getParent) else options.roots)
          .map(_.toAbsolutePath.normalize)
      val key = SessionKey(roots, prelude._2, options.stackBytes)
      val session = sessions.remove(key).getOrElse(new Session(prelude._1))
      sessions(key) = session
      if (sessions.size > maxSessions) sessions.remove(sessions.head._1)
      val loader = loaders.getOrElseUpdate(key, new Loader(roots, prelude._1, snapshot))
      session.check(loader, entry, shown, options.allowUserAxioms, listener)
    }
  }
}

object ModuleChecker {

  /**
   * Where a run's prelude comes from: the bundled one, none, a file, or a configuration, as tests give, which its `name`
   * identifies to the checker.
   */
  sealed trait PreludeSource
  object PreludeSource {
    case object Bundled extends PreludeSource
    case object Absent extends PreludeSource
    final case class File(path: Path) extends PreludeSource
    final case class Given(name: String, config: Prelude.Config) extends PreludeSource
  }

  /**
   * A run's configuration, as the CLI's flags give it: source roots, the prelude, whether user axioms are allowed, and
   * the stack size of the thread the run's checks use, which decides where evaluation is too deep.
   */
  final case class Options(
      roots: Vector[Path],
      prelude: PreludeSource,
      allowUserAxioms: Boolean,
      stackBytes: Long
  )

  /** What hears an entry's steps; the CLI logs them. */
  trait Listener {

    /** The entry and its imports loaded. */
    def loaded(): Unit = ()

    /** The entry's modules elaborated; `axioms` are the user axioms they declare, in depth-first order. */
    def elaborated(axioms: Vector[String]): Unit = ()

    /** The module at `module` checked afresh: no result of it was kept from an earlier entry or run. */
    def checked(module: Path): Unit = ()
  }

  object Listener {
    val silent: Listener = new Listener {}
  }

  /**
   * An entry's verdict: the sources its error may be located in, the entry's first, as `ErrorReporter` falls back to it;
   * its user axioms, once its modules elaborated; and why it was rejected, or its body's result, if it has one.
   */
  final case class EntryResult(
      sources: Vector[LoadedSource],
      axioms: Vector[String],
      outcome: Either[Throwable, Option[BodyResult]]
  )

  /** What an entry's body evaluated to (`Interpreter.runBody`), and how the CLI prints it (`Interpreter.show`). */
  final case class BodyResult(value: Value, printed: String)

  /**
   * What a module's results depend on beyond its key: the source roots its imports resolve over, absolute and
   * normalized, the prelude, and the checking thread's stack size. `--no-user-axioms` is not in it: it changes no
   * module's results, only whether an entry's trust checks pass, which run before its modules check.
   */
  private final case class SessionKey(roots: Vector[Path], prelude: String, stackBytes: Long)

  private final case class Elaborated(module: Elaborator.ElaboratedModule, scope: Elaborator.Scope)
  private final case class Checked(env: TypecheckEnv, effect: ModuleEffect)

  /**
   * A module's results, for the module whose key is `key` and whose imports are `imports`, by path and key; each is
   * computed when first needed, and null until then.
   */
  private final class Record(val key: String, val imports: Vector[(Path, String)]) {
    var elaborated: Either[Throwable, Elaborated] = _
    var checked: Either[Throwable, Checked] = _
    var result: Either[Throwable, Option[BodyResult]] = _
  }

  private def attempt[A](body: => A): Either[Throwable, A] =
    try Right(body)
    catch { case NonFatal(e) => Left(e) }

  /** The results of the modules checked over `prelude` under one configuration. */
  private final class Session(prelude: Prelude.Config) {
    private val records = mutable.HashMap.empty[Path, Record]
    private lazy val preludeScope = attempt(Elaborator.preludeScope(prelude))
    private lazy val preludeEnv = attempt(Interpreter.topLevel(Interpreter.initialEnv(prelude)))

    /** `module`'s record, a new one when its key is not the recorded one's. */
    private def record(module: Module): Record =
      records.get(module.path) match {
        case Some(record) if record.key == module.key => record
        case _ =>
          val record = new Record(module.key, module.imports.map(imported => imported.path -> imported.key))
          records(module.path) = record
          record
      }

    /** Drops every record of an import result that is not the recorded one, and every record that depends on one. */
    def sweep(): Unit = {
      val live = mutable.HashMap.empty[Path, Boolean]
      def current(path: Path, key: String): Boolean =
        records.get(path).exists { record =>
          record.key == key && live.getOrElseUpdate(path, record.imports.forall { case (p, k) => current(p, k) })
        }
      records.filterInPlace { case (path, record) => current(path, record.key) }
    }

    /**
     * The state `module` begins in: `base` when it imports nothing; otherwise its first import's final state (`end`),
     * with every later module of its closure replayed in order (`replay`). A failed module fails it.
     */
    private def start[S](
        module: Module,
        base: => Either[Throwable, S],
        end: Module => Either[Throwable, S],
        replay: (S, Module) => Either[Throwable, S]
    ): Either[Throwable, S] =
      module.imports.headOption match {
        case None => base
        case Some(first) =>
          module.closure.drop(first.closure.length + 1).foldLeft(end(first))((state, next) => state.flatMap(replay(_, next)))
      }

    private def elaborate(module: Module): Either[Throwable, Elaborated] = {
      val record = this.record(module)
      if (record.elaborated == null)
        record.elaborated = start[Elaborator.Scope](
          module,
          preludeScope,
          elaborate(_).map(_.scope),
          (scope, next) => elaborate(next).flatMap(done => attempt(Elaborator.declare(scope, done.module.declared)))
        ).flatMap { scope =>
          attempt {
            val (elaborated, end) = Elaborator.elabModule(module.program, scope)
            Elaborated(elaborated, end)
          }
        }
      record.elaborated
    }

    /** `module`, checked; it elaborated, and its closure passed the trust checks. `listener` hears a fresh check. */
    private def check(module: Module, listener: Listener): Either[Throwable, Checked] = {
      val record = this.record(module)
      if (record.checked == null) {
        record.checked =
          start[TypecheckEnv](module, preludeEnv, check(_, listener).map(_.env), replay(_, _, listener)).flatMap { env =>
            elaborate(module).flatMap { elaborated =>
              attempt {
                val (end, effect) = Interpreter.checkModule(elaborated.module.decls, env)
                Checked(end, effect)
              }
            }
          }
        listener.checked(module.path)
      }
      record.checked
    }

    /** `env` with `module`'s effect, which checked, replayed; a clash is located at the redeclared name. */
    private def replay(env: TypecheckEnv, module: Module, listener: Listener): Either[Throwable, TypecheckEnv] =
      check(module, listener).flatMap { checked =>
        try Right(env.withEffect(checked.effect))
        catch {
          case clash: AlreadyDefined =>
            val declared = elaborate(module).toOption.iterator.flatMap(_.module.declared)
            Left(declared.find(_.parts.mkString(".") == clash.name).fold[TypeError](clash) { name =>
              TypeError.withSpan(clash, name.span)
            })
        }
      }

    /** `module`'s body's result, if it has one; it checked. */
    private def result(module: Module, body: Option[CoreAst.Term], listener: Listener): Either[Throwable, Option[BodyResult]] = {
      val record = this.record(module)
      if (record.result == null)
        record.result = body match {
          case None => Right(None)
          case Some(term) =>
            check(module, listener).flatMap { checked =>
              attempt {
                val value = Interpreter.runBody(term, checked.env)
                Some(BodyResult(value, Interpreter.show(value, TypeChecker.sourceSpan(term))))
              }
            }
        }
      record.result
    }

    /**
     * The first elaboration failure of `sequence`, an entry's closure then the entry, given that `failed` is its first
     * module that failed. Two modules before it whose names clash come first, though neither imports the other; when
     * `failed` is the entry, it began from its first import, whose own closure had no clash, so its own failure is
     * first.
     */
    private def firstElaborationFailure(sequence: Vector[Module], failed: Module): Throwable = {
      val own = elaborate(failed).left.getOrElse(throw WTF(s"${failed.path} elaborated"))
      if (failed eq sequence.last) own
      else
        sequence
          .takeWhile(_ ne failed)
          .foldLeft(preludeScope) { (scope, next) =>
            scope.flatMap(names =>
              elaborate(next).flatMap(done => attempt(Elaborator.declare(names, done.module.declared)))
            )
          }
          .fold(identity, _ => own)
    }

    /** The entry at `entry`, written `shown`, loaded by `loader` and checked (`ModuleChecker`). */
    def check(loader: Loader, entry: Path, shown: String, allowUserAxioms: Boolean, listener: Listener): EntryResult =
      (try Right(loader.load(entry, shown))
       catch { case failure: LoadFailure => Left(failure) }) match {
        case Left(failure) => EntryResult(failure.sources, Vector.empty, Left(failure.error))
        case Right(module) =>
          listener.loaded()
          checkLoaded(module, allowUserAxioms, listener)
      }

    private def checkLoaded(module: Module, allowUserAxioms: Boolean, listener: Listener): EntryResult = {
      val sequence = module.closure :+ module
      val sources = module.file.source +: module.closure.map(_.file.source)
      sequence.find(elaborate(_).isLeft) match {
        case Some(failed) => EntryResult(sources, Vector.empty, Left(firstElaborationFailure(sequence, failed)))
        case None =>
          val elaborated = sequence.map(elaborate(_).fold(throw _, _.module))
          val decls = elaborated.view.flatMap(_.decls)
          val axioms = Interpreter.axioms(decls).map(_.name)
          listener.elaborated(axioms)
          // Only a closure that passed the trust checks checks.
          val failure = Interpreter
            .trustViolation(decls, allowUserAxioms)
            .orElse(sequence.iterator.map(check(_, listener)).collectFirst { case Left(error) => error })
          EntryResult(sources, axioms, failure.map(Left(_)).getOrElse(result(module, elaborated.last.body, listener)))
      }
    }
  }
}
