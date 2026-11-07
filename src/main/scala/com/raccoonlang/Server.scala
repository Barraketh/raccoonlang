package com.raccoonlang

import java.io.{BufferedReader, ByteArrayOutputStream, InputStreamReader, OutputStream, PrintStream, PrintWriter, StringWriter}
import java.net.{StandardProtocolFamily, UnixDomainSocketAddress}
import java.nio.channels.{Channels, ServerSocketChannel, SocketChannel}
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters._
import scala.util.Using
import scala.util.control.NonFatal

/**
 * `raccoon-lang --serve`: CLI runs served over a Unix domain socket by one `ModuleChecker`, so module results carry
 * from one run to the next (`ModuleChecker`), and the prelude, the kernel and the JIT stay warm.
 *
 * A request is one line, a JSON object: `{"cwd": <dir>, "args": [<argument>...]}`, a single or batch run of the CLI
 * whose relative paths are read from `cwd`, or `{"stop": true}`. The reply is JSON lines: `{"out": <text>}` and
 * `{"err": <text>}`, what the CLI prints on its standard output and error, in order, then `{"exit": <code>}`. Runs are
 * served one at a time, as the evaluator is single-threaded, each on a thread of its own `--stack`. A run re-reads every
 * source it loads, so a result is never one of a source that changed.
 *
 * A server whose compiler classes changed since it started answers `{"restart": <reason>}` and stops instead: its
 * results, and the classes it would load next, are no longer the compiler's. `scripts/raccoon-client` is a client.
 */
object Server {

  /** Serves on `socket` until a stop request; the exit code. */
  def serve(socket: Path): Int = {
    val address = UnixDomainSocketAddress.of(socket)
    if (Files.exists(socket)) {
      val live =
        try { SocketChannel.open(address).close(); true }
        catch { case NonFatal(_) => false }
      if (live) {
        System.err.println(s"A server already answers on $socket")
        return 1
      }
      Files.delete(socket)
    }
    val listener = ServerSocketChannel.open(StandardProtocolFamily.UNIX)
    listener.bind(address)
    val identity = compilerIdentity()
    val checker = new ModuleChecker
    System.err.println(s"raccoon-lang serving on $socket")
    try {
      var serving = true
      while (serving) Using.resource(listener.accept())(connection => serving = handle(connection, checker, identity))
    } finally {
      listener.close()
      Files.deleteIfExists(socket)
    }
    0
  }

  /** Answers one request on `connection`; whether to keep serving. */
  private def handle(connection: SocketChannel, checker: ModuleChecker, identity: String): Boolean = {
    val reply = new Reply(Channels.newOutputStream(connection))
    val line = new BufferedReader(new InputStreamReader(Channels.newInputStream(connection), UTF_8)).readLine()
    val request =
      try Option(line).map(Json.parse).collect { case fields: Map[String, Any] @unchecked => fields }
      catch { case _: IllegalArgumentException => None }
    request match {
      // A client that only looked for the server sends nothing.
      case None if line == null => true
      case Some(fields) if fields.get("stop").contains(true) =>
        reply.exit(0)
        false
      case _ if compilerIdentity() != identity =>
        reply.send(Json.obj("restart" -> Json.quote("the compiler's classes changed since the server started")))
        false
      case Some(fields) =>
        val cwd = fields.get("cwd").collect { case dir: String => Paths.get(dir) }.filter(_.isAbsolute)
        val args = fields.get("args").collect { case items: Vector[Any] @unchecked if items.forall(_.isInstanceOf[String]) =>
          items.map(_.asInstanceOf[String])
        }
        (cwd, args.flatMap(Main.parseArgs).filterNot(cli => cli.serve || cli.waitForEnter)) match {
          case (Some(dir), Some(cli)) => run(cli, checker, dir, reply)
          case (Some(_), None) =>
            reply.err.println(Main.Usage)
            reply.exit(2)
            true
          case (None, _) =>
            reply.err.println("A request is {\"cwd\": <absolute directory>, \"args\": [<argument>...]}")
            reply.exit(2)
            true
        }
      case None =>
        reply.err.println("A request is one line of JSON")
        reply.exit(2)
        true
    }
  }

  /**
   * Runs `cli` as the CLI does, on a thread of its stack size, and replies. An error the CLI would not catch is reported
   * as the JVM reports it; one that leaves the JVM in doubt, unlike a stack overflow, stops the server.
   */
  private def run(cli: Main.CliArgs, checker: ModuleChecker, cwd: Path, reply: Reply): Boolean = {
    val (code, serving) =
      try (Execution.onStack(cli.stackBytes)(Main.run(cli, checker, cwd, reply.out, reply.err)), true)
      catch {
        case thrown: Throwable =>
          val trace = new StringWriter
          thrown.printStackTrace(new PrintWriter(trace))
          reply.err.print(s"Exception in thread \"main\" $trace")
          (1, thrown.isInstanceOf[StackOverflowError] || NonFatal(thrown))
      }
    checker.sweep()
    reply.exit(code)
    serving
  }

  /**
   * What identifies the compiler this server runs: the files of the class path entry its own classes come from, by
   * path, size and modification time.
   */
  private def compilerIdentity(): String = {
    val location = Paths.get(Main.getClass.getProtectionDomain.getCodeSource.getLocation.toURI)
    val files =
      if (Files.isDirectory(location)) Using.resource(Files.walk(location))(_.iterator.asScala.filter(Files.isRegularFile(_)).toVector)
      else Vector(location)
    ModuleLoader.sha256(
      files.sorted.map(file => s"$file ${Files.size(file)} ${Files.getLastModifiedTime(file).toMillis}").mkString("\n")
    )
  }

  /** A reply's JSON lines, and the CLI's two output streams, each line of which is sent as it is printed. */
  private final class Reply(stream: OutputStream) {
    def send(json: String): Unit =
      try {
        stream.write((json + "\n").getBytes(UTF_8))
        stream.flush()
      } catch { case NonFatal(_) => () } // A client that left misses the rest of its reply.

    private final class Chunks(field: String) extends OutputStream {
      private val buffer = new ByteArrayOutputStream
      override def write(b: Int): Unit = buffer.write(b)
      override def write(b: Array[Byte], off: Int, len: Int): Unit = buffer.write(b, off, len)
      override def flush(): Unit =
        if (buffer.size > 0) {
          send(Json.obj(field -> Json.quote(buffer.toString(UTF_8))))
          buffer.reset()
        }
    }

    val out = new PrintStream(new Chunks("out"), true, UTF_8)
    val err = new PrintStream(new Chunks("err"), true, UTF_8)

    def exit(code: Int): Unit = {
      out.flush()
      err.flush()
      send(Json.obj("exit" -> code.toString))
    }
  }
}
