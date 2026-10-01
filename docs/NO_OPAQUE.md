# No opaque definitions

Status: **draft for review** (2026-10-01). To be implemented after `docs/SCOPE_CONTAINMENT.md`.

## 1. The change

`opaque def` is removed. Every definition is transparent: it reduces during checking and evaluation. Only the trusted
prelude introduces names that do not compute, its axioms and builtins, as only it may declare axioms today.

So a closed value of a family reduces to a constructor unless it depends on a prelude axiom.

## 2. Why

**An opaque application is a second kind of stuck value.** The kernel reasons around it in many places, each a rule
of its own:
- apartness: an opaque application clashes with nothing;
- implicit projection: its arguments were projection positions until `SCOPE_CONTAINMENT`;
- deferred evidence, which it stores among its arguments;
- termination metrics, which may not be of an opaque type;
- `LinearGlobal`;
- the sealing argument that every value of a sealed family was built by its module.

Two soundness holes went through these rules:
- **Bug #5:** `Eq.refl` hidden behind an opaque definition made a proof scrutinee that no probe could see through, and
  `False` followed.
- **The scope review's H1:** an implicit read an atom out of an opaque application's arguments, so a lease was made
  after its scope closed.

**Nothing needs it.** The bundled prelude, the GPU prelude, the GPU library and its proofs, and the examples declare
no opaque definition. Every use is in the test suite: about 60, across 20 files. They do one of two things:
- **Stand for a value that never reduces.** A parameter does the same: applying an abstract `f: Peano -> Peano` is
  stuck exactly as an opaque `f` is.
- **Hide a proof's body,** in exploit regressions. A proof-valued declaration never runs anyway, so hiding its body
  added nothing but the exploit.

**It matches axioms.** Since 2026-09-29 only the trusted prelude declares axioms, so that names which never compute
are audited (obligations T1–T5). An opaque definition was the one way left for any module to make such a name.

## 3. What changes in the language

- **Syntax.** A declaration is `def`, `axiom` (trusted prelude only), `inductive`, `struct` or `mutual`. `opaque` is no
  longer a keyword, so `opaque def` is a parse error and `opaque` is an ordinary identifier (decision 2).
- **Closed canonicity.** A closed value of a family reduces to a constructor unless an axiom or builtin of the trusted
  prelude blocks it. Kernel code still may not assume constructor heads, because of prelude axioms, `Quot`, and
  open terms while checking.
- **Every rule that names opaque definitions** names prelude axioms instead, or nothing:
  - apartness: no exception for opaque applications;
  - projection positions: family heads and the prelude's type formers (as `SCOPE_CONTAINMENT` §4 has it);
  - deferred evidence: "any other head, an axiom's say";
  - termination metrics: not of an axiomatized type;
  - `LinearGlobal`: a definition whose type is linear;
  - sealing: a neutral of a sealed family is a parameter, a blocked computation, or an axiom application;
  - kernel.md "Maintained invariants", item 9: axiom and quotient values may remain closed neutrals.

## 4. What changes in the kernel

- Delete `isOpaque` from `SurfaceAst` and `CoreAst` `ConstDecl`, the `opaque` keyword (`LanguageParser.opaqueP`,
  `IdentifierSyntax`), the elaborator's "mutual definitions cannot be opaque" check, and the interpreter's publication of
  an opaque definition as a `Symbol` head. Axioms keep `Symbol`.
- Update the comments that list opaque constants (`Projection`, `ValueEquivalence`, `InductiveChecks`,
  `Interpreter`).

## 5. Tests

- **A stuck value.** An opaque constant becomes a parameter of the enclosing definition, and an opaque application an
  application of a function parameter. If a test needs a closed neutral, it uses an axiom in the test prelude
  (`TestPrelude.rac`).
- **An exploit regression.** It is kept in the form that is still writable: the hiding definition becomes a function
  parameter, so the scrutinee is still a stuck application, not a variable. If the hazard can no longer be written at
  all, the test is deleted and its commit message says so.
- **A test of opacity itself** (does not unfold, cannot be mutual) is deleted.
- **New:** `opaque def` is a parse error.

The scope review's probes `a3` and `a4` become tests with function parameters in place of the opaque definitions.
They must still be rejected, by `SCOPE_CONTAINMENT`'s projection restriction.

`gpu/check.sh` is unaffected (no use), and the generated kernels stay byte-identical.

## 6. Steps

One step after the scope fix lands: an implementer at medium effort, hostile review at high effort. The reviewer
looks for a rule that still mentions opaque definitions, and for a regression test whose hazard was lost in the
rewrite.

## 7. Decisions for review

1. **Removed everywhere**, the trusted prelude included, rather than restricted to it as axioms are. No prelude uses
   it, and an audited prelude that needs a name that never computes declares an axiom.
2. **`opaque` stops being a keyword**, rather than staying reserved for a diagnostic that explains the removal.
3. **No replacement** for hiding a definition's body from conversion. If cost ever needs it, a design that keeps
   closed canonicity would come first, such as a definition that conversion unfolds only on demand.
