# Nat normal forms

Nat values normalize to sums of products. Addition and multiplication are
associative and commutative, numerals compute, multiplying by a numeral
distributes, and powers of equal bases multiply by adding their exponents.
Nothing else distributes: a product of sums stays a product, and a power of a
product stays a power. The normal forms are canonical for exactly these laws, so
definitional equality decides them completely. Every operation takes time
linear in the size of its operands and result, so normalization needs no
limits, budgets, or fuel.

## Terms

- An **atom** is a Nat value that is neither zero nor a normal form: a
  variable, a stuck application (including a stuck native subtraction), a
  stuck match, or an axiom constant.
- A **numeral** is a closed natural number, stored as a `BigInt`.
- A **numeral power** is a factor with a known positive exponent, such as
  `x^2`. A **symbolic power** is a factor whose exponent is a Nat value with
  no known constant, such as `x^a` or `2^(a + b)`.
- The **operands** of a form are its factors' bases and symbolic exponents:
  the arguments of the Nat operations that built it.
- The **summands** of a form are its terms, plus its constant when the
  constant is nonzero.
- The **content** of a nonzero form is the greatest common divisor of its
  constant and coefficients. A form is **primitive** when its content is one.

## Scope and trust boundary

Nat and Bool are built into the kernel. `Kernel` declares `Bool` with `false`
and `true`, `Nat` with exactly `Nat.zero : Nat` and `Nat.succ : Nat -> Nat`, and
native `Nat.add`, `Nat.mul`, `Nat.pow`, `Nat.sub`, `Nat.pred`, `Nat.isZero`,
`Nat.beq`, and `Nat.ble`. These declarations are elaborated and evaluated once,
beneath every prelude and program, including with `--no-prelude`. Preludes and
programs cannot redeclare those names, so every value of type Nat or Bool belongs
to these families and quotation can name the native operations directly. Nothing
validates a Nat declaration because no other Nat declaration can exist;
namespaced inductives such as `Lib.Nat` are unrelated families. Ordinary source
functions acquire no arithmetic laws from their names.

The prelude adds source definitions such as `Nat.le`, `Nat.lt`, and
`Nat.decEq`, one axiom about the natives, `Nat.mul_add`, and the theorems
`Nat.mul_pow` and `Nat.pow_mul`, all described below. They live in the prelude
because `Eq` is a prelude family.

## Definitional laws

1. Addition is associative and commutative, with unit zero.
2. Multiplication is associative and commutative, with unit one, and
   `0 * x = 0`.
3. Closed arithmetic computes to numerals, and `Nat.succ(x) = x + 1`.
4. For every numeral `n`, `n * x` is `x + ... + x` with `n` copies. So
   `x + x = 2 * x` and `2 * (a + b) = 2 * a + 2 * b`.
5. Powers: `x^0 = 1`; for every numeral `n`, `x^n` is `x * ... * x` with `n`
   copies; for all exponents, symbolic or not, `x^a * x^b = x^(a + b)`; and
   `1^e = 1`. The successor equation `x^(e + 1) = x^e * x`, and more generally
   `x^(e + n) = x^e * x^n`, are instances of the product law. So are
   `2^a * 2^b = 2^(a + b)` and, with the numeral powers,
   `(x^a)^2 = x^a * x^a = x^(2 * a)`.

Law 4 and the numeral powers of law 5 are families indexed by numerals. No law
has a variable in the position of a multiplier that distributes, or a base that
splits.

These are not definitional:

- Distributivity over a symbolic multiplier: `a * (b + c) = a * b + a * c`.
  This includes the successor equations of multiplication,
  `a * (b + 1) = a * b + a` and `(a + 1) * b = a * b + b`.
- Powers of sums: `(a + b)^2 = a^2 + 2 * a * b + b^2`.
- Powers of products with a symbolic exponent: `(x * y)^a = x^a * y^a`,
  including its closed instances such as `6^a = 2^a * 3^a`.
- Powers of powers with a symbolic outer exponent: `(x^a)^b = x^(a * b)`,
  including `(x^2)^b = x^(2 * b)` and `4^b = 2^(2 * b)`.

The prelude declares the distributive law as an axiom:

```
axiom Nat.mul_add (a: Nat)(b: Nat)(c: Nat):
  Eq(Nat, Nat.mul(a, Nat.add(b, c)), Nat.add(Nat.mul(a, b), Nat.mul(a, c)))
```

Every other semiring identity follows from this axiom and conversion. Right
distributivity `(a + b) * c = a * c + b * c` is `Nat.mul_add(c, a, b)`, because
both sides convert by commutativity, and `a * (b + 1) = a * b + a` is
`Nat.mul_add(a, b, 1)`. The axiom cannot be proved inside the system: no law
reduces a product with a symbolic successor, so induction has no step to use.

The successor equation of powers is definitional, so the left-out exponent laws
are prelude theorems, proved by induction on the exponent:

```
def Nat.mul_pow (x: Nat)(y: Nat)(a: Nat):
  Eq(Nat, Nat.pow(Nat.mul(x, y), a), Nat.mul(Nat.pow(x, a), Nat.pow(y, a)))
def Nat.pow_mul (x: Nat)(a: Nat)(b: Nat):
  Eq(Nat, Nat.pow(Nat.pow(x, a), b), Nat.pow(x, Nat.mul(a, b)))
```

The step of `Nat.mul_pow` multiplies the induction hypothesis by `x * y`; both
sides then convert by the successor equation and commutativity. The step of
`Nat.pow_mul` multiplies the hypothesis by `x^a`, which gives `x^(a*k + a)` by
the product law, and rewrites `a*k + a` to `a * (k + 1)` with `Nat.mul_add`.

## Why these laws and no more

Definitional equality has to be closed under substitution. If it equates `T`
and `U` with `x` free, it must equate them for every value of `x`; otherwise a
body that checks for an arbitrary `x` stops checking when `x` is instantiated,
and results depend on evaluation order. A procedure stays closed under
substitution when it decides a set of laws completely, because a law instance
under a substitution is again a law instance. Applying laws partially breaks
that. So the design question is which set of laws to decide, not which
rewrites to apply.

**Symbolic distributivity forces expansion.** The product
`(x1 + y1) * ... * (xk + yk)` takes linear space to write and expands to `2^k`
terms. Comparing coefficients without expanding does not help in general: the
coefficient of `x1 * ... * xn` in a product of `n` sums of the `x`s is the
permanent of their coefficient matrix, which is #P-hard to compute, and
deciding equality of such expressions deterministically without expanding is
polynomial identity testing, for which no efficient algorithm is known. So a
procedure that decides the semiring laws completely must either expand or cap
its work.

**Partial distribution is not a smaller law.** A law about a variable covers
every term substituted for it, including sums, so "distribute over atoms" or
"factor common monomials out of sums" is either full distributivity or wrong
under substitution. Factoring, for example, gives `(x*a + x*b) * (c + d)` and
`x * (a + b) * (c + d)` the same form. Substituting `c := 1, d := 0` turns them
into the sum `x*a + x*b` and the product `x * (a + b)`, so standalone sums would
have to be factored too. Then `(p + q) + y` and `p + (q + y)` normalize
differently after `p := x*a, q := x*b`: the first factors `x` out of `x*a + x*b`
before `y` joins, and the second never sees that sum alone. Repairing that
requires multiplying factors back in when sums combine, which for
`x * (a + b) * (c + d)` means choosing which sum receives `x`, and settling that
canonically is full expansion.

**Commutativity or a successor equation for multiplication, not both.** If
multiplication is commutative and `a * (b + 1) = a * b + a` holds, then
grouping `(x+1) * (y+1) * (z+1)` two ways gives `(x*y + x + y) * z + x*y + ...`
and `x * (y*z + y + z) + y*z + ...`. Associativity makes them equal, and showing
it takes general distributivity. These forms keep commutativity and
associativity, which index arithmetic for shapes and tiling uses most, and
provide the successor equations through `Nat.mul_add`.

**The product law alone is cheap.** Its normal form compares the bases of
powers by key and adds their exponents, which are already normal forms. It
never looks inside a base, so `(2*x)^a * (2*x)^b` is `(2*x)^(a + b)` while
`2^a * x^a` stays a different product. It is also the useful exponent law:
`2^k * 2^l` and the successor equation `x^(e + 1) = x^e * x` are instances.

**Power-of-a-power conflicts with the product law.** `(x^a)^b * (x^a)^c` is
`(x^a)^(b + c)` by the product law, and power-of-a-power makes that
`x^(a * (b + c))`. Applying power-of-a-power first gives `x^(a*b) * x^(a*c)`,
which the product law makes `x^(a*b + a*c)`. With both laws, exponents would
have to distribute, which is the trap of commutative multiplication plus a
successor equation for it, described above. The product law was chosen because
it is cheaper and more useful. Power-of-a-power alone would not be cheap either:
it needs perfect-power detection, since `4^b = 2^(2*b)`, and
`x^2 * y^2 = (x*y)^2`.

**Power-of-a-product forces factoring numerals.** With `x := 2, y := 3`, closed
arithmetic turns `(x*y)^a = x^a * y^a` into `6^a = 2^a * 3^a`, and the same law
gives `4^a = 2^a * 2^a = 2^(2*a)`. A canonical form for every `n^a` is then the
prime factorization of `n`, which no known efficient algorithm computes.

**Numerals are safe as counts, not as bases.** Law 4 and the numeral powers of
law 5 use numerals as counts: `n * x` repeats an addition and `x^n` repeats a
multiplication. Substitution never puts a sum or a product where a numeral
count stands, and adding counts is trivial. The only product that equals a sum
is a numeral times a single sum, and the normal form always stores that product
as the sum. As bases of multiplicative laws, numerals are not safe: closed
arithmetic folds `2*3` into `6` and `2^2` into `4`, so a numeral base hides a
factorization. The product law is safe because it never decomposes a base.

The two counted operations compare as follows:

| Case | Multiplication `n * x` | Power `x^n` |
| --- | --- | --- |
| Known count | `n * x`: kept | `x^n`: kept |
| Count gains a known amount | `(a + 1) * x = a * x + x`: out | `x^(a + 1) = x^a * x`: kept |
| Count is a sum | `(a + b) * x = a * x + b * x`: out | `x^(a + b) = x^a * x^b`: kept |
| Base is a sum or product | `a * (x + y)`: kept only for numeral `a` | `(x * y)^a`: kept only for numeral `a` |
| Counts compose | `(a * b) * x = a * (b * x)`: kept | `x^(a * b) = (x^a)^b`: out |

The rows differ for two reasons. Multiplication is commutative and power is
not: splitting a multiplication's count also distributes over the other factor,
which expands, while splitting an exponent gives `x^a * x^b`, which merges back
into one factor. The last row differs because of the power-of-a-power conflict
above.

The same asymmetry decides which laws are lemmas. Multiplication's successor
equation is not definitional, so distributivity is the axiom `Nat.mul_add`.
Power's successor equation is definitional, so every left-out exponent law is a
theorem: `Nat.mul_pow` by induction on the exponent, and `Nat.pow_mul` by
induction on the outer exponent, using `Nat.mul_add` to rewrite `a * (b + 1)`.

## One representation

Every Nat value has exactly one representation:

| Value | Representation |
| --- | --- |
| Zero | `VCtor(Nat.zero)` |
| A lone atom with coefficient and exponent one | The atom itself, such as a `Var` |
| Anything else, including every positive constant and every successor | `VNatPoly` |

`ConstructorValue` is the semantic constructor factory. It folds `Nat.succ(x)`
into the form of `x + 1`, and `VApp` rejects a stored `Nat.succ`, so successors
never exist as constructor applications and zero is Nat's only stored
constructor. Equal forms over the same atoms therefore have equal keys, and a
form needs structural conversion only when one of its atoms does. Types such as
`Vec(A, n + 1)` keep the fast key comparison.

## Normal form

`NatNormalForm.Form` is the immutable representation, with a private
constructor. Its invariants:

- A form has a nonnegative `BigInt` constant and a sequence of terms. Each term
  has a positive `BigInt` coefficient and a monomial; the monomials are distinct
  and in key order.
- A monomial is a nonempty sequence of factors ordered by base key, then
  numeral power before symbolic power. No two factors share both base and kind,
  so a base appears at most once as each kind, as in `x^2 * x^a`.
- A numeral power has a positive `BigInt` exponent, and its base is an atom or
  a primitive sum: the published value of a primitive form with at least two
  summands.
- A symbolic power's exponent is a published Nat value with zero constant and
  at least one term. Its base is any Nat value except one: zero, a numeral of at
  least two, an atom, any sum (content is not extracted), a monomial, or another
  symbolic power. The base is the whole value because `(x * y)^a` does not
  split.
- No monomial is a single primitive sum with numeral exponent one. Such a term
  is the sum scaled by its coefficient, and its summands appear in the
  enclosing form directly.

`Form.toValue` is the single publication boundary: it collapses zero and lone
atoms with coefficient and numeral exponent one before wrapping a
`Value.VNatPoly`, and caches the result, so a published form is the value of its
own form. A sum used as a factor, and a symbolic exponent, are therefore
ordinary Nat values with their own keys, dependencies, and quotation. The
lone-sum rule above likewise applies only to a numeral exponent of one.

| Expression | Normal form |
| --- | --- |
| `(n + 1) * (m + 2)` | one term, the product of the factors `n + 1` and `m + 2` |
| `2 * (a + b)` | `2*a + 2*b` |
| `(2*a + 2*b) * c` | `2 * (a + b) * c` |
| `x * x + x` | `x^2 + x` |
| `(a + b) * (b + a)` | `(a + b)^2` |
| `(a + 1) * b + b` | `(a + 1) * b + b`, two terms |
| `x^a * x^b` | `x^(a + b)` |
| `2^a * 2^b` | `2^(a + b)` |
| `2^(a + 1)` | `2 * 2^a`, coefficient two |
| `x^2 * x^a` | `x^2 * x^a`, one factor of each kind, the same as `x^(a + 2)` |
| `(2*x)^a` | one symbolic power with base `2*x`, unlike `2^a * x^a` |
| `(2*x)^(a + 2)` | `4 * x^2 * (2*x)^a` |
| `(x^a)^2` | `x^(2*a)` |
| `(x^a)^b` | one symbolic power with base `x^a`, unlike `x^(a*b)` |
| `1^e` | `1` |
| `0^(e + 1)` | `0`; `0^e` stays a power |

## Operations

Each form computes its content and primitive part at most once.

- **Add** by merging sorted terms, adding coefficients of equal monomials and
  the constants.
- **Scale** by a numeral `c`: zero gives zero, one gives the form itself, and
  otherwise every coefficient and the constant are multiplied by `c`, keeping
  the monomials.
- **Multiply** forms `f` and `g`. If either is zero the product is zero; if
  either is a numeral, scale the other. Otherwise the product is one term: its
  coefficient is `content(f) * content(g)`, and its monomial merges the factors
  of the two primitive parts. A primitive part that is a single monomial
  contributes its factors; a primitive sum contributes itself as a numeral
  power with exponent one. Factors with equal base and kind merge: numeral
  exponents add as numbers and symbolic exponents add as forms. The product has
  at least two factor occurrences, so it is never a lone sum.
- **Raise** to a numeral `n`. Any base to the zero is one, zero to a positive
  power is zero, and a numeral base gives its power. Otherwise the result is one
  term with coefficient `content^n` and the primitive part's factors raised to
  `n`: a numeral exponent is multiplied by `n` and a symbolic exponent is scaled
  by `n`, so `(x^a)^2 = x^(2*a)` agrees with `x^a * x^a`. Raising a numeral of
  at least two, including a base's content, to an exponent that does not fit a
  32-bit integer would need
  more bits than the JVM can represent, so it raises `NatValueTooLarge`, as does
  a smaller exponent whose result the JVM's integers cannot hold. That is a
  representation limit, not a budget.
- **Raise** to a symbolic exponent `e + k`, where `k` is the exponent's constant:
  the result is `base^k`, computed as above with content extraction, times the
  symbolic power of the whole base to `e`. A base of one contributes nothing, so
  `1^e = 1`, and a zero base with positive `k` gives zero.
- Form a **successor** by increasing the constant, and expose the
  **predecessor** of a form whose constant is positive. Both share the terms.
- **Substitute** atoms by rebuilding the form through these operations,
  replacing each distinct atom once, including atoms inside operands that are
  forms: sum bases, symbolic exponents, and any symbolic power base. Zero is not
  an atom. An unchanged substitution returns the original value. A monomial is
  rebuilt as one n-ary product, so a monomial with many factors is sorted once
  rather than merged factor by factor. So a rebuilt symbolic exponent that
  gains a constant splits again, one that becomes zero gives one, and a
  symbolic power whose base becomes one vanishes. A term whose numeral power
  base becomes zero vanishes; a symbolic power whose base becomes zero stays,
  because `0^e` is not zero.

### Canonicity

Two arithmetic expressions over the same atoms have identical normal forms
exactly when the definitional laws equate them.

1. Every operation step is an instance of the laws, so identical forms denote
   equal expressions. For example, extracting content from a factor,
   `(2*a + 2*b) * c = 2 * ((a + b) * c)`, uses laws 2 and 4.
2. The forms with these operations satisfy every law, so equal expressions have
   identical forms. Addition is a merge, so it is associative and commutative
   with unit zero. Multiplication is commutative by symmetry. It is associative
   because content is multiplicative and the factors of a product's primitive
   part are the union of its operands' factors: `(f * g) * h` and `f * (g * h)`
   both have coefficient `content(f) * content(g) * content(h)` and the union of
   the three factor multisets, merged by addition of exponents, which is
   associative and commutative for numbers and for forms. Scaling satisfies
   law 4, the unit and zero cases hold by construction, and raising to a
   numeral agrees with repeated multiplication because content multiplies and
   exponents, numeral or symbolic, are scaled.
3. In particular, the forms satisfy the product law. Write each exponent `E` as
   `e + k`, with `k` its constant. Then `x^E` is `x^k` times the symbolic power
   `(x, e)`, omitted when `e` is zero. In `x^A * x^B` the numeral parts merge
   into `x^(k_A + k_B)` by the multiplication above, and the symbolic parts
   merge into `(x, e_A + e_B)`, because both have base `x` and kind symbolic.
   That is exactly the split of `A + B`, whose constant is `k_A + k_B` and whose
   terms are `e_A + e_B`. A base of one never forms a symbolic power, so `1^e`
   is one, and `x^0` is one.

Symbolic power bases are compared only by key, so the forms never relate
`(x*y)^a` to `x^a * y^a` or `(x^a)^b` to `x^(a*b)`, matching the laws.

So keys decide equality of forms unless an atom needs structural conversion.

### Cost

Every operation does work linear in the size of its operands and result,
plus sorting factor bases and computing greatest common divisors. Adding
creates no monomial and scaling only changes coefficients; each multiplication
or power creates at most one. A form therefore never has more monomials than
the atoms and multiplications that produced it, counting a shared
subexpression once. The superlinear patterns are a long sum built one term at a
time and a long product built one factor at a time, where each operation copies
an ever-longer term or factor sequence, for quadratic total work.
Coefficients, constants, and exponents grow only as the program's own closed
arithmetic grows them. Merging two symbolic powers adds their exponent forms,
and raising one to a numeral scales its exponent, both linear in the exponents'
size; a symbolic exponent is never expanded or factored.

## Truncated subtraction and comparisons

The native functions depend only on the signed difference of their arguments.
They cancel the coefficient-wise common part of the two forms, which leaves the
positive and negative parts `P` and `N` of `a - b`: forms that share no
monomial. Cancellation works on whole terms; a sum inside a factor is opaque,
so `x * (a + b) - x * a` stays stuck, and so is a symbolic power, so
`x^(a + 1) - x^a` stays stuck. Shared or equal terms cancel directly, so
subtracting a form from its successor never compares atoms. When an atom needs
structural conversion, both forms are first aligned over equivalent atoms as
conversion does.

| Function | Decides | Otherwise stuck as |
| --- | --- | --- |
| `sub(a, b)` | `P` when `N` is zero; zero when `P` is zero | `sub(P, N)` |
| `pred(n)` | `sub(n, 1)` | `sub(n, 1)` |
| `isZero(n)` | true for zero; false for a known successor | `isZero(n)` |
| `beq(a, b)` | `isZero(N)` when `P` is zero; `isZero(P)` when `N` is | `beq(P, N)`, parts ordered by key |
| `ble(a, b)` | true when `P` is zero; false when `N` is zero and `P` has a known successor | `ble(P, N)` |

A stuck subtraction absorbs a known constant, since `(p - q) - c = p - (q + c)`.
It does not absorb a symbolic subtrahend: `sub(sub(a, b), x)` stays stuck, so
that substituting `x := sub(a, b)` still cancels to zero. Every result is
therefore stable under substitution. All of these are valid identities, and they
include the recursive equations `sub(a, succ(b)) = pred(sub(a, b))`,
`beq(zero, b) = isZero(b)`, and `ble(succ(a), succ(b)) = ble(a, b)`. A stuck
result is an application of the native function that resumes once a dependency
of its arguments is solved. Stuck `beq` results also convert with their arguments
swapped: equivalent atoms can have different keys and therefore reverse the
stored key order.

## Atom equality and conversion

Vars are identified by their ids. Other neutral values use ordinary
definitional conversion: function extensionality or convertible captures can
equate atoms whose keys differ. Form keys hash the constant, then each term's
coefficient and, for each factor in canonical order, its base key, a kind tag,
and its exponent: a numeral or a symbolic exponent's key. Integers use binary
data with a direct path for values that fit a `Long`.

Conversion reaches `NatNormalForm.equivalent` only when the keys differ and some
atom needs structural conversion, so the forms already differ. It rejects
mismatched constants, which alignment cannot change. Otherwise it collects the
distinct atoms of both forms, including atoms inside operands that are forms
such as sum factors and symbolic exponents, and groups them into equivalence
classes using `ValueEquivalence.defEq`. It then rebuilds both forms with every
atom replaced by its class representative, by the same substitution as
materialization, and compares the results by key. This handles `f + g` versus
`2*f` when `f` and `g` convert but have different keys, `(f + g) * h` versus
`2 * f * h`, and `x^f * x^g` versus `x^(2*f)`. Grouping compares each new atom
with the existing representatives, which is quadratic in the number of distinct
atoms with structural conversion; ordinary atoms only search structural
representatives. Atom comparison never invokes refinement unification and never
adds links. All equality successes are valid identities.

## Matching and reevaluation

`ConstructorValue.unapply` is the constructor view used by evaluator matching,
match checking, and type-pattern capture projection:

| Nat value | Constructor view |
| --- | --- |
| Zero | `Nat.zero` |
| Form with constant at least one | `Nat.succ(P - 1)` |
| Form with zero constant, or an atom | None (blocked) |

A form with zero constant is not necessarily zero or positive, so a match on it
waits for refinement. This includes products of successors such as
`(n + 1) * (m + 1)`, whose form is one term with constant zero, and symbolic
powers such as `x^n`. Their reduction blockers are all of their dependencies,
because changing any operand can expose a constructor: `x^n` resumes when either
`x` or `n` is solved. Blocked applications and match thunks carry dependency
sets and are reevaluated when any of them is solved, recomputing blockers after
each reduction. `ReductionBlockers` describes scheduling only: value matching
may refine a variable denoting the whole scrutinee and freshly opened
constructor variables, never a variable that merely schedules reduction.

In a binder such as `Sized(Nat.succ($n))`, the capture projects the form's
predecessor rather than indexing into its terms.

Materialization substitutes atoms transitively, reruns their blocked
computations, and rebuilds the form. If `n := a + b`, then `n*m + n` becomes
`(a + b)*m + a + b`, and if `m := 2` as well it becomes `3*a + 3*b`. Normalizing
then substituting gives the same form as substituting then normalizing.

## Refinement and termination

Whole-variable linking and its occurs check run before any arithmetic case.
Arithmetic equations do not justify links between their atoms: there is no
inversion of multiplication and no choice of a solution of `a+b=c+d`.

Known successor counts cancel in one step: `P+c = Q+d`, with both constants
positive, reduces to the equation after subtracting `min(c,d)`. Zero versus a
positive constant, and unequal constants, are contradictions. Unequal symbolic
forms are `Stuck`, not `Contradiction`.

For structural termination, a Nat candidate is smaller only when it converts to
the root with a positive number of known successors removed: its constant is
smaller and its terms are equivalent. For example, `n+m` is smaller than
`n+m+1`, but `n` is not smaller than `n+m`. Monomials, factors, and atoms are
not structural subterms. Other constructors use the ordinary subterm rule,
including when a field is a form.

Positivity and absence checks treat a form's operands, its factor bases and
symbolic exponents, as arguments of the Nat operations: an occurrence of the
positivity target in an operand is never positive, just as in any application
argument. An operand that is itself a form is checked the same way,
recursively.

## Quotation and display

Checked residuals remain syntax, without embedded `Value` or `Env` objects.
Quotation rebuilds a form from checked applications of `Nat.add`, `Nat.mul`,
and `Nat.pow` over quoted operands, quoting each distinct operand once; a sum
factor quotes as its own sum, and a symbolic power quotes as
`Nat.pow(base, exponent)`. It omits zero and unit operations and uses balanced
application trees, so syntax depth is logarithmic in the number of terms and
factors at each level.

`ElabAst.Term.NatLit(value, span)` is a checked leaf holding a nonnegative
`BigInt`, used for constants, coefficients, and exponents. Like an application,
it is a type term, so a constant can stand in a type-pattern argument. Source
programs have no literal syntax; quotation emits literals only from constants of
evaluated values, so evaluating one builds the constant directly. Capture
analysis and closed-environment inlining treat literals as leaves. Round trips
preserve type, conversion, dependencies, and captured local slots.

Ground values up to 8 display in the unary constructor syntax. Larger or
symbolic values display as sums of products and powers with decimal coefficients
and the constant last, such as `2 * a * (b + 1)^2 + b + 3`. Operands that are
forms with terms print in parentheses and numeral bases in decimal, as in
`x^a`, `x^(a + b)`, `2^n`, `(2 * x)^a`, and `(x^a)^b`. Checked literals print
in decimal.

## Measurements

`sbt 'Test / runMain com.raccoonlang.NatNormalFormBench'` reports warmed
medians on one JVM thread. These numbers are from an Apple-silicon laptop under
other load, so treat them as relative.

| Operation | Time | Allocation |
| --- | --- | --- |
| Multiply two atoms | 0.28 us | 0.9 KiB |
| Successor of an atom | 0.05 us | 0.25 KiB |
| 2048-term sum: built one term at a time | 21 ms | 21 MiB |
| 2048-term sum: built as a balanced tree | 0.54 ms | 1.6 MiB |
| 2048-factor product: built one factor at a time | 45 ms | 52 MiB |
| 2048-factor product: built as a balanced tree | 0.94 ms | 2.2 MiB |
| Product of 256 two-atom sums, balanced | 0.14 ms | 260 KiB |
| That product squared | 15 us | 18 KiB |
| 2048-term sum: two atoms replaced by a sum | 0.4 ms | 340 KiB |
| 2048-factor product: one atom replaced by a sum | 0.35 ms | 210 KiB |
| Product of 256 sums: one atom of each replaced by one | 0.30 ms | 590 KiB |
| 64 terms over different-key convertible atoms: conversion | 2.8 ms | 8.3 MiB |
| Product of 64 sums over such atoms: conversion | 1.9 ms | 8.3 MiB |
| 2048-term sum: peel 64 successors | 0.9 us | 6 KiB |
| 2048-term sum: `ble(sub(p + 5, p), 5)` | 0.06 us | 0.3 KiB |

Symbolic powers left the other rows unchanged within noise. The substitution
row allocates less than before because collecting the unchanged terms'
metadata no longer builds an iterator per term. The two quadratic rows are the
patterns described under cost. Conversion over
structural atoms is dominated by the quadratic grouping of 128 distinct
structural atoms, each comparison opening two lambdas. The full test suite takes
about 18 CPU seconds, most of it JVM startup and compilation.
