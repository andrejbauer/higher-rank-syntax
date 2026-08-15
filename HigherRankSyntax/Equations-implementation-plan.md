# Equations and quotient decorations

This roadmap inserts an equation layer between the completed raw/decorated
syntax and the deferred T2 judgment layer.  Each pass is independently
buildable and is completed and reported before the next pass begins.

## Status

- **Pass 1 — T1 categorical cleanup:** complete
- **Pass 2 — equations and quotient relative monad:** complete
- **Pass 3 — quotient decorated-telescope monoid:** complete
- **T2 judgments:** deferred

## Pass 1 — T1 categorical cleanup

Reorganize `Typing` so its files follow the mathematical progression from
decorations to their syntax module, arity-shaped modules, the
context-extension tensor, and the internal monoid of decorated telescopes.
Generalize `ArityMod` and its tensor from the raw syntax monad to an arbitrary
relative monad equipped with coherent extension by raw arities.

Acceptance criteria:

- `ArityMod T` is the slice of `T`-modules over the constant arity functor.
- a coherent Kleisli arity action supplies the generic telescope tensor;
- the raw `SyntaxMonad` action is induced by `Subst.lift`;
- `DTelMon bd` remains the internal monoid of raw decorated telescopes;
- every `Typing` file begins with an intuitive mathematical account;
- existing core, magma, dependent-classification, and archived T2-boundary
  targets build without `sorry` or new axioms.

Completed:

- `Typing` now follows the progression `Decoration`, `DecorationModule`,
  `ArityModule`, `TelescopeTensor`, and `DecoratedTelescopeMonoid`; the archived
  boundary extraction remains under `Typing/T2` and outside the root imports.
- `arityConst T` and `ArityMod T` are generic in the relative monad.
- `KleisliArityAction T` packages coherent suffix lifting; `Subst.lift`
  provides the raw-syntax instance, including empty- and composite-suffix
  comparisons.
- the context-extension tensor and its Mathlib `MonoidalCategory` instance are
  generic under that action.
- raw decorated telescopes retain
  `DTelMon bd : CategoryTheory.Mon (ArityMod (SyntaxMonad C))`.
- all requested builds, import checks, `git diff --check`, and the checks for
  `sorry` and Lean `axiom` declarations pass.

## Pass 2 — equations and quotient relative monad

For a fixed signature prefix, define equation schemas, the least
proof-irrelevant structural congruence closed under two-sided substitution,
ordinary quotient expressions, and the quotient fixed-prefix relative monad.
Use classical choice only to select representatives of quotient-valued
fillers.  Validate the layer with the associativity and unit equations of
monoids, without a freeness or list-adequacy theorem.

Acceptance criteria:

- derivable equality is an equivalence, an application congruence, and stable
  in both substitution inputs;
- renaming and arbitrary axiom instances are derived operations;
- quotient Kleisli extension is representative-independent and satisfies the
  relative-monad laws;
- the raw-to-quotient map is a relative-monad morphism;
- monoid generators, a nontrivial substitution instance, congruence, and
  quotient equalities are checked.

Completed:

- `EquationPresentation` separates a protected signature prefix, substitutable
  metavariables, and fixed local variables.
- `DerivEq` is the least structural equivalence relation containing the
  declared schemas and closed under two-sided substitution; common
  substitution, pointwise-equivalent fillers, renaming, and schema instances
  are derived consequences.
- `QExpr` is an ordinary objectwise `Quotient`, with elimination and exactness
  lemmas; raw slots and `J C` are unchanged.
- private representative selection supplies quotient-valued substitutions,
  and two-sided congruence proves independence of expression and filler
  representatives.
- `quotientMonad`, `quotientHom`, and the induced identity-on-context Kleisli
  functor are implemented without axioms.
- the monoid presentation checks associativity, both unit generators, a
  nontrivial simultaneous instance, multiplication congruence, quotient
  equalities, and unit/Kleisli computations.
- all requested core, monoid, magma, dependent-classification, and archived
  T2 builds pass, as do `git diff --check` and checks for `sorry` and Lean
  `axiom` declarations.

## Pass 3 — quotient decorated-telescope monoid

Relate raw decorations of a fixed shape pointwise through derivable equality,
quotient each fixed-shape decoration fibre, and make these quotient telescopes
a module over the quotient relative monad.  Descend shape, empty telescope,
and dependent concatenation, and package the result as an internal monoid in
the generic arity-module category.

Acceptance criteria:

- decoration equality is an equivalence compatible with two-sided
  substitution, empty, and concatenation;
- quotient telescopes retain their raw arity definitionally;
- the quotient action is independent of telescope and substitution
  representatives;
- the quotient monad has a coherent Kleisli arity action;
- the quotient telescope module, shape map, and internal monoid are packaged;
- dependent examples identify `x : A` with `x : B` when `A ≈ B`, including
  substitution and congruence inside a classifier;
- no T2 well-formedness, typing, equality judgment, or conversion rule is
  introduced.

Completed:

- classifier equality applies `DerivEq` exactly in expression-valued
  classifier fibres, and decoration equality compares every immediate and
  nested site of one fixed raw shape;
- fixed-shape decoration quotients assemble into `QDTel`, whose raw arity is
  retained literally and whose action is independent of selected expression
  and substitution representatives;
- quotient syntax has coherent suffix extension, so the generic
  context-extension tensor applies to `ArityMod E.quotientMonad`;
- quotient empty telescopes and dependent concatenation are natural,
  shape-preserving, associative, and unital, yielding
  `QDTelMon E bd : CategoryTheory.Mon (ArityMod E.quotientMonad)`;
- the raw-to-quotient map is natural and preserves raw shape;
- the dependent example identifies `x : A` and `x : B` from `A ≈ B`, checks a
  substitution instance, and propagates the equation into a larger
  classifier by structural congruence;
- all requested builds, whitespace checks, and checks for `sorry` and Lean
  `axiom` declarations pass; T2 remains unstarted.
