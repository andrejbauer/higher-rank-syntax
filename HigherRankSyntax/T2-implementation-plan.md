# Incremental T2 implementation

This roadmap keeps the raw syntax unchanged and builds the typing layer in
eight independently buildable passes.  Each pass ends with focused examples,
the core and existing example builds, no `sorry`s, and an update to this file.

## Status

The equations-and-quotients roadmap now comes before this deferred T2 work.
No T2 judgment layer has begun.

- **Pass 1 — T1 boundary extraction:** complete; archived outside the T1 import path
- **Pass 2 — T1 algebraic closure:** replaced by the completed categorical
  `ArityMod` development
- **Pass 3 — Raw T2 morphism and judgment vocabulary:** pending
- **Pass 4 — Formation and renaming layer:** pending
- **Pass 5 — Substitution layer:** pending
- **Pass 6 — Walking-family formation:** pending
- **Pass 7 — Walking-family substitution:** pending
- **Pass 8 — Derived structures:** pending

## Pass 1 — T1 boundary extraction

Add the raw inclusion of a slot's preceding arity, restriction of a decoration
to that prefix, and a slot-boundary object containing the decorated prefix,
decorated binding arity, and classifier.

Acceptance criteria:

- Prefix inclusions are derived from `Precedence.factor` and `Carrier.inl`.
- Prefix restriction retains classifiers at every immediate and nested slot.
- Slot boundaries expose the three components required by T2's boundary law.
- The operations are checked for `listCarrier` and `A : Type, x : A`.

Completed:

- `Precedence.inclusion` inserts a slot from `before x` into the ambient arity.
- `Decoration.preceding` and `DecoratedTelescope.preceding` restrict all
  immediate and nested classifier data to `before x`.
- `SlotBoundary` and `DecoratedTelescope.boundary` package the preceding
  telescope, decorated binding arity, and classifier.
- `ListCarrier.inclusion_val` and the `termBoundary` checks validate the API on
- the list carrier and `A : Type, x : A` validated the API before it was moved
  out of the T1 example.
- `lake build HigherRankSyntax MagmaAdequacy DependentClassification` passes.
- the implementation is retained in
  `HigherRankSyntax/Typing/T2/DecorationBoundary.lean` and will return to the
  import graph when the T2 vocabulary work resumes.

## Pass 2 — T1 algebraic closure (superseded)

The generic algebraic work moved to `T1-telescope-module.md`.  Passes A--D are
complete: `ArityMod T` has its context-extension monoidal structure whenever
`T` has a `KleisliArityAction`, and
`DTelMon bd : CategoryTheory.Mon (ArityMod (SyntaxMonad C))` packages decorated
telescopes as its internal monoid.  No T2 judgment layer has begun.

The rooted aliases are no longer part of T1.  Fixed signatures arise by
pulling the generic module back along prefixing, while T2 will select the
well-formed rooted objects.

## Pass 3 — Raw T2 morphism and judgment vocabulary

Define decoration-compatible renamings using explicit maps on slot prefixes and
boundary-preservation equations.  Define proof-irrelevant predicates for
contexts, telescopes, and classified expressions.  Index classified judgments
uniformly by `ClassifierAt`, with `PUnit` at unclassified classes.

Acceptance criteria:

- Compatibility exposes each slot's restricted source and target boundaries.
- Judgment families are propositions and retain their raw expressions.
- Classified and unclassified classes share one generic interface.

## Pass 4 — Formation and renaming layer

Package L0--L3: root, empty telescope, extension, prefix closure, well-formed
boundaries, variables, weakening, and general renaming stability.  Prove
identity and composition for compatible renamings.

Acceptance criteria:

- Every operation is stated over the predicates from Pass 3.
- Compatible renamings form a category at the raw-map level.
- Weakening is obtained as a distinguished compatible renaming.

## Pass 5 — Substitution layer

Define layer substitutions as raw fixed-prefix substitutions whose fillers
inhabit the transported classified-expression judgments.  Package L4:
identity, composition, telescope transport, and expression substitution.

Acceptance criteria:

- Filler boundaries are computed by `Decoration.substitute`.
- Identity and composition use the existing raw eta/action laws.
- No second expression traversal or termination argument is introduced.

## Pass 6 — Walking-family formation

Define the decorated signature `iota : ty`, `P : (x : iota) -> ty`, its
generated well-formed contexts, telescopes, and expressions, and prove L0--L3.

Acceptance criteria:

- The boundary of `P` requires an argument classified by `iota`.
- Formation, boundary, variable, weakening, and renaming rules are proved.
- A negative compile-time test records that `P(y)` is unavailable for
  `y : P(x)`.

## Pass 7 — Walking-family substitution

Prove the walking-family substitution lemma, instantiate the complete T2
interface, and check nontrivial weakening and simultaneous substitutions.

Acceptance criteria:

- The generated judgments satisfy L4.
- Identity and composite substitutions agree with their raw actions.
- At least one classifier changes under simultaneous substitution.

## Pass 8 — Derived structures

Restrict raw eta and Kleisli extension to well-formed expressions and package
the fibred relative monad.  Package the decoration expansion over the raw
Kleisli structure, the typing layer as its closed substructure, and the
resulting generalized/decorated carrier interface.

Acceptance criteria:

- Relative-monad laws are inherited from the raw fixed-prefix monad.
- Erasure commutes with the packaged structure maps.
- The categorical interfaces use the T1 and T2 operations proved in earlier
  passes rather than adding axioms for them.

## Standing decisions

- Keep `DecorationPath`, global `Precedence`, and the `Option` classifier policy.
- Use proof-irrelevant predicates in the first T2 implementation.
- Keep optional head characterization L5 outside the generic interface.
- Preserve existing raw syntax, renaming, substitution, and relative-monad
  behavior.
