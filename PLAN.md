# Higher-Rank Syntax - Active Plan

## Active Branch

The active formalization is the `endomaps` approach in
`HigherRankSyntax/HigherRankSyntax`.

Do not revive the older `HigherRankSyntaxSig` representable-list-map attempt for
current proof work.  The Tele version uses cons-style representable endomaps:

- `Tele α` is an endomap on `List α`.
- `Shape C` is `Tele C.Arity`.
- `Shape.nil`, `Γ ∷ α`, and `Γ ⋈ τ` are strict endomap operations.
- `Proper` supplies `inl`, `inr`, classification, and cover data for
  telescopes that behave like proper context extensions.

The strict associativity and unit behavior of `Tele` is the reason this branch
avoids the list-append reassociation transports that blocked earlier attempts.

## Current Status

`HigherRankSyntax` has the basic syntax infrastructure:

- `Carrier.lean`: arities, binders, binder arities, and well-founded sub-arity.
- `Tele.lean`: representable endomap telescopes.
- `Shape.lean`: shapes and slots as telescope list views.
- `Renaming.lean`: renamings, extension, and expression action.
- `Expr.lean`: expressions and eta expansion.
- `ProperTele.lean`: structural operations for classifying extension slots.
- `Subst.lean`: the single fixed-shape substitution walker `Subst.act`, plus
  the `SubstSite` facade for the τ/dom/pre head split.
- `Equations.lean`: substitution equations and monad-law proof work, with
  proof-facing head classifiers for the larger interchange case splits.
- `SyntaxMonad.lean`: the relative monad packaging.
- `equations-math.tex`: code-companion notes matching the mathematical
  statements in `Equations.lean` to their Lean declarations.
- `equations-refactor-plan.md`: thesis-style refactor plan for making
  `Equations.lean` read as action, interaction lemmas, composition, and
  relative-monad laws.

The two unit laws are now proved through the substitution layer:

- `Subst.act_id` proves identity substitution acts as identity.
- `Subst.act_η` proves the left unit law on eta expansions.

The key helper layer is the one-binder identity-instantiation bundle:

- `Subst.instId`
- `Subst.act_inst.idOf`
- `Subst.act_inst.η`
- `Subst.act_inst.id`

These are proved without axioms by bundling the beta-for-eta and identity facts
by arity, then using expression recursion only in `Subst.act_inst.idOf`.

## Diamond/Lift Interaction Status

The adjacent substitution/instantiation interaction is now organized around one
private generalized mutual pair in `Equations.lean`:

- `diamondAt`
- `liftAt`

The old private stack has been deleted: `UnderList`, `PreLift`,
`PreNaturality`, `Interchange`, `underListAt`, `preNaturalityLiftAt`,
`preNaturalityAt`, and `interchange` are no longer part of the file.

The core statement is expressed through private facades:

- `Diamond.acted` applies a substitution to every filler of another
  substitution;
- `Diamond.actThenInst` means act first, then instantiate with acted fillers;
- `Diamond.instThenAct` means instantiate first, then act;
- `Lift.sequential` and `Lift.fused` express the lifted beta-instantiation
  companion needed by the domain branch.

The key proof-engineering layer is `Proper.AppendCoherence`.  It carries the exact
`Proper` witnesses and decomposition laws for `τ`, `src`, `dst`, `τ ⋈ src`,
and `τ ⋈ dst`.  Under-list witnesses are computed canonically with
`Proper.extendList`.  This is necessary because `Proper` witnesses are
computational data, not proof-irrelevant propositions.

The visible `diamondAt` proof is organized by the five mathematical head cases
through `DiamondSite`:

- `under`: head comes from the concrete list depth `υ`;
- `src`: head is substituted by the auxiliary substitution `κ`;
- `tau`: head comes from the ambient depth `τ`;
- `dom`: head is substituted by `σ` and calls `liftAt`;
- `pre`: head is preserved from the untouched prefix.

The visible `liftAt` proof is organized by the three mathematical head cases
through `LiftSite`:

- `under`: head comes from the concrete list depth `χ`;
- `beta`: head is the singleton binder instantiated by `lam` and calls back
  into `diamondAt`;
- `pre`: head is preserved from the untouched prefix.

The private mutual block uses `InterchangeFuel`, a pair of domain measures
considered up to swapping, together with expression-subterm descent:

- `diamondAt.src` decreases the second fuel component by `SlotAt.subWitness`;
- `diamondAt.dom` decreases the first fuel component and calls `liftAt`;
- `liftAt.beta` uses `InterchangeFuel.Lt.left_swap`;
- ordinary recursive calls into arguments use `Expr.Subterm.of_arg_ofList_cons`.

The composition chapter now has the intended public shape:

- `Subst.comp` composes arbitrary substitutions by acting with the second
  substitution on each filler of the first;
- `Subst.act_comp` proves that action preserves arbitrary substitution
  composition and calls `diamondAt` directly in the `dom` branch;
- `Subst.act_kcomp` is a short specialization of `Subst.act_comp` to
  `toSubst` and `Subst.kcomp`.

This pass improved the conceptual architecture, but not the line count: after
deleting the old stack and installing explicit target witnesses,
`Equations.lean` is about 1693 lines.  The target-witness coherence layer is
the main new size cost.

## Next Realistic Formalization Targets

1. Be careful with telescope-composition coherence.
   A naive fully arbitrary extra-τ statement compares the `Proper` instance
   for a composite telescope with nested `Proper` instances; the current
   class does not expose such coherence.  `Proper.compose` now packages the
   canonical two-stage composition, with `compose_inr_inr`,
   `compose_inr_inl`, and `compose_inl` as named rewrites.  For recursive
   binder extensions under concrete lists, use `Proper.extendList` and its
   `extendList_inr_inr`, `extendList_inr_inl`, and `extendList_inl` rewrites.

2. Keep Andrej's cleaned-up naming and comments as the baseline.
   Use `inr` for the telescope/right side, `inl` for the base/left side, and
   the computation lemmas `Subst.act_ap_inr`, `Subst.act_ap_inl_dom`, and
   `Subst.act_ap_inl_pre`.

## Validation Commands

Run from `HigherRankSyntax/`:

```bash
lake env lean HigherRankSyntax/Equations.lean
lake env lean HigherRankSyntax/SyntaxMonad.lean
lake build HigherRankSyntax
rg -n "\bsorry\b|\baxiom\b" HigherRankSyntax
```

Expected current result: the Lean files build, and `rg` reports no matches.
