# Higher-Rank Syntax - Active Plan

## Active Branch

The active formalization is the `endomaps` approach in
`HigherRankSyntax/HigherRankSyntax`.

Do not revive the older `HigherRankSyntaxSig` representable-list-map attempt for
current proof work.  The Tele version uses cons-style representable endomaps:

- `Tele α` is an endomap on `List α`.
- `Shape C` is `Tele C.Arity`.
- `Shape.nil`, `Γ ⋈ α`, and `Γ ⋈* τ` are strict endomap operations.
- `ProperTele` supplies `inl`, `inr`, classification, and cover data for
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
- `Subst.lean`: the single fixed-shape substitution walker `Subst.act`.
- `Equations.lean`: substitution equations and monad-law proof work.
- `SyntaxMonad.lean`: the relative monad packaging.

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

## Interchange Status

The adjacent substitution/instantiation interchange is now proved in its
list-indexed form through the auxiliary layer:

- `Subst.act_inst.underListAt`
- `Subst.act_inst.underList`
- `Subst.act_inst.preNaturalityAt`
- `Subst.act_inst.preNaturality`
- `Subst.act_inst.interchange`

The theorem statements are written through private statement facades, so the
main lemmas read as equations between named constructions rather than exposing
all local `ProperTele` instances and singleton-instantiation plumbing inline:

- `Subst.act_inst.UnderList.actThenInst = UnderList.instThenAct`
- `Subst.act_inst.PreLift.sequential = PreLift.fused`
- `Subst.act_inst.PreNaturality.sequential = PreNaturality.fused`
- `Subst.act_inst.Interchange.actThenInst = Interchange.instThenAct`

The algebraic proof of the lifted commute is now in place:

- `Subst.act_inst.preNaturalityLiftAt` proves the under-list version with an
  added list depth `χ`.
- `Subst.act_inst.preNaturalityLift` is the `χ = []` wrapper.
- `Subst.act_inst.underListAt` and `preNaturalityLiftAt` are mutually recursive,
  because the dom branch of `underListAt` needs the lifted commute, while the
  β-head branch of the lift needs `underListAt` on the substituted filler.

The private mutual block now has a checked termination argument.  It uses
`InterchangeFuel`, a pair of domain measures considered up to swapping, together
with expression-subterm descent:

- filler jumps decrease one side of the fuel by `Carrier.Sub`/`DomLt`;
- the β-head call from `preNaturalityLiftAt` into `underListAt` uses the swapped
  fuel order;
- ordinary recursive calls into arguments use `Expr.Subterm.of_arg_ofList_cons`.

There are currently no `sorry`s or `axiom`s in `HigherRankSyntax`.

## Next Realistic Formalization Targets

1. Be careful with telescope-composition coherence.
   A naive fully arbitrary extra-τ statement compares the `ProperTele` instance
   for a composite telescope with nested `ProperTele` instances; the current
   class does not expose such coherence.  `ProperTele.compose` now packages the
   canonical two-stage composition, with `compose_inr_inr`,
   `compose_inr_inl`, and `compose_inl` as named rewrites.  For recursive
   binder extensions under concrete lists, use `ProperTele.extendList` and its
   `extendList_inr_inr`, `extendList_inr_inl`, and `extendList_inl` rewrites.

2. Keep Andrej's cleaned-up naming and comments as the baseline.
   Use `inr` for the telescope/right side, `inl` for the base/left side, and
   the computation lemmas `Subst.act_apply_inr`, `Subst.act_apply_inl_dom`, and
   `Subst.act_apply_inl_pre`.

## Validation Commands

Run from `HigherRankSyntax/`:

```bash
lake env lean HigherRankSyntax/Equations.lean
lake env lean HigherRankSyntax/SyntaxMonad.lean
lake build HigherRankSyntax
rg -n "\bsorry\b|\baxiom\b" HigherRankSyntax
```

Expected current result: the Lean files build, and `rg` reports no matches.
