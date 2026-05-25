# Higher-Rank Syntax - Active Plan

## Active Branch

The active formalization is the `endomaps` approach in
`HigherRankSyntax/HigherRankSyntaxTele`.

Do not revive the older `HigherRankSyntaxSig` representable-list-map attempt for
current proof work.  The Tele version uses cons-style representable endomaps:

- `Tele α` is an endomap on `List α`.
- `Shape C` is `Tele C.Arity`.
- `Shape.nil`, `Γ ⋈ α`, and `Γ ⋈* τ` are strict endomap operations.
- `ProperTele` supplies weakening, embedding, classification, and cover data for
  telescopes that behave like proper context extensions.

The strict associativity and unit behavior of `Tele` is the reason this branch
avoids the list-append reassociation transports that blocked earlier attempts.

## Current Status

`HigherRankSyntaxTele` has the basic syntax infrastructure:

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

The key new helper layer is the one-binder identity-instantiation bundle:

- `Subst.instId`
- `Subst.act_inst_id_of`
- `Subst.act_inst_η_pre`
- `Subst.act_inst_id`

These are proved without axioms by bundling the beta-for-eta and identity facts
by arity, then using expression recursion only in `act_inst_id_of`.

## Remaining Target

The only remaining intentional proof hole in `HigherRankSyntaxTele` is:

- `Subst.act_kcomp` in `HigherRankSyntaxTele/Equations.lean`

This is the equation needed by `SyntaxMonad.comp_lift`.

## Next Realistic Formalization Targets

1. State a tau-generalized composition theorem for `Subst.act_kcomp`.
   Do this before working on the public one-binder theorem, because recursive
   calls under arguments need the generalized statement.

2. Prove the easy branches first.
   The tau-embed branch should follow from `Subst.act_apply_embed` and the
   induction hypothesis.  The pre branch should follow from
   `Subst.act_apply_weaken_pre` and the induction hypothesis.

3. Isolate the dom-branch fusion.
   The hard case is where the first action substitutes a domain head and
   produces a one-binder `Subst.inst`.  Name this as its own lemma before
   trying to close `act_kcomp`.

4. Reuse the one-binder identity pattern.
   If the dom fusion needs an instantiation law, follow the same shape as the
   unit proof: prove the one-binder equation first, bundle mutually dependent
   arity facts, and keep expression recursion in a separate fixed-shape lemma.

## Validation Commands

Run from `HigherRankSyntax/`:

```bash
lake env lean HigherRankSyntaxTele/Equations.lean
lake env lean HigherRankSyntaxTele/SyntaxMonad.lean
lake build HigherRankSyntaxTele
rg -n "\bsorry\b|\baxiom\b" HigherRankSyntaxTele
```

Expected current result: the Lean files build, and `rg` reports only the
remaining `Subst.act_kcomp` sorry.
