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

- `Subst.act_inst_interchange` in `HigherRankSyntaxTele/Equations.lean`

This is the adjacent substitution/one-binder-instantiation interchange lemma.
The public `Subst.act_kcomp` theorem is now factored through the generalized
`Subst.act_kcomp_τ` theorem and reduces its dom branch to this interchange
lemma; it is still the equation needed by `SyntaxMonad.comp_lift`.

## Next Realistic Formalization Targets

1. Prove `Subst.act_inst_interchange`.
   This is the real remaining fusion step: substituting a lower domain and
   instantiating one binder above it commute when the instantiation bodies are
   mapped through the lower substitution.

2. Use the same arity-bundling pattern as the one-binder identity proof.
   The upper-binder branch recurses on binder sub-arities, while the lower-dom
   branch recurses by the `DomLt` measure already used by `Subst.act`.

3. Be careful with telescope-composition coherence.
   A naive fully arbitrary extra-τ statement compares the `ProperTele` instance
   for a composite telescope with nested `ProperTele` instances; the current
   class does not expose such coherence.  `ProperTele.compose` now packages the
   canonical two-stage composition, with `compose_embed_embed`,
   `compose_embed_weaken`, and `compose_weaken` as named rewrites.  The next
   issue is matching this canonical composition with the `instCons`-extended
   instances that arise in recursive calls under binders.

4. Keep `Subst.act_kcomp_τ` as the public composition proof spine.
   Its τ-embed branch is already closed by `Subst.act_apply_embed` and the
   induction hypothesis; its dom branch is exactly `Subst.act_inst_fusion`,
   a specialization of `Subst.act_inst_interchange`.

## Validation Commands

Run from `HigherRankSyntax/`:

```bash
lake env lean HigherRankSyntaxTele/Equations.lean
lake env lean HigherRankSyntaxTele/SyntaxMonad.lean
lake build HigherRankSyntaxTele
rg -n "\bsorry\b|\baxiom\b" HigherRankSyntaxTele
```

Expected current result: the Lean files build, and `rg` reports only the
remaining `Subst.act_inst_interchange` sorry.
