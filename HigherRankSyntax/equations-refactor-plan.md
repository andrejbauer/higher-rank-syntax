# `Equations.lean` Refactor Status

This note records the current thesis-style organization of
`HigherRankSyntax/HigherRankSyntax/Equations.lean` after the explicit-witness
diamond/lift refactor.

## 1. Syntax-Directed Action

The file begins with the three computation lemmas for `Subst.act` on an
application head:

```lean
Subst.act_ap_inr
Subst.act_ap_inl_dom
Subst.act_ap_inl_pre
```

These are the syntax-directed action clauses.  They are the local Lean form of
the mathematical split of a head in `pre ⋈ dom ⋈ τ` into:

- the current depth `τ`;
- the substitution domain `dom`;
- the untouched prefix `pre`.

## 2. Generic Application And Unit Laws

The next chapter proves the eta and identity-instantiation facts:

```lean
Subst.act_η_inr
idOf
Subst.act_inst.η
Subst.act_inst.id
Subst.act_id
Subst.act_η
```

This is the relative-monad unit-law layer.

## 3. Action/Instantiation Interaction

The old list-target stack has been deleted:

```lean
UnderList
PreLift
PreNaturality
Interchange
underListAt
preNaturalityLiftAt
preNaturalityAt
interchange
```

The current interaction proof is the generalized private mutual pair:

```lean
diamondAt
liftAt
```

The proof-facing facades are:

```lean
Diamond.acted
Diamond.actThenInst
Diamond.instThenAct
Lift.sequential
Lift.fused
```

`diamondAt` says that acting by `σ` commutes with instantiating an arbitrary
source telescope `src` by a substitution `κ`.

`liftAt` is the lifted beta-instantiation companion needed when the `dom`
branch of `diamondAt` fires.

## 4. Explicit Target Coherence

The central implementation device is:

```lean
Proper.AppendCoherence τ src dst υ
```

It carries exact `Proper` witnesses for `τ`, `src`, `dst`, `τ ⋈ src`, and
`τ ⋈ dst`, together with the decomposition laws needed by the head-normalizing
branches.

This is necessary because `Proper` is computational data.  In particular,
`Proper.compose Shape.nil τ` does not compute like the ordinary ambient
`[Proper τ]` witness.  The constructor `Proper.AppendCoherence.nil` is used by
`Subst.act_comp` to keep the nil-target specialization definitionally aligned.

## 5. Composition And Relative-Monad Laws

The public composition layer is now the conceptual end of the file:

```lean
Subst.comp
Subst.act_comp
Subst.act_kcomp
```

`Subst.act_comp` calls `diamondAt` directly in its `dom` branch.  The Kleisli
law `Subst.act_kcomp` remains a short corollary of `Subst.act_comp`.

## Result

The conceptual duplicate recursive stack is gone.  The line-count target did
not land: the file is about 1693 lines because the explicit `Proper.AppendCoherence`
coherence layer is substantial.  The next realistic cleanup is not another
global theorem, but factoring repeated target-witness/filler-family
normalization into small local lemmas without hiding the five/three head-case
story.
