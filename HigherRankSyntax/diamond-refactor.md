# Explicit-Witness Diamond Refactor Notes

This note records the current replacement architecture for the interaction
proofs in `HigherRankSyntax/HigherRankSyntax/Equations.lean`.

## Current Shape

The old private list-target stack has been removed:

- `UnderList`
- `PreLift`
- `PreNaturality`
- `Interchange`
- `underListAt`
- `preNaturalityLiftAt`
- `preNaturalityAt`
- `interchange`

The core proof is now the generalized mutual pair:

```lean
private theorem diamondAt ...
private theorem liftAt ...
```

The public composition theorem now calls `diamondAt` directly in its `dom`
branch:

```lean
theorem Subst.act_comp ...
```

and `Subst.act_kcomp` remains the short corollary of `Subst.act_comp`.

## Target Witnesses

The key implementation point is that `Proper` witnesses are computational data.
The theorem cannot merely ask typeclass search for arbitrary witnesses of
composites such as `τ ⧺ dst`.

The private package

```lean
private structure TargetProper (τ src dst : Shape C) (υ : List C.Arity)
```

carries exact witnesses for:

- `τ`;
- `src`;
- `dst`;
- `τ ⧺ src`;
- `τ ⧺ dst`;
- the laws describing how right and left injections decompose through those
  composites.

The under-list witnesses are then computed canonically by
`TargetProper.hSrcUnder` and `TargetProper.hDstUnder` using
`Proper.extendList`.  This keeps recursive argument calls aligned with the
computation lemmas for concrete list depths.

There are three important constructors:

- `TargetProper.arg`, for ordinary argument recursion;
- `TargetProper.srcStep`, for the source-filler recursive call in
  `diamondAt`;
- `TargetProper.liftBeta`, for the beta branch of `liftAt`.

There is also `TargetProper.nil`, used by `Subst.act_comp`, whose target
witness is exactly the ambient `[Proper τ]`.  This avoids comparing
`Proper.compose Shape.nil τ` with the ordinary witness for `τ`.

## Main Diamond

`diamondAt` says that action by an arbitrary substitution commutes with an
arbitrary substitution `κ` over an additional source telescope:

```lean
Diamond.actThenInst σ target κ e =
Diamond.instThenAct σ target κ e
```

Informally:

```text
act by σ, then instantiate src by the σ-acted κ-fillers
  =
instantiate src by κ first, then act by σ.
```

The proof is organized by `DiamondSite`:

- `under`: the head lies in the concrete list depth `υ`;
- `src`: the head is substituted by `κ`;
- `tau`: the head lies in the ambient depth `τ`;
- `dom`: the head is substituted by `σ`;
- `pre`: the head lies in the untouched prefix.

The `under`, `tau`, and `pre` branches preserve the head and recurse on
application arguments.  The `src` branch descends into the selected `κ` filler.
The `dom` branch calls `liftAt`.

## Lifted Companion

`liftAt` is the companion needed by the `dom` branch of `diamondAt`.  It says
that applying `κ` after a one-binder instantiation agrees with the fused
one-binder instantiation whose fillers already include `κ`.

The proof is organized by `LiftSite`:

- `under`: the head lies in the concrete list depth `χ`;
- `beta`: the head is the binder instantiated by `lam`;
- `pre`: the head lies in the untouched prefix.

The `beta` branch calls back into `diamondAt` with
`TargetProper.liftBeta`.

## Termination

The mutual pair still uses `InterchangeFuel`, a pair of domain measures
considered up to swapping, together with expression-subterm descent:

- argument recursion decreases the expression subterm;
- `diamondAt.src` decreases the second fuel component;
- `diamondAt.dom` decreases the first fuel component and calls `liftAt`;
- `liftAt.beta` uses the swapped fuel order and calls `diamondAt`.

This is the same termination geometry as the old proof, but the recursive
content is now concentrated in one generalized mutual pair.

## Line Count

Before this pass, `Equations.lean` was about 1682 lines.

After deleting the old stack and installing the explicit-witness mutual pair:

```text
Equations.lean: 1693 lines
```

So the conceptual replacement succeeded, but the hoped-for 1100-1250 line
target did not.  The additional `TargetProper` coherence laws are roughly as
large as the old specialized proof infrastructure they replaced.
