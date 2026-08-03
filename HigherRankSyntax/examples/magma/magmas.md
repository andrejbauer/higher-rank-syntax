# Magmas as a fixed-prefix syntax example

This example has one sort, one binary operation, no constants, and no
equations.  It is raw magma syntax, not monoid or group syntax.

## Files

- `examples/magma/MagmaSignature.lean` instantiates `listCarrier Unit`, defines the one
  multiplication slot, finite variable contexts, their dependent slot
  eliminators, and `magmaPrefixedSyntaxMonad`.
- `examples/magma/MagmaTerm.lean` gives ordinary binary-tree terms and simultaneous
  substitution.
- `examples/magma/MagmaAdequacy.lean` proves the equivalence with ground expression fibres
  and compares the two substitution operations.

## Fixed prefix

For every carrier `C` and fixed arity `S`, the reusable construction in
`HigherRankSyntax/PrefixedSyntaxMonad.lean` is

\[
  T'_S(\Gamma)(\alpha,\tau) = \operatorname{Expr}(S \bowtie \Gamma \bowtie \alpha,\tau).
\]

Its unit maps a `Γ`-slot to `Expr.η (C.inr x)`, and its Kleisli extension is
`Subst.act` with prefix `S`.  The laws are consequences of `act_idOfη`,
`act_η_prefixed`, and `act_comp`.

For magmas, `S = magmaSignature`; the resulting internal relative monad is
`magmaPrefixedSyntaxMonad`.

## Adequacy

`MagmaTerm n` has exactly the constructors

```lean
| variable : Fin n → MagmaTerm n
| multiplication : MagmaTerm n → MagmaTerm n → MagmaTerm n
```

The two translations are

```lean
toMagmaTerm : Expr (magmaSignature ⋈ variableContext n) () → MagmaTerm n
ofMagmaTerm : MagmaTerm n → Expr (magmaSignature ⋈ variableContext n) ()
```

and satisfy both round trips:

```lean
toMagmaTerm_ofMagmaTerm
ofMagmaTerm_toMagmaTerm
```

The expression substitution arising from
`σ : Fin n → MagmaTerm m` is `magmaExpressionSubstitution σ`.  The comparison
theorem is

```lean
toMagmaTerm_act_magmaExpressionSubstitution
```

so fixed-prefix `Subst.act` is precisely `magmaSubstitution` under adequacy.
The identity and composition laws for `magmaSubstitution` are then derived
from the corresponding fixed-prefix action laws.

There are no closed terms: `MagmaTerm 0` is empty, as expected for a signature
with neither variables nor constants.  The Lean examples also check a
one-variable term, a nested binary tree, and a nontrivial simultaneous
substitution.
