# Handoff: equations and typed higher-rank syntax

Status: exploratory. The constraints below seem solid, but the final mathematical package is not yet settled.

## Motivation and conclusions so far

Equations cannot be added only after a whole signature has been formed. They must be interleaved with object declarations, because an earlier equation may be needed for a later declaration boundary even to make sense. For dependent sums, `beta_fst` gives

```text
fst(pair(a,b)) = a : A,
```

so congruence for the family `B` gives

```text
B(fst(pair(a,b))) = B(a) type.
```

Only after conversion along this equality is the usual `beta_snd` boundary well-formed.

We therefore want one sequential notion of context. A theory is literally a prefix of syntax, and users may add operations and equations on the fly. A declaration carries both its higher-rank arity/telescope and a full judgment boundary. This suggests constructing contexts, expressions, equality, boundaries, and substitutions simultaneously, rather than using the present pipeline of raw syntax, decorations, typing, and finally equations.

An important refinement is that “equations are context slots” is true only in the broad sense of ordered context entries. With proof-irrelevant judgmental equality:

- an object entry generates expressions (a point constructor);
- an equation entry generates an identification/constraint (a path constructor), not an equation-proof expression.

Thus equation entries should not simply be given a new coarse `Expr` class. In the current framework every `Carrier` slot is automatically an `Expr.ap` head; doing this for equations would produce proof-relevant equation syntax without making the endpoints equal.

## Simplified untyped/equational case

With one raw object class, use mixed contexts

```text
Gamma ::= empty
        | Gamma, d : [Theta] box
        | Gamma, q : [Theta] (e = e')
```

where `e,e'` are expressions over `Gamma,Theta`. Object entries contribute heads; equation entries do not. Erasing equations gives an ordinary raw arity `|Gamma|`, and the old raw tree syntax is still

```text
RawExpr_Gamma = Expr(|Gamma|).
```

Let `~_Gamma` be the least equivalence containing the declared equations and closed under application and two-sided substitution. The extensional syntax is

```text
Q_Gamma = RawExpr_Gamma / ~_Gamma.
```

For a fixed protected `Gamma`, `Q_Gamma` is still a quotient relative monad for substitution of fresh metavariables. This is essentially what `Equations.md` currently constructs for one externally fixed presentation.

What changes globally is substitution of the theory/context itself. An interpretation `sigma : Gamma -> Delta` consists of expressions in `Q_Delta` for the object entries of `Gamma`, subject to every equation of `Gamma` becoming true in `Delta`:

(This paragraph uses the Kleisli/algebraic arrow direction; type-theoretic substitutions conventionally reverse these arrows.)

```text
Sub(Gamma, Delta)
  = { sigma : ObjSlot(Gamma) -> Q_Delta
    | e[sigma] = e'[sigma] for every (e=e') in Gamma }.
```

There is no component `sigma(q)` for an equation entry. Identities and composition are ordinary substitution; preservation of equations makes composition well-defined. This gives a category `EqCtx` of equational contexts and equation-preserving interpretations.

The old relative monad over the bare slot functor `J` cannot have `EqCtx` as its Kleisli category. For example, from `(x,y,q:x=y)` to an equation-free `(u,v)`, the bare assignment `x |-> u`, `y |-> v` exists, but cannot descend to quotient expressions unless `u=v`. The old `J` sees the same slots in `(x,y)` and `(x,y,q:x=y)`, so it cannot express this restriction.

For every arity `Theta`, quotient expressions nevertheless form a functor/presheaf over `EqCtx`; a valid interpretation acts by `[t] |-> [t[sigma]]`. Equivalently, we have a context-indexed family of quotient monads. A single global relative monad can be recovered later via Yoneda by taking its values to be valid substitutions, but that is a derived repackaging, not the old expression relative monad.

There is a further mutuality if hereditary arities `Theta` may themselves contain equations. An application cannot accept an arbitrary tuple of expressions; it must accept an equation-respecting instantiation of `Theta`. Then expressions depend on valid instantiations, which depend on equality of expressions. This mutuality already occurs without dependent types.

## Simplified MLTT-specific case

Before attempting a general boundary former `P`, hard-code the four standard judgments. Conceptually use a set-truncated QIIT generating simultaneously

```text
Ctx
Tel(Gamma)
Ty(Gamma)
Tm(Gamma,A)
Sub(Delta,Gamma)
```

with type and term equality represented by paths in `Ty` and `Tm`. Set truncation makes judgmental equality proof-irrelevant.

The meaningful full boundaries over `Gamma` are exactly

```text
box type
box : A
A = B type by box
u = v : A by box
```

with constructor data

```text
A : Ty(Gamma)
A,B : Ty(Gamma)
A : Ty(Gamma), u,v : Tm(Gamma,A)
```

respectively. Hence meaningfulness is intrinsic: for example, `box : A` cannot be constructed unless `A` is already a type expression in the current prefix.

A higher boundary is `[Theta] Q`, where `Theta : Tel(Gamma)` and `Q` is a full boundary over `Gamma,Theta`. The sole context-extension schema is

```text
Gamma context    Theta : Tel(Gamma)    Q : JBnd(Gamma,Theta)
-----------------------------------------------------------
                 Gamma, d:[Theta]Q context
```

The new declaration is unavailable while checking/building its own boundary. Entries inside `Theta` use the same rule, so hereditary boundaries are valid too.

The extension has two effects:

- `[Theta] box type` or `[Theta] box:A` adds a generic type/term constructor and all its instantiated applications;
- `[Theta] A=B` or `[Theta] u=v:A` adds a path constructor and all its substitution instances.

Conversion is transport in the dependent family `Tm(Gamma,-)`. Congruence is ordinary path functoriality (`congrArg`/dependent functoriality), rather than a handwritten rule for every declared symbol. This makes the Sigma `beta_fst`/`beta_snd` test work conceptually.

The price is real: because contexts mention boundaries built from `Ty/Tm`, while `Ty/Tm` are generated from declarations in contexts, this is an inductive-inductive construction; adding equation paths and quotienting makes it quotient-inductive-inductive. We are currently discussing the mathematics, not committing to a Lean encoding.

## General boundary forms: current candidate, not a conclusion

We briefly proposed presenting a general boundary operator by a dependent sort signature

```text
s : [partial(s)] sort
```

where `partial(s)` is a classifier telescope. For MLTT this would be

```text
Ty : [] sort
Tm : [A : Ty] sort,
```

whose interpretation gives object boundaries `box type` and `box:A`. More generally, instantiating `partial(s)` by expressions in `Gamma` would produce the admissible classifiers for objects of sort `s`.

This is only a candidate presentation of `P`, and its precise status remains unclear. A black-box functor `P(Expr_Gamma)` hides too much: substitution, binder lifting, equality action, positivity, and well-foundedness. A dependent classifier telescope makes these visible, but raises further questions about which telescope language is allowed, whether sort dependencies must be ranked, and whether classifier telescopes may contain proof-irrelevant equation constraints. The safest next move is to understand the hard-coded MLTT case fully before abstracting it.

## Likely categorical picture

The global object is probably a contextual category/CwF-like or dependent-clone structure of checked equational contexts and equation-preserving substitutions, not merely the current bare-slot relative monad. Object extension adds a coordinate; equation extension cuts out the subspace of interpretations satisfying an equality. For a fixed theory prefix, its expression syntax remains a relative monad in fresh metavariables. Globally these monads vary functorially with the prefix.

This does not require two user-visible notions, “theory presentation” and “object context.” The same context serves both roles: as syntax it supplies available declarations; when interpreted, it presents generators and relations.

## Main unresolved questions / suggested next steps

1. Give a completely explicit mutual/QIIT specification for the untyped case when hereditary arities may contain equations.
2. Give the corresponding MLTT-specific QIIT specification and test the entire Sigma declaration sequence, especially `beta_snd`.
3. Determine the exact global substitution structure and how the existing raw `Carrier`/`Expr` relative monad appears as its equation-erasing free cover.
4. Only then generalize the two MLTT object boundaries to a carrier-level doctrine of object judgment forms; decide whether dependent classifier telescopes are the right presentation.
5. Keep congruence a structural consequence of the construction. It should be a non-issue for theory authors, even if proving the generic metatheorem or constructing the QIIT is difficult for the kernel implementer.
