# Algebras after precomposing a relative monad

## Setup

Let

```text
J : Y -> C
```

be a functor and let `T` be a relative monad over `J`.  Thus `T` has
objects `T y` in `C`, units

```text
eta_y : J y -> T y
```

and Kleisli extension:

```text
f : J y -> T z
----------------
f^* : T y -> T z.
```

Given another functor

```text
F : X -> Y,
```

we get a relative monad `T F` over `J F` by restricting the object index:

```text
x |-> T(F x).
```

The question is: how are algebras for `T` related to algebras for `T F`?

## The basic relationship: restriction of algebras

There is always a restriction functor

```text
Res_F : Alg(T) -> Alg(T F).
```

Indeed, an algebra for `T` consists of an object `A : C` and, for every
`y : Y`, every map

```text
v : J y -> A,
```

an evaluation/extension map

```text
v^#_A : T y -> A
```

satisfying the usual unit and associativity laws.

To get an algebra for `T F`, keep the same object `A`, but only use those
operations whose index is of the form `F x`:

```text
v : J(F x) -> A
----------------
v^#_A : T(F x) -> A.
```

So precomposition of the relative monad corresponds to forgetting the algebra
operations at all objects of `Y` not seen by `F`.

## Kleisli-category interpretation

This becomes cleaner if we use Kleisli categories.

The Kleisli category `Kl(T)` has:

```text
objects:   y : Y
morphisms: y -> z  are maps  J y -> T z  in C.
```

Similarly, `Kl(T F)` has:

```text
objects:   x : X
morphisms: x -> x' are maps J(F x) -> T(F x').
```

Therefore there is a fully faithful functor

```text
Kl(T F) -> Kl(T)
```

sending

```text
x |-> F x
```

and acting as the identity on the displayed hom-sets:

```text
C(J(F x), T(F x')).
```

Thus `T F` is not a mysterious new monad.  It is the restriction of the
Kleisli theory of `T` to the objects hit by `F`.

An algebra for `T` is an object `A : C` equipped with an action of the
Kleisli category `Kl(T)` on the family

```text
y |-> C(J y, A).
```

Restricting along

```text
Kl(T F) -> Kl(T)
```

gives precisely the algebra for `T F`.

So the slogan is:

```text
Alg(T F) is the category of algebras for the Kleisli subtheory of T
on the F-indexed objects.
```

## When is restriction an equivalence?

The functor

```text
Kl(T F) -> Kl(T)
```

is always fully faithful.  Hence if every object of `Kl(T)` is isomorphic to
one in the image of `F`, then this functor is an equivalence of Kleisli
categories, and restriction should give an equivalence

```text
Alg(T) ≃ Alg(T F).
```

A sufficient condition is that `F : X -> Y` is essentially surjective and the
isomorphisms in `Y` give the corresponding Kleisli isomorphisms.  More
generally, the right condition is essential surjectivity in the Kleisli
category, not necessarily in `Y` itself.

If the image of `F` is not Kleisli-essentially-surjective, then `Alg(T F)` is
usually larger: it asks for coherent interpretation only of the restricted
part of the theory.

## Adjoints

In good cocomplete/presentable situations, the restriction functor may have a
left adjoint:

```text
Alg(T F) -> Alg(T),
```

which freely adds interpretations for the missing arities/objects of `Y`.

But this is not automatic from the definition of relative monad alone.  It is
a Kan-extension/free-algebra existence question.

## Example 1: Lawvere theories and unary restriction

Let `T` be the relative monad corresponding to a Lawvere theory, over the
inclusion

```text
J_f : Fin -> Set.
```

Then a `T`-algebra is an ordinary model of the Lawvere theory.  Concretely,
for a set `A`, it evaluates all `n`-ary terms:

```text
eval_n : (Fin n -> A) -> T(n) -> A.
```

Now take

```text
F : 1 -> Fin
```

selecting the one-element finite set.  Then `T F` sees only the object `1`.
An algebra for `T F` is no longer a full algebra for the Lawvere theory.  It
only sees the unary Kleisli operations:

```text
T(1)
```

with composition given by substitution of unary terms.  Thus a `T F`-algebra
is essentially a set with an action of the monoid of unary term operations.

For example, a group gives such an action on its underlying set by unary group
terms, but this forgets the binary multiplication as a binary operation.  So
restriction from groups to unary-term actions is far from an equivalence.

This is a good example of what precomposition does: it restricts the arities
of operations that the algebra is required to interpret.

## Example 2: restricting the arities of a syntax monad

In our higher-rank syntax situation, `Y` is some category of arities/contexts
and `T y` is the family of expressions with interface `y`.

If

```text
F : X -> Y
```

selects only some arities, then `T F` is the same syntax monad but observed
only at those arities.

An algebra for the full `T` has semantic fibres for all arities and all the
evaluation operations relating them.  An algebra for `T F` only has to
interpret expressions at the arities selected by `F`.

For instance, if `F` selects only atomic/ordinary interfaces, then `Alg(T F)`
is the category of algebras that only see the first-order-looking part of the
syntax.  The full `Alg(T)` contains additional higher-rank semantic fibres and
their coherence laws.  This matches the distinction discussed in `MATH.md`
between atomic-index restrictions and full higher-rank algebras.

## Example 3: subtheories by object restriction

More generally, suppose `T` presents a many-sorted algebraic theory, with
objects of `Y` serving as contexts/arities/sorts of operation input.

Choosing

```text
F : X -> Y
```

amounts to choosing a subcollection of those objects.  Then `T F` presents the
full Kleisli subtheory on that subcollection.  Algebras for `T F` are partial
models: they interpret exactly the operations whose arities lie in the chosen
part.

If the chosen objects are dense in the Kleisli category, nothing is lost.  If
not, the restriction forgets genuine algebraic structure.

## Summary

Precomposing a relative monad does not usually preserve its algebra category.
It gives a restriction:

```text
Alg(T) -> Alg(T F).
```

The clean way to understand it is through Kleisli categories:

```text
Kl(T F) is the full Kleisli subcategory of Kl(T) on the objects F x.
```

Therefore:

```text
algebras for T F = algebras for the restricted Kleisli theory.
```

The restriction is an equivalence when `F` is essentially surjective after
passing to the Kleisli category.  Otherwise it forgets the operations and laws
indexed by the missing objects.
