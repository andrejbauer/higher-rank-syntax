# T1 as a telescope module

## Status

- **Pass A — relative Kleisli categories and modules:** complete
- **Pass B — the generic `DTel_bd` module:** complete
- **Pass C — base extension and the monoidal `ArityMod` tensor:** complete
- **Pass D — `DTel_bd` as an internal monoid:** complete

## 1. The established categorical notion

Let `J : A ⥤ E` and let `T` be a relative monad on `J`.  Its Kleisli
category has the objects of `A` and morphisms

\[
  \operatorname{Kl}(T)(X,Y)=E(JX,TY).
\]

A left module over `T` with values in a category `D` is a functor

\[
  M:\operatorname{Kl}(T)\longrightarrow D.
\]

Thus a Kleisli morphism `f : JX ⟶ TY` acts by a map

\[
  f_*:MX\longrightarrow MY
\]

such that `(η_X)_*` is the identity and
`(g ⋆ f)_* = g_* ∘ f_*`.  The words *left* and *right* vary with
convention; the functor-from-the-Kleisli-category formulation fixes the
meaning.

This is the relative version of the modules over monads used by Hirschowitz
and Maggesi for substitution-compatible syntax.  Ahrens develops modules over
relative monads explicitly.  Voevodsky uses exactly a covariant functor from a
relative Kleisli category and constructs a C-system from a relative monad and
such a module.

References:

- A. Hirschowitz and M. Maggesi, [Modules over Monads and
  Linearity](https://arxiv.org/abs/cs/0608051).
- B. Ahrens, [Modules over relative monads for syntax and
  semantics](https://arxiv.org/abs/1107.5252).
- V. Voevodsky, [C-system of a module over a `Jf`-relative
  monad](https://arxiv.org/abs/1602.00352).

## 2. The generic decoration module

Fix a carrier `C`, a global precedence structure, and a classifier policy

```lean
bd : C.Ty → Option C.Ty
```

but do not fix a signature.  Define

\[
  \mathsf{DTel}_{bd}(\Omega)
  = \sum_{\Delta:C.\mathrm{Arity}}
      \operatorname{Decoration}_{bd}(\Omega,\Delta).
\]

This is already represented by `DecoratedTelescope bd Ω`.  Its erasure is the
first projection

\[
  |-|:\mathsf{DTel}_{bd}(\Omega)\longrightarrow C.\mathrm{Arity}.
\]

The base `Ω` is deliberately raw.  A T1 telescope records classifiers written
in an external environment, but does not assert that this environment is a
well-formed context.  For example, `x : A` is a decorated telescope over the
raw arity containing `A`; the separate decoration of `A : Type` is combined
with it by concatenation.  Requiring `Ω` itself to be decorated would duplicate
that external decoration and make T1 depend on the decorated-context and
morphism structure that T2 is meant to define.  Categorically, raw arities are
the objects of `Kl(T_C)`, so the generic module must have a fibre over every raw
arity.  T2 will select the well-formed objects in the resulting total family.

A raw Kleisli substitution `σ : Ω → Ω'` acts on a decorated telescope by
substituting in every expression-valued classifier and leaving its erased
shape unchanged:

\[
  \sigma_*(\Delta,D)
  = (\Delta,\operatorname{Decoration.substitute}(\sigma,D)).
\]

The identity and composition laws are consequences of
`Decoration.substitute_comp`, the raw identity action, and the comparison of
renaming with eta-substitution.  Consequently

\[
  \mathsf{DTel}_{bd}:\operatorname{Kl}(T_C)\longrightarrow\mathbf{Type}
\]

is a module over the completely generic raw syntax relative monad `T_C`.

The fixed-signature construction comes later.  Prefixing by `S` gives a
functor from the Kleisli category of `PrefixedSyntaxMonad C S` into the raw
Kleisli structure, and pulling `DTel` back along it gives telescopes over
`S ⋈ Γ`.  Thus the generic module is not defined relative to a chosen
signature.

## 3. Substitution under a fixed suffix

The existing substitution operation has the more informative form

\[
\begin{aligned}
  \sigma &: \operatorname{Subst}(\Gamma,S\bowtie\Delta),\\
  \sigma_*^\Phi &: \mathsf{DTel}_{bd}
       (S\bowtie\Gamma\bowtie\Phi)
       \longrightarrow
       \mathsf{DTel}_{bd}(S\bowtie\Delta\bowtie\Phi).
\end{aligned}
\]

The suffix `Φ` is held fixed: `σ` substitutes the older `Γ`-variables while
leaving the newer `Φ`-variables untouched.  Equivalently, raw substitution has
a lifting operation

\[
  \sigma\mathbin{\uparrow}\Phi:
  \Gamma\bowtie\Phi\longrightarrow\Delta\bowtie\Phi
\]

which acts by `σ` on `Γ` and by the identity on `Φ`.  The displayed operation
on decorations is the direct implementation of acting by this lifted
substitution.  No additional module structure is intended here.

This distinction matters for telescope concatenation.  If

\[
  \Gamma\in\mathsf{DTel}_{bd}(\Omega),\qquad
  \Delta\in\mathsf{DTel}_{bd}(\Omega\bowtie|\Gamma|),
\]

then reindexing `Δ` must leave `|Γ|` fixed.  The required equation is

\[
  \sigma_*(\Gamma;\Delta)
  = (\sigma_*\Gamma);(\sigma_*^{|\Gamma|}\Delta),
\]

which is precisely the content of `substitute_concatenate`.  Using lifted
substitution, the same equation is

\[
  \mathsf{DTel}(\sigma)(\Gamma;\Delta)
  = \mathsf{DTel}(\sigma)(\Gamma);
    \mathsf{DTel}(\sigma\mathbin{\uparrow}|\Gamma|)(\Delta).
\]

Thus concatenation is expressed entirely using the ordinary module action,
together with the raw operation of lifting a substitution under a suffix.

## 4. The arity-module category and its tensor

Let

\[
  K=\operatorname{Kl}(\mathsf{SyntaxMonad}\ C)
\]

and let \(\underline{C.\mathsf{Arity}}:K\to\mathbf{Type}\) be the constant
functor whose value is the type of raw arities and whose action is the
identity.  Define

\[
  \mathsf{ArityMod}_C
  =
  [K,\mathbf{Type}]/\underline{C.\mathsf{Arity}}.
\]

Thus an object is exactly a raw-syntax module \(M\), together with a
substitution-invariant shape map \(|-|:M(\Omega)\to C.\mathsf{Arity}\).
A morphism is a module natural transformation that preserves shape.

This slice has the context-extension tensor

\[
  (M\otimes_{\rm tel}N)(\Omega)
  =
  \sum_{\Gamma:M(\Omega)}
    N(\Omega\bowtie|\Gamma|).
\]

Its unit has one element of empty shape.  Substitution acts on the first
component by the original Kleisli map and on the second component by that map
lifted under \(|\Gamma|\).  The natural isomorphisms
`SyntaxKleisli.extendByOne` and `SyntaxKleisli.extendByAssoc` supply the
base-extension coherence for the unitors and associator.

`Typing/TelescopeTensor.lean` installs this as a literal Mathlib
`MonoidalCategory (ArityMod C)`.  Tensor functoriality, associator and unitor
naturality, the pentagon, and the triangle are proved, not postulated.

## 5. Decorated telescopes as an internal monoid

The generic module `DTel bd`, together with its erasure map
`DecoratedTelescope.arity`, defines

`DTelArityMod bd : ArityMod C`.

Its internal-monoid operations are:

```text
unit             DecoratedTelescope.empty
multiplication   DecoratedTelescope.concatenate
```

The slice equations say that empty has shape `1` and concatenation has shape
`Γ.arity ⋈ Δ.arity`.  Naturality says that empty and concatenation commute
with raw substitution, with the second telescope acted on by the lifted
substitution.  The monoid unit and associativity diagrams are exactly the
already-proved left-unit, right-unit, and associativity laws for decorated
concatenation, including their carrier transports.

The final result is the literal categorical package

```lean
DTelMon (C := C) bd : CategoryTheory.Mon (ArityMod C)
```

No custom `TelescopeModule` structure or compatibility adapter remains.
Concrete algebra lives in `Typing/DecoratedTelescope.lean`; the monoidal
slice structure lives in `Typing/TelescopeTensor.lean`; and the internal
monoid is packaged in `Typing/DTelMonoid.lean`.

### Pass C: base extension and the monoidal slice

Completed:

- `Subst.lift` has the raw unit, composition, and two-suffix associativity
  laws required by context extension.
- `SyntaxKleisli.extendBy` is equipped with unit and associativity natural
  isomorphisms.
- `ArityMod C` is the Mathlib slice over the constant arity functor.
- the context-extension tensor, its unit, associator, and unitors install a
  `MonoidalCategory (ArityMod C)`.
- all monoidal coherence laws are proved without `sorry` or axioms.

### Pass D: the internal monoid of decorated telescopes

Completed:

- the concrete empty and concatenation algebra was moved out of the obsolete
  interface into `Typing/DecoratedTelescope.lean`;
- `DTelArityMod bd` packages `DTel bd` with its raw shape;
- `DTelOne bd` and `DTelMul bd` are shape-preserving natural
  transformations;
- the existing decorated-telescope unit, associativity, and substitution laws
  prove the Mathlib `MonObj` axioms;
- `DTelMon bd` is a `CategoryTheory.Mon (ArityMod C)`;
- the dependent example checks the internal monoid, its components, unit and
  associativity equations, and nontrivial substitution naturality.

## 6. Boundary with T2

Completing these passes proves that all raw decorated telescopes form a
telescope module.  It does not say that their classifiers are meaningful or
well formed.  T2 should define proof-irrelevant subfamilies of well-formed
contexts, telescopes, and expressions and prove that those subfamilies are
closed under this module action, empty telescope, and concatenation.  The
eventual comprehension structure is therefore a closed, typed refinement of
the T1 telescope module rather than a second substitution implementation.
