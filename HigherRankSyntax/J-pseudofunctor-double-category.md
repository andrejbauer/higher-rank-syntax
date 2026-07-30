# The generalized carrier: J as a pseudofunctor, and the double category of shapes

This note records (§1) the two-dimensional reading of the simply-typed
carrier, (§2) why its one-object form is an accident, (§3) the
definition of the generalized carrier with the intuition for each
piece, (§4) the justification that this is the right generalization,
and (§5) an audit of how much of the structure is genuinely new.
Composition is written diagrammatically (`f ; g` = "f then g"),
matching `Γ ⋈ Δ` = "Γ extended by Δ".

## 1. The simply-typed picture, delooped

Fix a carrier: a monoid `M`, a set `Ty`, slot fibres `Γ ∋[τ] α` with

```
1 ∋[τ] α ≅ ∅        (Γ * Δ) ∋[τ] α ≅ (Γ ∋[τ] α) ⊔ (Δ ∋[τ] α)      (coherently).
```

Write `P₀ Γ := Σ_{α,τ} (Γ ∋[τ] α)` for the total slot set of `Γ`,
decorated by `P₀ Γ → M × Ty` (the `P Γ` of MATH.md §4); as an object
of `Fam(M × Ty)` this is exactly `J Γ`.  Let `ℛ` be the category of
arities and renamings.  Two facts, both literal in the formalization:

1. `⋈` is a binary coproduct in `ℛ` and `1` is initial
   (`copair`, `copair_uniq`, `cover`; `unit_empty`), so `(ℛ, ⋈, 1)` is
   a cocartesian monoidal category, strictified on objects.
2. `J : ℛ → Fam(M × Ty)` is fully faithful (by definition of
   renaming) and preserves finite coproducts.

A monoidal category is a one-object bicategory (its delooping `ΣV`),
and a strong monoidal functor is a pseudofunctor between deloopings.
So the carrier is a pseudofunctor

```
ΣJ : Σ(ℛ, ⋈, 1) ⟶ Σ(Fam(M × Ty), ⊔, ∅)
```

with components:

| pseudofunctor component | carrier |
|---|---|
| 1-cells `Γ ↦ J Γ` | `slotAt` |
| 2-cells `ρ ↦ Jρ` | renamings, `J.map` |
| unit constraint `∅ ≅ J 1` | `unit_empty` |
| compositor `J Γ ⊔ J Δ ≅ J(Γ⋈Δ)` | `slotAt_mul` (components `inl`, `inr`) |
| compositor naturality | `extend_inl`, `extend_inr` |
| associativity coherence | `inl_inl`, `inr_inl`, `inr_inr` |
| unit coherences | `Carrier.unit_right`, `Carrier.unit_left` |

The puzzle "an arity is a morphism, but it is sent to a set" is
resolved by the delooping: families are the **1-cells** of
`Σ(Fam,⊔)`, promoted to morphism status by the same move that
promoted the elements of `M`.

## 2. Decompression: why a double category

In `Σ(ℛ,⋈)` the objects of `ℛ` were converted into 1-cells.  This is
possible only because of a degeneracy of the simply-typed case:
*every* `Δ` extends *every* `Γ` — the family of possible extensions
is constant, the **free self-action** of `(ℛ,⋈)` on itself.  For any
monoidal category `V` there is an action double category

```
𝔻(V):  objects = objects of V,   tight = morphisms of V,
       loose   = A : X ⇸ X⊗A,    squares (f, a) bounded by (f, f⊗a),
```

and `Σ(V)` is the compression of `𝔻(V)` along the free object
direction.  Dependency destroys exactly the freeness: which telescopes
extend `Γ` varies with `Γ`.  The compression then ceases to exist —
and a renaming of telescopes `Δ → Δ'` over `Γ` relates loose arrows
`Γ ⇸ Γ⋈Δ` and `Γ ⇸ Γ⋈Δ'` with *different codomains*, so it cannot be
a 2-cell of any bicategory.  The renaming dimension must live in the
squares of a double category.

## 3. Definition

**Definition (carrier).**  A *carrier* consists of:

**1.** A strict double category `𝔻` — objects `O` (*shapes*), tight
category `ℛ` (*renamings*), loose category `𝒮` (*telescopes*, written
`Δ : Γ ⇸ Γ⋈Δ`) — equipped with:

**(a)** a **concrete double functor** `W : 𝔻 → Sq(ℛ)`, where `Sq(ℛ)`
is the double category of commutative squares of `ℛ`: a double
functor that is the identity on objects and tight arrows and faithful
on cells [Clarke §1.1, after Bourke].  Since `Sq(ℛ)` is thin,
concreteness makes `𝔻` thin: a cell is determined by its frame.
Unfolded: every loose `Δ` has an underlying tight *weakening*
`ι(Δ) : Γ → Γ⋈Δ`, with `ι(∅) = id` and `ι(Δ·Δ') = ι(Δ);ι(Δ')`; and,
`𝔻` being thin, a square `Δ → Δ'` is no data beyond its frame
`(ρ, ρ̂)`, which necessarily commutes with the weakenings:
`ι(Δ);ρ̂ = ρ;ι(Δ')`.  Which commuting frames bound a square is the
remaining information carried by `𝔻` — syntactically: those `ρ̂` that
carry the `Δ`-part to the `Δ'`-part, preserving boundaries.  Concrete double functors
into `Sq` are the ambient notion of the double-categorical account of
algebraic weak factorisation systems [Bourke; Bourke–Garner] (their
convention draws the structured arrows vertically; transposition of
strict double categories is an isomorphism and `Sq` is
transposition-invariant, so the orientation is immaterial), whose
loose arrows are likewise arrows-with-structure (`R`-algebras, delta
lenses); here a telescope is its weakening equipped with structure —
the slots and boundaries of items 3–4.

> *Why:* appending a telescope embeds the old context into the new
> one; that embedding must itself be a renaming (today: `C.inl`), and
> every square must be compatible with it.

**(b)** *opfibration*: write `𝕃` for the category whose objects are
the loose arrows and whose morphisms are the squares, and

```
L, R : 𝕃 → ℛ      L(Δ : Γ ⇸ Γ⋈Δ) = Γ      R(Δ : Γ ⇸ Γ⋈Δ) = Γ⋈Δ
                  L(square) = its left frame ρ
                  R(square) = its right frame ρ̂
```

for the frame functors.  The axiom: **`L` is a split opfibration
whose chosen opcartesian squares are closed under loose
composition.**  Unfolded:

- for every `ρ : Γ → Γ'` and `Δ ∈ Tele(Γ)` there are a chosen
  *pushforward* `ρ⋆Δ ∈ Tele(Γ')` and a chosen square `λ_{ρ,Δ}`,

  ```
           Δ
      Γ ————⇸———— Γ⋈Δ
    ρ |   λ_{ρ,Δ}   | ρ⇑Δ           ρ ⇑ Δ := R(λ_{ρ,Δ}),
      ▼             ▼
      Γ' ———⇸———— Γ'⋈ρ⋆Δ
          ρ⋆Δ
  ```

  the *extension*, which is `L`-opcartesian: every square out of `Δ`
  whose left frame factors as `ρ;ρ''` factors through `λ_{ρ,Δ}` by a
  square with left frame `ρ''`, uniquely.  (`𝔻` being thin by (a),
  uniqueness is automatic and opcartesianness is a property of the
  frame `(ρ, ρ⇑Δ)`.)
- *splitness* (the choice is functorial):

  ```
  id⋆Δ = Δ,  id⇑Δ = id        (ρ;ρ')⋆Δ = ρ'⋆(ρ⋆Δ),  (ρ;ρ')⇑Δ = (ρ⇑Δ);(ρ'⇑ρ⋆Δ)
  ```

- *closure under loose composition* (the choice is compatible with
  concatenation):

  ```
  ρ⋆∅_Γ = ∅_{Γ'},  ρ⇑∅ = ρ        ρ⋆(Δ·Δ') = ρ⋆Δ · (ρ⇑Δ)⋆Δ',  ρ⇑(Δ·Δ') = (ρ⇑Δ)⇑Δ'
  ```

Two consequences.  `W` sends `λ_{ρ,Δ}` to the commuting square
`ι(Δ);(ρ⇑Δ) = ρ;ι(ρ⋆Δ)` — transport commutes with weakening.  And
every square factors uniquely as a chosen opcartesian square
followed by a *globular* one (left frame an identity); the globular
squares over a fixed `Γ` form the fibre category of telescopes and
telescope-renamings over `Γ` — so (b) says the entire square
structure is generated by the fibres together with the transports
`ρ⋆`.

> *Why:* a telescope mentions variables of its base, so renaming the
> base must transport the telescope; the opcartesian square is the
> universal such transport.  Today `ρ⋆ = id` and `ρ ⇑ Δ` is literally
> `Renaming.extend`; `extend_id`/`extend_comp` are the splitness
> equations, and at slot level `λ_{ρ,Δ}` acts by `ρ` on the old part
> and bijectively on the new part — `extend_inl` and `extend_inr`,
> the latter being item 3's "`P` inverts opcartesian squares" in its
> one-object shadow.

**(c)** *root*: the loose category `𝒮` has an initial object `∗`;
write `r_Γ : ∗ ⇸ Γ` for the unique loose arrow.  Uniqueness gives
`r_∗ = ∅_∗` and `r_{Γ⋈Δ} = r_Γ·Δ` for free.

> *Why:* every context is reached from the empty context by its own
> telescope (Cartmell's contextuality).  Today the root is `1`:
> `𝒮(1,Γ) = {Δ : 1*Δ = Γ} = {Γ}`, a singleton.

**2.** *Classifiers*: a functor `Ty : ℛ → Set`.

> *Why:* result types must exist over each shape and be renamable;
> constant `Ty` is the simply-typed case.

**3.** *Slots*: a **pseudo double functor** `P : 𝔻 → Σ𝔻(Set, ⊔, ∅)`
(the delooping double category: one object, one tight arrow, loose
arrows = sets, squares = functions) that inverts opcartesian
squares.  Unfolded:

- `P` assigns a set of *slots* `P(Γ,Δ)` to each loose arrow and a
  function to each square; *pseudoness* (as opposed to mere laxity)
  means the structure cells

  ```
  ∅ ≅ P(Γ, ∅_Γ)          P(Γ,Δ) ⊔ P(Γ⋈Δ, Δ') ≅ P(Γ, Δ·Δ')
  ```

  are invertible — the *additivity property*: telescopes
  concatenate, slot sets add;
- `P` *inverts opcartesian squares*: for each chosen opcartesian
  square `λ_{ρ,Δ}` of (b), the function it induces,

  ```
  ρ· := P(λ_{ρ,Δ}) : P(Γ,Δ) → P(Γ', ρ⋆Δ),
  ```

  is a bijection — pushing a telescope forward relabels its
  classifiers but neither creates nor destroys its slots.  By
  splitness these bijections are functorial (`id· = id`,
  `(ρ;ρ')· = ρ'· ∘ ρ·`); applying `P` to the closure equations of
  (b) makes them additive (the bijection at `Δ·Δ'` is the disjoint
  union of the bijections at the two pieces).  One-object shadow:
  `ρ⋆ = id` and `ρ·` is the identity on the new-part slots —
  `extend_inr`.

Define `P₀(Γ) := P(r_Γ)`, the slots of the shape `Γ`.  The former
"module law" is now a proposition: additivity at `r_{Γ⋈Δ} = r_Γ·Δ`
gives

```
P₀(Γ) ⊔ P(Γ,Δ) ≅ P₀(Γ⋈Δ).
```

> *Why:* variables are born at extension, so slot data attaches to
> the loose arrows; additivity is the logarithm law "a variable of a
> concatenation is created in exactly one of the two stages", and its
> invertibility is the classification property (today `cover` +
> `copair_uniq`).  Pushing a telescope forward relabels its
> classifiers but keeps its slots — hence `P` inverts the lifts.
> Today `P₀(Γ) = P(1,Γ)` and the displayed proposition *is*
> `slotAt_mul`.

**4.** *Boundaries*.  For a loose arrow `Δ : Γ ⇸ ·` define its set of
*boundaries*

```
Bnd(Γ,Δ) := Σ_{(Δ₀,Δ₁) : Δ₀·Δ₁ = Δ}  Σ_{α ∈ Tele(Γ⋈Δ₀)}  Ty(Γ⋈Δ₀⋈α)
```

— a cut of `Δ`, an arity based at the cut, a type based over the
arity.  A carrier assigns a boundary to every slot,

```
bnd = (pre, rest, ar, τ) : P(Γ,Δ) → Bnd(Γ,Δ),
```

subject to:

- **(B0) normalization**: under the additivity iso at a slot's own
  cut, `P(Γ, pre x) ⊔ P(Γ⋈pre x, rest x) ≅ P(Γ, Δ)`, the slot `x` is
  a right injection, `x = inr x̄`, with `pre x̄ = ∅` — a slot sits at
  the start of its own `rest`.  ((B1) alone constrains `pre` along
  the isos but does not pin it; (B0) does.)

- **(B1) locality**: under the additivity iso
  `P(Δ) ⊔ P(Δ') ≅ P(Δ·Δ')`,

  ```
  bnd(inl x) = (pre x, rest x · Δ', ar x, τ x)
  bnd(inr y) = (Δ · pre y, rest y, ar y, τ y)
  ```

  — cutting a telescope changes no slot's own boundary, only the
  bookkeeping of where the cut lies relative to it;

- **(B2) transport**: on the opcartesian square of `ρ`,

  ```
  bnd(ρ⋆x) = ( ρ⋆(pre x), (ρ⇑pre x)⋆(rest x), (ρ⇑pre x)⋆(ar x), (ρ⇑pre x ⇑ ar x)⋆(τ x) );
  ```

- **(B3) squares are boundary-compatible**: for a square
  `δ : Δ → Δ'` over `ρ : Γ → Γ'` and each `x`, there is a tight
  *prefix-restriction* `ρ↾x : Γ⋈pre x → Γ'⋈pre(δx)` with
  `ι(pre x) ; ρ↾x = ρ ; ι(pre(δx))` and

  ```
  ar(δx) = (ρ↾x)⋆(ar x),        τ(δx) = (ρ↾x ⇑ ar x)⋆(τ x).
  ```

  Note `pre` itself is *not* preserved — a renaming may move a slot
  anywhere; only the transport-track of its arity and type is
  constrained.  (Syntactically `ρ↾x` is the restriction of `ρ`, and
  its existence is a property; abstractly (B3) is the definition of
  which slot maps qualify as squares.)

> *Why:* the boundary is what a slot exports to the syntax: `Expr.ap`
> indexes children by the slots of `ar x` and the result by `τ x`.
> In a dependent telescope these may mention only the part *before*
> the slot — `pre` is MATH.md §6.2's "global precedence", invisible
> at one object because a context-independent arity typechecks
> anywhere.  Note `Bnd` is built from the carrier's own loose arrows
> (a boundary is a composable pair plus a classifier): the carrier is
> *self-indexed*, which at rank 0 is exactly the `tm → ty` shape of a
> natural model.  `Bnd` is not additive (a cut of `Δ·Δ'` is induced
> from both factors), so boundaries must live as a map over `P`, not
> inside the delooped codomain.

**5.** *Well-foundedness*: the relation
"`(Γ⋈pre x, ar x)` arises from a slot `x` of `(Γ,Δ)`" is
well-founded.

> *Why:* `η`-expansion and substitution recurse into arities; this is
> `subWf`, and it is mathematical content, not a formalization device
> (MATH.md §1).

**Remark 1 (what is property, what is presentation).**  Every small
category *is* a directed container (Ahman–Uustalu, arXiv:1604.01187):
set `Tele(Γ) := Σ_Ξ 𝒮(Γ,Ξ)` and `Γ⋈Δ := cod Δ`; strictness is
automatic because composition in a category is strictly associative
and unital.  So "the loose category is a directed container" is a
*presentation*, not a property — exactly as "a monoid is a one-object
category".  The only genuine condition imposed on `𝒮` is the root
(1c); everything else is **structure on** the double category —
asking "which double categories are carriers" is the wrong question
in the same way "which categories are monoidal" is.

**Remark 2 (where `J` went).**  The one-object `J` conflated two
roles which the generalization separates.  The *morphism-level* datum
is `P` — attached to loose arrows, additive, the lax double functor.
The *object-level* datum is `J Γ := P₀(Γ) = P(r_Γ)` with its
boundaries — the base functor of the relative monad, with `J ρ` the
square action.  The simply-typed degeneracy `P(Γ,Δ) = P₀(Δ)` is why
§1 could present "J as a pseudofunctor" without mentioning `P`.

**Remark 3 (the root determines `ℛ`).**  Let `𝕃_∗` be the category
of loose arrows out of `∗` and squares with left frame `id_∗`, and
`E : 𝕃_∗ → ℛ` the right-frame functor.  On objects `E(r_Γ) = Γ`, a
bijection by rootedness.  The natural further axiom is: **`E` is an
isomorphism of categories** — every renaming `ρ : Γ → Γ'` bounds
exactly one square `r_Γ → r_{Γ'}` under the root.  Then
`J ρ := P(E⁻¹ρ)` is functorial by construction, and "renamings are
slot maps of the shapes, `J` fully faithful" — today's situation — is
recovered as a theorem rather than a definition.  This resolves the
earlier fork (postulate `ℛ` vs. derive it): `ℛ` is pinned by the
square structure at the root.

## 4. Why this is the right generalization

Three checks.

**(i) Conservativity.**  *Proposition.*  For `O = {∗}` … more
precisely, for `𝒮` the free self-action of a monoid … the definition
reduces to the current `Carrier`, up to inert data:

| generalized component | one-object value |
|---|---|
| `𝔻` | `𝔻(ℛ,⋈)`, the self-action double category of §2 |
| root `∗`, `r_Γ` | `1`, `r_Γ = Γ` |
| `W`, `ι(Δ)` | `C.inl` |
| opcartesian lifts | `ρ⋆ = id`, `ρ ⇑ Δ = Renaming.extend` |
| `P`, `P₀ = P(r_−)`, derived module law | `slotAt`; the module law = `slotAt_mul` |
| additivity coherence | the well-order uniqueness lemmas (`relIso_of_wellOrder_eq`) |
| boundaries `(ar, τ)` | the `(α, τ)` indexing of `slotAt` |
| boundary `pre` | **unconsumed** — precisely MATH.md §6.2 |
| wf | `subWf` |

so one-object carriers = `Carrier` × precedence data, and the
compression of §2 turns the double-categorical `J` back into the
pseudofunctor of §1.

**(ii) No junk.**  Every component is consumed by the generalized
syntax at a specific site:

| component | consumer |
|---|---|
| `𝒮` (`⋈`, `∅`, `·`) | contexts of children in `Expr.ap`; the depth parameter of `Subst.act` |
| root | heads of `Expr` are slots of shapes: `P₀ = P(r_−)` |
| `ι(Δ)` | weakening the head in `Expr.η`; the left/right cases of `Subst.act` |
| opcartesian lifts | `Renaming.act`, functoriality of `T` |
| additivity of `P` | the `threeway` head dispatch of `Subst.act` |
| boundaries `(pre, ar, τ)` | indexing of children and result in `Expr.ap` (dependently: the arity must typecheck over its own prefix) |
| `Ty` | the result index of `Expr` |
| wf | termination of `Expr.η` and `Subst.act` |

**(iii) No gap.**  The intended instance realizes every component:
`O` = contexts of a dependent type theory, loose = syntactic
telescopes (a *thin* loose category: the prefix order; root = the
empty context), tight = renamings with `type(ρx) = type(x)[ρ]`,
`ρ⋆Δ = Δ[ρ]`, `P(Γ,Δ)` = declarations of `Δ`, `pre x` = the
declarations before `x`, `ar x = ∅` at rank 0 (MLTT variables) and a
telescope at higher rank (symbols, metavariables, schemata); wf =
telescopes are finite lists.  The comparison with natural models
stratifies by rank.  At rank 0 the boundary of a slot `x` over
`Ξ := Γ⋈pre x` degenerates: `ar x = ∅_Ξ` is the identity loose
arrow, so the classifier is just `τ x ∈ Ty(Ξ)` — an element of a
family on objects — and `(P₀, Ty)` has literally the signature of a
natural model whose terms are variables (`u : tm → ty`, extension =
comprehension).  At rank ≥ 1 the classifier of `x` is the pair

```
( ar x : Ξ ⇸ Ξ⋈ar x ,   τ x ∈ Ty(Ξ⋈ar x) )     — read:  ar x ⊢ τ x,
```

a hypothetical judgement whose context component is a **loose arrow
of `𝔻` itself** (the self-indexing of item 4: this is why no
constant classifier index like `M × Ty` survives dependency), and of
which only the context component is comprehended — the
representable-map discipline.  Example: a variable `x : A` has
classifier `A`; the `Π`-symbol, a rank-2 slot of a signature prefix,
has classifier

```
⟨ A : Ty ,  B : (x : El A) Ty ⟩  ⊢  Ty
```

— its arity is the two-entry telescope binding a type `A` and a
type-family `B` over a fresh `El A`-variable, itself a loose arrow.

## 5. How much structure is this, really?

The definition looks many times larger than the simply-typed
`Carrier`.  Most of it is decompression, not addition.

**Derived, not data.**  Given items 1–5:
- `P₀` and the module law (from the root and additivity, §3.3);
- the weakenings `ι(Δ)` *as slot maps*: the left injection of the
  module law is boundary-compatible by (B1), so under Remark 3 the
  tight arrow `ι(Δ)` is the unique square with that action — `W` is
  then a theorem, not data;
- `ℛ` itself (Remark 3: renamings = squares under the root);
- all squares, by concreteness of `W` (item 1(a)): a cell is
  determined by its frame, and in the syntactic reading *is* a
  boundary-compatible slot map.

**Minimal generating data.**  What remains after these derivations:

```
𝒮  (a rooted small category)                        [M; root 1]
pushforward of telescopes and types along slot maps  [absent: ρ⋆ = id]
P on loose arrows, additive, coherent                [slotAt, unit_empty, slotAt_mul]
boundaries (pre, ar, τ)                              [the (α,τ) index; pre absent]
wf                                                   [subWf]
```

— the same number of items as the simply-typed `Carrier`, with
exactly **two** genuinely new operations: the pushforward `ρ⋆` and
the prefix component `pre` of the boundary.  These are precisely the
two open problems MATH.md §6.5 (1)–(2) had already isolated; the
double category adds *nothing beyond them* — it is the bookkeeping
that makes their compatibilities (frame commutation, opcartesianness,
(B1)–(B3)) into standard categorical axioms instead of an ad-hoc
equation list.

**The caveat, expanded: what is and is not derivable.**

*Where the circle sits*: "`ρ` is a renaming" is boundary-compatibility
at every slot `x ∈ P₀(Γ)`,

```
ar(ρx) = (ρ↾x)⋆(ar x),   τ(ρx) = (ρ↾x ⇑ ar x)⋆(τ x),
```

which consumes `⋆` along a *witness* `ρ↾x : ∗⋈pre x → ∗⋈pre(ρx)`
that must itself already be a renaming — one boundary-stage down.
This is a legitimate recursion, not a vicious circle, provided the
stages descend well-foundedly.  Two amendments are needed:

- *(wf⁺)* strengthen item 5 to joint descent: the relation generated
  by arity descent `(Γ⋈pre x, ar x) ≺ (Γ,Δ)` *and* prefix descent
  `(∗, pre x) ≺ (∗, r_Γ)` is well-founded.  (Syntactically both
  strictly shorten a finite list; item 5 alone tracks only arities.)
- *(B0)* the normalization law of item 4, without which `pre` — the
  very index of the recursion — is not pinned by the axioms.

*The proposed derivation*, in three phases:

1. *(wf⁺-recursion)* Define `Adm(Γ,Γ') ⊆ {maps P₀(Γ) → P₀(Γ')}` by
   recursion on wf⁺: `φ ∈ Adm` iff for every `x` there exists
   `φ↾x ∈ Adm` at the (strictly lower) prefix stage satisfying the
   two displayed transport equations.  All conditions consult `Adm`
   and `⋆` only at wf⁺-smaller stages, so the definition is by
   well-founded recursion — no induction-recursion needed, since `⋆`
   is prior data.
2. *(properties)* Impose the axioms on the data over the now-defined
   admissible maps: splitness and closure of `⋆`, (B2), and closure
   of `Adm` under composition and identities — the latter provable
   stage-wise (compose the witnesses; uses functoriality of `⋆` one
   stage down).
3. *(assembly)* `ℛ` := shapes and admissible maps; a square
   `Δ → Δ'` over `ρ` := an admissible `ρ̂` carrying the `Δ`-part to
   the `Δ'`-part boundary-compatibly; `ι(Δ)` := the module-law
   injection `inl` (admissible by (B1) with identity witnesses), and
   `W` := the resulting frame assignment; `λ_{ρ,Δ}` := the square
   whose slot action is `⋆`'s bijection.  The double-category laws,
   concreteness of `W`, and the axioms of §3.1(a)–(b) become
   stage-wise inductions.

*Status.*  Syntactically all three phases close — indeed they are
already closed for free: for syntactic instances `ρ⋆` is the raw
renaming action of the *simply-typed* monad (`Renaming.act`, a
structural recursion carried out once, at the raw level), and `ℛ`,
`W`, squares arise by restricting the raw structure to the
well-formed fragment.  Abstractly, phases 1–3 are a construction we
have not verified end-to-end: that the assembled `(𝔻, W, P, bnd)`
satisfies every axiom of §3 (in particular the interchange-grade
compatibilities of `⋆`, which phase 2 *assumes* rather than derives)
remains to be written out.  Until then §3's chunky axiomatization is
the definition, and the equivalence with the minimal presentation —
now amended by (wf⁺) and (B0) — is a precisely-stated conjecture
rather than a proposition.

## References

- D. Ahman, T. Uustalu, *Directed containers as categories*,
  MSFP 2016, arXiv:1604.01187.
- M. Grandis, R. Paré, *Limits in double categories*, Cah. Topol.
  Géom. Différ. Catég. 40 (1999); M. Grandis, *Higher Dimensional
  Categories*, World Scientific, 2019 — double categories, `Sq`.
- J. Bourke, *An orthogonal approach to algebraic weak factorisation
  systems*, J. Pure Appl. Algebra 227 (2023), arXiv:2204.09584 —
  the double-categorical reformulation of AWFS via concrete double
  functors into `Sq(𝒞)`.
- J. Bourke, R. Garner, *Algebraic weak factorisation systems I:
  accessible AWFS*, J. Pure Appl. Algebra 220 (2016),
  arXiv:1412.6559 — double categories over `Sq(𝒞)` and their
  characterization.
- B. Clarke, *Lifting twisted coreflections against delta lenses*,
  arXiv:2401.17250 — §1.1: "concrete double functor" (identity on
  `𝔻₀`, faithful on cells), thinness over `Sq`; the double category
  `𝕃ens` as a worked example of arrows-with-structure.
- nLab, *algebraic weak factorization system*,
  ncatlab.org/nlab/show/algebraic+weak+factorization+system.
