# Semantics for higher-rank theories

A proposal answering §15 of `equational-telescopes-core.md`. Bare `§n` and bare
numbers like `13.3` refer to that note.

Results of §§1–13 are cited by their number there — `13.3`, `11.4`, `10.4` — and
are taken as established. Everything this note adds carries its status:

```
[routine]     short, no new idea, but not written down
[conjecture]  I believe it; not checked
[open]        the research question
```

**Standing assumption.** The carrier is the **list carrier** of
`examples/ListCarrier.lean`: an arity is a list of `Entry`, and an `Entry` is
itself a list of `Entry` — its binding arity. So an arity is a forest, a slot is
a position in the top-level list, and `before`/`after` are `take`/`drop`. Where
this buys something specific it is flagged; it matters most at 3.2.

---

## 0. Summary

**What is modelled.** Not the framework. A **theory** is a pair `(Ξ, 𝒫)`: a
well-formed ambient — the signature — together with a sub-presheaf `𝒫 ⊆ 𝒯₀`
naming which telescopes count as context extensions (§1). `𝒫` is not decoration:
**as soon as the theory binds, it is what supplies morphisms of models** — a
theory of order `n` has them only when `𝒯₀^{≤n−1} ⊆ 𝒫` (2.6.2).

**What a model is.** A category `𝒞` with a terminal object, together with a
filling of `Ξ` computed in `PSh(𝒞)` — Definition 9.1 with `Expr` replaced by
`PSh(𝒞)` (§2).

**The one idea.** `𝒫` and `𝒯₀` are the two ends of a chain, and **rank measures
how far out of `𝒫` the signature's `Π`s reach** (§3):

```
𝒫 = 𝒯₀^{≤1}  ⊆  𝒯₀^{≤2}  ⊆  𝒯₀^{≤3}  ⊆  …  ⊆  𝒯₀
```

Every link is a natural model on one and the same category of contexts.

**What is new.** Existing frameworks fix both ends. Arkor–Fiore have the graded
hierarchy but no dependency; Uemura and Kaposi have dependency but stop at rank
2; Gratzer–Sterling reach rank ω but drop both the grading and the contexts. The
chain is what this framework contributes (§4).

**Where the risk is.** Everything about the chain rests on Conjecture 3.2, which
is unchecked and needs a carrier operation the code does not have. §6 tabulates
the status of every claim; §7 is the order to attack them in.

---

## 1. What is modelled

### 1.1 Categories with representable maps

The ambient notion is Uemura's (arXiv:1904.04097 Def. 4.1–4.2; thesis Def. 3.2.1,
where it is called a **CwR**).

> **Definition 1.1 (CwR).** A **category with representable maps** is a category
> `C` with finite limits, together with a class `R` of arrows such that
>
> - identities lie in `R`, and `R` is closed under composition;
> - `R` is **pullback-stable**: for `f ∈ R` and any `g` into its codomain, the
>   pullback of `f` along `g` exists and lies in `R`;
> - every `f : X ⟶ Y` in `R` is **exponentiable**: `f^* : C/Y ⟶ C/X` has a right
>   adjoint `Π_f`.
>
> Arrows of `R` are **representable**. A **CwR morphism** preserves finite
> limits, representable arrows, and pushforwards along representable arrows.

Two omissions from that list are deliberate and are used throughout.

**`X ⟶ 1` need not be representable.** An object whose terminal map is
representable is a **context**; the rest are **judgments** (Gratzer–Sterling
§1.1·1). That is what separates a CwR from a clan, where every object is fibrant
(4.4), and why Uemura writes (thesis Rem. 3.2.10) that clans and display map
categories "are considered as models of a type theory" whereas CwRs "are
considered as type theories themselves".

**`R` need not be closed under pushforward.** Exponentiability says `Π_f` exists,
not that it lands back in `R`. Uemura declines that closure deliberately
(Rem. 3.2.11); 4.2 shows the omission is precisely the rank jump `1 ↦ 2`.

### 1.2 Any sub-presheaf of `𝒯₀` is a natural model

> **Lemma 1.2** `[routine]`**.** Let `𝔅` be `Ctx`, or a slice `Ctx / Ξ` of it,
> and let `𝒫` assign to each object of `𝔅` lying over `Γ` a subset
> `𝒫 Γ ⊆ 𝒯₀ Γ`, closed under `Γ ⊢ − ≈ −` and stable under `σ ⋆ −` along the
> morphisms of `𝔅`. Put
> `𝒫̃ := 𝒫 ×_{𝒯₀} 𝒯̃₀`. Then `q|_𝒫 : 𝒫̃ ⟶ 𝒫` is a natural model, with the same
> comprehension `Γ ⋈ Θ`, projection `p Γ Θ` and generic element `(⇑Θ, ν)` as
> 13.2. If moreover `𝟙 ∈ 𝒫` and `𝒫` is closed under `⋈`, then `𝒫` is a
> submonoid of 11.4.
>
> *Proof.* Pullback pasting: `yΓ ×_𝒫 (𝒫 ×_{𝒯₀} 𝒯̃₀) ≅ yΓ ×_{𝒯₀} 𝒯̃₀ = y(Γ ⋈ Θ)`.
> In setoids: 13.2's fibre at `σ` is
> `Σ (Θ' : 𝒯₀ Ξ) (_ : Ξ ⊢ Θ' ≈ σ ⋆ Θ), Filling Ξ Θ'`, and `σ ⋆ Θ ∈ 𝒫 Ξ` with
> `𝒫` `≈`-closed forces `Θ' ∈ 𝒫 Ξ`, so the fibre is unchanged. ∎

This settles 15.2's "whether `q` restricts to a natural model over it is the real
question": yes, and for any sub-presheaf whatsoever. The pullback cannot escape
`𝒫` because 13.2's comprehension is already the one `𝒫` inherits.

### 1.3 `Ctx` is a CwR

> **Proposition 1.3.** Let `𝒫` be as in 1.2, with `𝟙 ∈ 𝒫 Γ` for every `Γ` and
> `𝒫` closed under `⋈`. Write `𝒟_𝒫 := { p Γ Θ : Γ : Ctx, Θ ∈ 𝒫 Γ }`.
>
> **(a)** `[routine]` `Ctx` has finite limits. `𝟙` is terminal;
> `Γ × Δ = Γ ⋈ ⇑Δ`; and the equalizer of `σ, θ : Ξ ⟶ Γ` is `Ξ ⋈ E(σ,θ)`, where
> `E(σ,θ) : 𝒯₀ Ξ` has one entry per non-equational `z : |Γ| ∋ Λ`, binding
> `(σ ↾ z) ⋆ (⇑Γ).binding z`, with boundary `.eq (σ z) (θ z)`.
>
> **(b)** `[routine]` `𝒟_𝒫` contains identities, is closed under composition, and
> is pullback-stable.
>
> **(c)** `[conjecture]` Every arrow of `𝒟_𝒫` is exponentiable.
>
> Hence, granting (c), `(Ctx, 𝒟_𝒫)` is a CwR.
>
> **(d)** `[routine]` Every slice of a CwR is a CwR: for `(C, R)` and `X : C`,
> take `C/X` with the arrows whose underlying map lies in `R`.

*Proof of (a).* Products: by 13.2,
`Hom(Ψ, Γ ⋈ ⇑Δ) ≅ Σ (σ : Hom Ψ Γ), Filling Ψ (σ ⋆ ⇑Δ)`, and `σ ⋆ ⇑Δ = ⇑Δ` since
`⇑Δ`'s decoration names no slot of `Γ`; so the right side is
`Hom(Ψ,Γ) × Hom(Ψ,Δ)`. Equalizers: a filling of an all-equational telescope is
unique up to `∼` and exists exactly when the instantiated equations hold (13.3),
and "the equations hold after `κ`" is literally `κ ≫ σ ∼ κ ≫ θ`. Uniqueness is up
to `∼` throughout, `Ctx` being setoid-enriched (4.6).

*Proof of (b).* Identities: `p Γ 𝟙 = id` and `𝟙 ∈ 𝒫 Γ`. Composition:
`p Γ Θ ∘ p (Γ ⋈ Θ) Λ = p Γ (Θ ⋈ Λ)`, and `Θ ⋈ Λ ∈ 𝒫 Γ` by the dependent closure
of 1.4. Pullback-stability: 10.4's square exhibits the pullback of `p Γ Θ` along
`σ : Ξ ⟶ Γ` as `p Ξ (σ ⋆ Θ)`, and `σ ⋆ Θ ∈ 𝒫 Ξ` because `𝒫` is a sub-presheaf
(1.2).

*Proof of (c), modulo well-formedness.* Written out in full, with the decoration
checked path by path and the two residual obligations isolated, in
`Ctx-CwR.md` §3; the construction and the argument are summarised here.

Let `Θ : 𝒯₀ Γ` and `Λ : 𝒯₀ (Γ ⋈ Θ)`.
Define `Π_Θ Λ : dTel |Γ|` by recursion on the length of `Λ`, via its three
projections (3.4) at each slot. Write `w : |Λ| ∋ Ψ` for a slot of `Λ` and `z_w`
for the corresponding slot of `Π_Θ Λ`.

**Arity.** `|Π_Θ Λ| := prefix |Θ| |Λ|` (3.2(1)), so `z_w` has binding arity
`|Θ| ⋈ Ψ` and `(Π_Θ Λ).before z_w = Π_Θ (Λ.before w)` — the recursive call, on a
shorter list.

**The substitution.** Everything turns on one substitution, which both re-applies
the earlier slots to the `Θ`-block *and* moves that block past them:

```
θ_w  :  (|Θ| ⋈ |Λ.before w|)  ⇒  (|Γ| ⋈ |Π_Θ (Λ.before w)| ⋈ |Θ|)

θ_w (C.inl t)  :=  Expr.η t                      t a slot of |Θ|, taken in the trailing block
θ_w (C.inr v)  :=  ap z_v (Subst.ofRenaming ι_v)  v : |Λ.before w| ∋ Ψ_v
```

where `ι_v : |Θ| ⋈ Ψ_v →ʳ |Γ| ⋈ |Π_Θ (Λ.before w)| ⋈ |Θ| ⋈ Ψ_v` hits the last two
blocks. The second clause is the η-expansion of 3.2(2): `z_v` binds `|Θ| ⋈ Ψ_v`,
so mentioning it costs an application, and its arguments are the identity on both
blocks.

**Consuming `|Θ|` and `|Λ.before w|` together is what makes this typecheck.** The
boundary available sits over `|Γ| ⋈ |Θ| ⋈ |Λ.before w| ⋈ Ψ` and the one needed
over `|Γ| ⋈ |Π_Θ (Λ.before w)| ⋈ |Θ| ⋈ Ψ`: the `|Θ|`-block has *moved*, so no
substitution replacing `|Λ.before w|` alone can do it — `Subst.act` holds its
prefix fixed. Taking the whole of `|Θ| ⋈ |Λ.before w|` as the consumed block and
`|Π_Θ (Λ.before w)| ⋈ |Θ|` as its replacement puts both sides in the shape
`|Γ| ⋈ (−) ⋈ Ψ` that 3.6 wants, every re-bracketing being `rfl` by 1.6.

**The two remaining projections.**

```
(Π_Θ Λ).binding  z_w  :=  ⇑Θ ⋈ (θ_w ⋆ Λ.binding w)          at Φ = 1
(Π_Θ Λ).boundary z_w  :=  θ_w ⋆ Λ.boundary w                 at Φ := Ψ
```

Both typecheck. For the binding: `Λ.binding w : dTel (|Γ| ⋈ |Θ| ⋈ |Λ.before w|)`
of arity `Ψ`, so `θ_w ⋆ Λ.binding w : dTel (|Γ| ⋈ |Π_Θ (Λ.before w)| ⋈ |Θ|)`,
still of arity `Ψ` by 3.2.1; concatenating after
`⇑Θ : dTel (|Γ| ⋈ |Π_Θ (Λ.before w)|)` of arity `|Θ|` gives a
`dTel (|Γ| ⋈ |Π_Θ (Λ.before w)|)` of arity `|Θ| ⋈ Ψ`, which is what `z_w` binds.
For the boundary, `Bd.act θ_w Ψ` sends
`Bd (|Γ| ⋈ (|Θ| ⋈ |Λ.before w|) ⋈ Ψ)` to
`Bd (|Γ| ⋈ (|Π_Θ (Λ.before w)| ⋈ |Θ|) ⋈ Ψ)`, exactly the two displayed types.

**Why this is the right thing.** `⇑Θ` first, then `Λ`'s own binding: a filling of
`z_w` is a filling of `Λ`'s `w`-slot *given* a filling of `Θ`. And the adjunction
is then a re-bracketing rather than a construction — a component of a filling of
`Π_Θ Λ` over `Ξ` lives in `Expr (|Ξ| ⋈ (|Θ| ⋈ Ψ))`, the matching component of a
filling of `Λ` over `Ξ ⋈ Θ` in `Expr ((|Ξ| ⋈ |Θ|) ⋈ Ψ)`, and by 1.6 those arities
are **definitionally equal**. **Currying is `rfl`**: the raw layer contributes
nothing, and all the content is in `prefix` and in `θ_w`.

**What is left, and why (c) stays `[conjecture]`.** The shapes above are checked;
two things are not.

1. **`θ_w` is well formed** — `Γ ⋈ Π_Θ (Λ.before w) ⋈ ⇑Θ ⊢ θ_w : ⇑(Θ ⋈ Λ.before w)`.
   By induction over the slots in precedence order, using 8(5) at the `Expr.η`
   clause and the induction hypothesis at the `ap` clause. Given it,
   `Γ ⊢ Π_Θ Λ` follows from `Γ ⋈ Θ ⊢ Λ` by 8(8) for `⇑Θ` and 8(9) for the two
   `θ_w ⋆ −`, checked slotwise against 7.1.
2. **The bijection respects the judgements** — that the identity on raw families
   carries 6.3's filling conditions across, and `∼` to `∼`. Equational slots are
   the easy case: a `Θ`-indexed family of conditions is a condition quantified
   over `Θ`, which is what an `eq` slot with a binding telescope already means,
   and 9.2 compares components at neither side.

**The price is rank**, and it explains a gap in the literature. `Π` along a
rank-one display yields slots binding a rank-one telescope, hence rank two —
`rank (Π_Θ Λ) = max (rank Θ + 1) (rank Λ)` (3.2). So a *rank-one* framework,
Cartmell's GATs, is **not** locally cartesian closed, and Uemura must *assume*
exponentiability rather than derive it: his `□` has no rule landing in `∗`. Here
it is derived, and that the result leaves `𝒫` is precisely the jump `1 ↦ 2` of
4.2. Uemura demands exponentiability of `R` alone and never of the general
displays, so only `𝒫 = 𝒯₀^{≤1}` is needed for 1.1 — `Π` along a rank-one display.

*Proof of (d).* Slices of lex categories are lex. The three class conditions are
computed in `C` and so transport verbatim. For exponentiability,
`(C/X)/f ≅ C/dom f` identifies the pullback functor in the slice with the one in
`C`, so its right adjoint is the same.

### 1.4 Theories

> **Definition 1.4 (theory, and its contexts).** A **theory** is a pair
> `(Ξ, 𝒫)`: a well-formed ambient `Ξ`, and a sub-presheaf `𝒫 ⊆ 𝒯₀` **over the
> slice `Ctx / Ξ`** — 1.2 at `𝔅 := Ctx / Ξ` — with `𝟙 ∈ 𝒫 (Γ, γ)` at every
> object and `𝒫` closed under `⋈`, that is, `Θ ∈ 𝒫 (Γ, γ)` and
> `Λ ∈ 𝒫 (Γ ⋈ Θ, γ ∘ p)` imply `Θ ⋈ Λ ∈ 𝒫 (Γ, γ)`. Write `𝒫 Γ` when `γ` is
> clear.
>
> Its **classifying CwR** `Ctx_{(Ξ,𝒫)}` is the **whole** slice `Ctx / Ξ`,
> equipped with the natural model `q|_𝒫` of 1.2 and with, as its
> **representable maps**, the projections
>
> ```
> p Γ Θ  :  Γ ⋈ Θ ⟶ Γ        for  Θ ∈ 𝒫 Γ
> ```
>
> Its **contexts** are the objects whose map to `Ξ` is representable, i.e. the
> `Ξ ⋈ Θ` with `Θ ∈ 𝒫 Ξ`; the remaining objects are its **judgments**.
>
> `Ctx_{(Ξ,𝒫)}` **is a CwR**, granting 1.3(c). When `𝒫` is pulled back from
> `Ctx`, this is 1.3(b) followed by 1.3(d). In general `𝒫` is only defined over
> the slice, and 1.3(a)–(c) apply there verbatim: their proofs use nothing about
> the base beyond `𝒫` being a `⋈`-closed sub-presheaf on it, and `Ctx / Ξ` has
> the finite limits of 1.3(a), slices of lex categories being lex.


**Why `𝒫` lives over the slice and not over `Ctx`.** This is forced. An object
of `Ctx / Ξ` is a pair `(Γ, γ)` with `γ : Γ ⟶ Ξ` a filling of `Ξ` over `Γ`, so
**`Γ` arrives with an interpretation of `Ξ`'s symbols** and a condition naming
them can be stated by naming their images under `γ`. For MLTT (1.5) the condition
on an entry is that its boundary be `.of S` with `S ≈ γ(tm)` applied to some `A`
of boundary `.of γ(ty)`.

Over a bare `Γ : Ctx` that does not even **parse**: a `Γ` with no `ty` and `tm` —
`𝟙`, or `Ξ_mon` — offers nothing for `S` to be compared against. Nor can it be
patched at such `Γ`. Taking `𝒫 Γ = ∅` violates `𝟙 ∈ 𝒫 Γ`; taking `𝒫 Γ = {𝟙}`
breaks `⋆`-stability, since a `σ : Γ ⟶ Δ` out of such a `Γ` carries a genuine
MLTT context `Θ ∈ 𝒫 Δ` to `σ ⋆ Θ`, which by 3.2.1 has the same arity as `Θ` and
so is not `𝟙`.

The slice is also the *exact* domain, not merely a large enough one: `Hom Γ Ξ` is
inhabited precisely when `Γ` interprets `Ξ`'s symbols, so **the contexts over
which such a `𝒫` can be stated at all are the objects of `Ctx / Ξ`**. Stability
comes with expressibility — a morphism of the slice commutes with the maps to
`Ξ`, hence carries `γ(tm)` to `γ′(tm)` up to `≈`.

Some `𝒫` are insensitive to this and are pulled back from `Ctx`: the rank,
`of`- and single-entry filters of 1.5 are arity- or constructor-level and make
sense at every `Γ`. Only the ones naming *particular sorts of `Ξ`* are
irreducibly theory-relative — and those are the ones MLTT needs.

**The slice is not bigger than it looks.** An object `(Γ, γ)` has `γ` arbitrary,
which appears to admit reinterpretations of `Ξ`'s symbols that `R(Σ)` would not.
But by 4.4 **every morphism of `Ctx` is a display**, so `γ ≅ p Ξ Θ` and
`Γ ≅ Ξ ⋈ Θ` over `Ξ`. Hence

```
Ctx / Ξ   ≃   the full subcategory on the  (Ξ ⋈ Θ, p),   Θ : 𝒯₀ Ξ
```

— the contexts over `Ξ`, with morphisms fixing `Ξ`'s symbols up to `∼`. That is
what makes `Ξ ↦ Ctx_{(Ξ,𝒫)}` a genuine analogue of `Σ ↦ R(Σ)` (4.2).

`Ξ` is the signature; `𝒫` is what the object theory may hypothesise. `Ξ` alone
does not determine a theory: `Ξ_MLTT` with `𝒫 = 𝒯₀` is a logical framework over
MLTT's signature, not MLTT.

The definition is Uemura's, relativised. His bi-initial model (Def. 6.7) takes as
base category the objects `A` whose terminal map `A → 1` is representable, and
Gratzer–Sterling gloss it (§1.1·1): such an object "can be thought of as a
context", while "an arbitrary (non-representable) object stands for a
**judgment**". Here `Ξ ⋈ Θ` with `Θ ∈ 𝒫` is exactly the object whose map to `Ξ`
is `𝒫`-representable; the objects of `Ctx` not of that form — an ambient
declaring a sort, or carrying a hypothetical equation — are the judgments.

Gratzer–Sterling argue for exactly this split, independently and from the other
direction (arXiv:2012.10783, abstract): "the notion of a context plays no role in
the definitions of type theories in this sense, but the structure of a class of
display maps can be imposed on a theory **post facto** wherever needed, as
advocated by the Edinburgh school and realized by the `%worlds` declarations of
the Twelf proof assistant". `Ξ` fixes the judgments; `𝒫` is imposed afterwards;
1.2 says every choice of it is legitimate. **`𝒫` is `%worlds`, made into a
sub-presheaf.** This meets the objection that a theory ought to be `Ξ` alone
half-way; **2.6 meets it properly** — `𝒫` is what makes morphisms of models
constructible once the theory binds. Read 2.6 before deciding whether Definition
1.4 is the right shape.

Mind the scope of that claim. For an **order-one** theory `𝒫 = {𝟙}` already
suffices and nothing is lost: monoids at the minimal `𝒫` have exactly their usual
homomorphisms (2.6.1). Contexts are needed for **binding**, not for operations —
a first-order operation has its arity handled by `Σ` in the metatheory, and only
a binder needs the `Π` that `𝒫` has to transport. The failure begins at order
two.

Working in the slice is not a convenience. Over `Ctx/Ξ` a morphism fixes `Ξ`'s
components up to `∼`, which is what makes a condition naming *which sorts of `Ξ`*
an entry may mention stable under substitution. Over all of `Ctx` it is not.

### 1.5 The filters

Each condition below is `≈`-closed, `⋆`-stable and `⋈`-closed, hence a legitimate
`𝒫` by 1.2. `[routine]` throughout; the cited item is what makes it stable.

| filter | condition on every entry `z` of `Θ` | stable by | base |
|---|---|---|---|
| `of` | `Θ.boundary z` is `.of _` | 2.3 | `Ctx` |
| rank ≤ n | `rank (Θ.binding z) < n` | 3.2.1 | `Ctx` |
| single | `\|Θ\|` has one slot | 3.2.1 | `Ctx` |
| sorts in `R` | `Θ.boundary z = .of S` with `S ∈ R (Γ, γ)` | `R` a sub-presheaf | **`Ctx / Ξ`** |

The first three are arity- or constructor-level and make sense at every `Γ`, so
they are pulled back from `Ctx`. The fourth names *particular sorts of `Ξ`* and
is stated only over the slice, where `γ` supplies those sorts — see 1.4.

**The last is the one §15.2 does not have**, and without it the account of MLTT
is wrong. `𝒯₀^{of,1}` admits

```
Ξ_MLTT ⋈ [ X : of ty ]
```

— a context with a **type variable** — a perfectly good rank-one `of`-boundaried
extension that is not an MLTT context. What separates `ty` from `tm A` is neither
rank nor the boundary constructor; it is whether the sort may be hypothesised.
That is exactly Uemura's `∗` versus `□` and Kaposi–Xie's `U⁺` versus `U`.

Take `R` to be a sub-presheaf of the presheaf of sorts,
`{S : ℰ₀ Γ // Γ ⊢ boundaryOf S ≈ .sort}`. Being a sub-presheaf forces `R` to be
`≈`-closed, a real condition when the theory declares sort equations: `Γ ⊢ of S ≈
of S'` does not preserve the head of `S`. MLTT has none.

Two ways to supply `R`: as a parameter of the theory, or by splitting the `sort`
constructor into `sort` and a representable `sortRep` — Uemura's and Kaposi's
choice. **I would take the parameter.** `Bd` stays as it is, and `𝒫` is where
every such restriction has to live anyway.

**`𝒫` for MLTT, written out.** `Ξ_MLTT` declares `ty : sort` and
`tm : [A : ty] sort` among its slots. Put

```
R_MLTT (Γ, γ)  =  { S : ℰ₀ Γ  //  Γ ⊢ S ≈ γ(tm) A  for some A with
                                    Γ ⊢ A : .of γ(ty) }

𝒫_MLTT (Γ, γ)  =  { Θ : 𝒯₀ Γ  //  every entry z of Θ has
                                     Θ.binding z  = 𝟙          rank one
                                     Θ.boundary z = .of S      with S ∈ R_MLTT }
```

Here `(Γ, γ)` ranges over `Ctx / Ξ_MLTT`, and `γ(tm)`, `γ(ty)` are the components
of the filling `γ` at those two slots — the images in `Γ` of `Ξ_MLTT`'s sorts.
**Without `γ` the condition could not be written**: a `Γ` need not contain `ty`
and `tm` at all (1.4).

Unfolded, `Θ ∈ 𝒫_MLTT Γ` says exactly that `Θ` is a list

```
[ x₁ : of (tm A₁),  …,  xₙ : of (tm Aₙ) ]      with  Γ ⋈ [x₁ … x_{i−1}] ⊢ Aᵢ : .of ty
```

— an MLTT context, on the nose. What matters is what each filter throws out, and
that each throws out something different:

| excluded telescope | what it would be | excluded by |
|---|---|---|
| `[X : sort]` | a context postulating a new sort | `of` |
| `[q : eq l r]` | a hypothetical equation | `of` |
| `[F : [x : of (tm A)] of ty]` | a metavariable of arity one | rank ≤ 1 |
| `[X : of ty]` | **a type variable** | sorts in `R` |

The last passes the first two filters and is excluded only by `R`. That is the
whole reason `R` is needed, and 15.2's `𝒯₀^{of,1}` — which is the first three
rows only — describes MLTT-with-type-variables, not MLTT.

`R_MLTT` is `≈`-closed, as 1.2 requires, for two reasons worth separating. MLTT
declares no equation between **sorts** — its equations are all between
`of`-boundaried expressions — so `≈` between sorts is generated by congruence
alone and preserves heads. And a morphism `(Γ, γ) ⟶ (Δ, δ)` of the slice
satisfies `σ ≫ δ ∼ γ`, so it carries `δ(tm)` to `γ(tm)` up to `≈` and the head
condition survives substitution.

---

## 2. What a model is

### 2.1 The target

**A category `𝒞` with a terminal object.** Nothing else; everything is
interpreted in `PSh(𝒞)`, read as the judgments over `𝒞`'s contexts.

> **Notation.** A **dependent presheaf** `A` over `Γ : PSh(𝒞)` assigns a set
> `A I γ` to each `I : 𝒞` and `γ ∈ Γ I`, with restrictions
> `A I γ ⟶ A J (γ · f)` functorial in `f : J ⟶ I`; equivalently, a presheaf on
> `∫Γ`. Write `DPSh(Γ)` for these and `Σ`, `Π` for the dependent sum and product
> of `PSh(𝒞)`. A **section** of `A` is a family `s` with `s γ ∈ A I γ` and
> `(s γ) · f = s (γ · f)`. `1` is the terminal presheaf; `DPSh(1) ≅ PSh(𝒞)`, and
> a section over `1` is a global element.

> **Definition 2.1 (locally representable).** `A ∈ DPSh(Γ)` is **locally
> representable** when every `I : 𝒞` and `γ ∈ Γ I` admit an object `I ⊲ A` of
> `𝒞` with a bijection natural in `J`,
>
> ```
> 𝒞(J, I ⊲ A)   ≅   Σ (f : 𝒞(J, I)), A J (γ · f)
> ```

In words: **a context can be extended by `A`**. A general dependent presheaf is a
judgment; a locally representable one is a judgment one may hypothesise. This is
the only role `𝒞` plays, and the only demand 2.2 makes of it.

**Sizes.** Fix `𝒰₀ ∈ 𝒰₁`; `𝒞` is `𝒰₀`-small, `PSh(𝒞) := [𝒞ᵒᵖ, Set_{𝒰₀}]`, and a
dependent presheaf is **small** when `𝒰₀`-valued. `𝒰` is the Hofmann–Streicher
universe — `𝒰(I)` the small dependent presheaves over `よI`, restriction by
pullback — whose sections over `X` are the small dependent presheaves over `X`.

**When `𝒰` is needed.** Say `Ξ` **binds only terms** when every binding telescope
occurring in it, at any depth, has all entries `.of _`, or `.eq l r` with `l, r`
of `of`-boundary. `𝒰` appears at exactly one place below — the clause
`⟦.sort⟧` — and that is reached only from a binding telescope. So a theory
binding only terms needs no universe, everything staying in `PSh(𝒞)` with
`Mod_𝒞 Γ` a `𝒰₁`-set; otherwise `𝒰` is used, and nested `sort`-binders would need
a hierarchy, not pursued here. `Ξ_MLTT` binds only terms; `List : [X : sort] sort`
does not.

### 2.2 The definition

Two clauses, and the split is the point: **the ambient says what is interpreted,
`𝒫` says which interpretations must be contexts.**

> **Definition 2.2 (model).** Define, by simultaneous recursion on the pair
> (nesting depth, length) of the telescope argument — nesting well-founded by
> `C.subWf`, as in §7 —
>
> - `Mod_𝒞 Γ`, the **models** of an ambient `Γ`;
> - for `M : Mod_𝒞 Γ`: a **presheaf** `⟦Δ⟧_M` for each `Δ : 𝒯₀ Γ`; a dependent
>   presheaf `⟦β⟧_{M,Δ} ∈ DPSh(⟦Δ⟧_M)` for each boundary `β` over `Γ ⋈ Δ`; and
>   for each expression `e` over `Γ ⋈ Δ`, a small `⟦e⟧_{M,Δ} ∈ DPSh(⟦Δ⟧_M)` when
>   `boundaryOf e` **is** `.sort`, a section of `⟦S⟧_{M,Δ}` when it **is**
>   `.of S`.
>
>   *Literal equality, not `≈`*: `boundaryOf` is total (4.2) and `Bd.act`
>   preserves the constructor (2.3), so every well-formed `e` has a definite
>   boundary. Phrased up to `≈` the typing would presuppose soundness, `.of S`
>   pinning `S` down only up to `≈`.
>
>   The subscript `_{M,Δ}` always means "interpreted over `⟦Δ⟧_M`". For
>   boundaries and expressions it is part of the declaration above; for
>   **telescopes** it is an abbreviation, not a fourth family. Given
>   `Λ : 𝒯₀ (Γ ⋈ Δ)`, concatenation gives `Δ ⋈ Λ : 𝒯₀ Γ`, and iterating the first
>   projection of the telescope clause's `Σ_{⟦Δ⟧_M}(−)`, once per slot of `Λ`,
>   yields
>
>   ```
>   π  :  ⟦Δ ⋈ Λ⟧_M  ⟶  ⟦Δ⟧_M
>   ```
>
>   Then `⟦Λ⟧_{M,Δ} ∈ DPSh(⟦Δ⟧_M)` is **`π`'s family of fibres**:
>
>   ```
>   ⟦Λ⟧_{M,Δ} I d  :=  { t ∈ ⟦Δ ⋈ Λ⟧_M I  |  π_I t = d }
>   ```
>
>   with restriction inherited from `⟦Δ ⋈ Λ⟧_M`, which lands in the right fibre
>   because `π` is natural. This is the equivalence `DPSh(X) ≃ PSh(𝒞)/X` in the
>   direction `PSh(𝒞)/X ⟶ DPSh(X)`, so it inverts `Σ`:
>   `Σ_{⟦Δ⟧_M} ⟦Λ⟧_{M,Δ} ≅ ⟦Δ ⋈ Λ⟧_M` over `⟦Δ⟧_M`.
>
>   It is legitimate wherever used below because the recursion has already
>   produced `⟦Δ ⋈ Λ⟧_M`, at strictly smaller nesting depth (2.2.3). Discussion
>   in 2.2.4.
>
> **Models.**
>
> ```
> Mod_𝒞 𝟙          =  1
> Mod_𝒞 (Γ ⋈ [z])  =  Σ (M : Mod_𝒞 Γ),  Datum_𝒞 (M, z)
> ```
>
> An ambient is a list, so `Γ ⋈ [z]` is a unique decomposition. Here `z` is the
> last slot of the **ambient**, so `z.binding : 𝒯₀ Γ` and `D := ⟦z.binding⟧_M` is
> a presheaf; `z.boundary`, and the `S`, `l`, `r` occurring in it, live over
> `Γ ⋈ z.binding` and so are interpreted over `D`. `Datum_𝒞 (M, z)` is the
> **collection the model's datum at `z` is drawn from** — the `Σ` above ranges
> over it — so each row below is a collection and the datum itself is an element
> of it:
>
> ```
> z.boundary = .sort      Datum  =  the small dependent presheaves over D
> z.boundary = .of S      Datum  =  the sections of ⟦S⟧ over D
> z.boundary = .eq l r    Datum  =  { ★ | ⟦l⟧ = ⟦r⟧ }
> ```
>
> the last a subsingleton. All three are **external**: at a `sort` entry the
> datum is an actual dependent presheaf, not an element of an internal universe.
> The internal reading is the telescope clause's `⟦.sort⟧ = 𝒰`, and the two agree
> only for small data (2.2.5) — which is why this row says *small*.
>
> **Telescopes.**
>
> ```
> ⟦𝟙⟧_M        =  1
> ⟦Δ ⋈ [z]⟧_M  =  Σ_{⟦Δ⟧_M} ( Π_{⟦z.binding⟧_{M,Δ}} ⟦z.boundary⟧_{M, Δ ⋈ z.binding} )
> ```
>
> Now `z` is the last slot of a **telescope over `Γ`**, so `z.binding` is a
> telescope over `Γ ⋈ Δ` and takes the relative interpretation of 2.2.4 — unlike
> the `Datum` clause, where it lies over `Γ`. Types: `B := ⟦z.binding⟧_{M,Δ}` is
> in `DPSh(⟦Δ⟧_M)`, so `Σ_{⟦Δ⟧_M} B = ⟦Δ ⋈ z.binding⟧_M`, and
> `C := ⟦z.boundary⟧_{M, Δ ⋈ z.binding} ∈ DPSh(Σ_{⟦Δ⟧_M} B)`, whence
> `Π_B C ∈ DPSh(⟦Δ⟧_M)` and `Σ_{⟦Δ⟧_M} (Π_B C) ∈ PSh(𝒞)`.

> **Boundaries.** `⟦.sort⟧ = 𝒰`, the only use of the universe;
> `⟦.of S⟧ = ⟦S⟧`; `⟦.eq l r⟧ = { ★ | ⟦l⟧ = ⟦r⟧ }`, a subterminal.
>
> **Expressions.** Every expression is a head applied to arguments, `ap x args`.
> Its interpretation is one idea: **look up what `x` denotes, then feed it the
> interpreted arguments.** The two cases below differ only in *where* `x` is
> looked up — in the model `M` if `x` is a symbol of the signature, in the point
> of `⟦Δ⟧_M` if `x` is a variable of `Δ`.
>
> *`x` a slot of `Γ` — a **symbol**, looked up in `M`.* Its binding telescope
> `Γ.binding x` lies over `Γ.before x`, and `M` restricts there along 2.2.5's
> projection, giving a presheaf `D_x := ⟦Γ.binding x⟧`. By 4.1 `args` **is a
> filling of `Γ.binding x`**; interpreting its components and assembling gives a
> point of `D_x`, varying with `⟦Δ⟧_M` — that is, a map of presheaves
>
> ```
> ⟦args⟧  :  ⟦Δ⟧_M  ⟶  D_x
> ```
>
> `M`'s datum at `x` lives over `D_x`, and feeding it `⟦args⟧` means **reindexing
> along that map**: pullback if `x` was declared `sort`, so `⟦ap x args⟧` is a
> dependent presheaf over `⟦Δ⟧_M`; precomposition if `x` was declared `of S`, so
> `⟦ap x args⟧` is a section.
>
> *`x` a slot of `Δ` — a **variable**, looked up in the point.* There is no datum
> from `M`. Instead the telescope clause has already put a function at `x`: a
> point of `⟦Δ⟧_M` over `I` restricts to some `d ∈ ⟦Δ.before x⟧_M (I)` and carries
>
> ```
> f_x  ∈  ( Π_{B_x} ⟦Δ.boundary x⟧ ) (d)          B_x := ⟦Δ.binding x⟧_{M, Δ.before x}
> ```
>
> — precisely "for each filling of what `x` binds, something of the kind
> `Δ.boundary x` names". Here `x.binding` lies over `Γ ⋈ Δ.before x`, so `B_x` is
> *dependent* over `⟦Δ.before x⟧_M` and `⟦args⟧` is correspondingly a point of the
> fibre of `B_x` at `d`. Feeding the function its argument is then literal
> **evaluation**:
>
> ```
> ⟦ap x args⟧  :=  f_x  applied to  ⟦args⟧
> ```
>
> This is the first place the `Π` of the telescope clause is *used* rather than
> introduced; it is what that `Π` is for.
>
> **Both cases are "substitute the arguments"** — reindexing and evaluation are
> the same act, differing only in whether the function came from `M` or from the
> point. And the typing is preserved: for a head declared `of S` the result is a
> section of `⟦S⟧` reindexed along `⟦args⟧`, which by 4.2 is the interpretation of
> `boundaryOf (ap x args)`.
>
> *Two instances, over `Ξ_MLTT`.* The expression `tm A` has head `tm`, a
> **symbol**, with `D_tm = Ty` and `⟦args⟧ = ⟦A⟧ : ⟦Δ⟧_M ⟶ Ty`; since `tm` is
> declared `sort`, `⟦tm A⟧` is the pullback `Tm[⟦A⟧]` — "the terms of `A`". The
> expression `B a` occurring in `pair`'s boundary has head `B`, a **variable** of
> the binding telescope `[A : ty, B : [x : tm A] ty]`; there `⟦Δ.before B⟧ = Ty`,
> `B_B = Tm_A`, and the point carries `f_B ∈ Ty(− ⊲ A)`, a function from terms of
> `A` to types, so `⟦B a⟧` is that function evaluated at `⟦a⟧`.
>
> **Theories.** A **model of `(Ξ, 𝒫)` in `𝒞`**, written `M : Mod_𝒞 (Ξ, 𝒫)`, is an
> `M : Mod_𝒞 Ξ` under which **every `𝒫`-display is locally representable**: for
> every `Θ′ ∈ 𝒫 Ξ` and `Θ ∈ 𝒫 (Ξ ⋈ Θ′)`, the dependent presheaf
> `⟦Θ⟧_{M,Θ′} ∈ DPSh(⟦Θ′⟧_M)` satisfies 2.1.

So `Mod_𝒞 (Ξ, 𝒫) ⊆ Mod_𝒞 Ξ`: the bare ambient is what the recursion defines, the
pair is what a theory has, and they coincide exactly at `𝒫 = {𝟙}` (2.6.3). The
second clause is the whole of `𝒫`'s contribution and the only demand on `𝒞`;
everything in the first happens in `PSh(𝒞)`, where by 2.3 it is free.

**2.2.3 Termination.** `⟦Δ ⋈ [z]⟧_M` calls `⟦Δ⟧_M` at the same nesting depth and
shorter length, and `⟦Δ ⋈ z.binding⟧_M` at **strictly smaller** depth, `z.binding`
being reached by entering a slot. The second call is at a *longer* telescope, so
neither length nor ambient length alone would do: the drop in depth pays for the
growth in length. This is §7's measure.

**2.2.4 Relative interpretations are derived.** Only the absolute
`⟦Δ⟧_M ∈ PSh(𝒞)` is primitive. For `Λ : 𝒯₀ (Γ ⋈ Δ)`, concatenation gives
`Δ ⋈ Λ : 𝒯₀ Γ`, and `⟦Λ⟧_{M,Δ}` is the dependent presheaf over `⟦Δ⟧_M` along the
projection `⟦Δ ⋈ Λ⟧_M ⟶ ⟦Δ⟧_M`. Two type facts the notation can obscure:
`⟦Δ⟧_M` is a **presheaf**, so `DPSh(⟦Δ⟧_M)` is well formed and nothing depends on
a dependent presheaf; and a point of `⟦Δ⟧_M` is **not** a model of `Γ ⋈ Δ`, since
`Δ`'s slots are variables and only `Γ`'s are interpreted by `M`.

**2.2.5 Fillings are derived.** Iterating the model clause gives a projection
`Mod_𝒞 (Γ ⋈ Θ) ⟶ Mod_𝒞 Γ`, the semantic `p Γ Θ`; put `Fill_𝒞 (M, Θ)` for its
fibre over `M`. Then `[routine]`

```
Fill_𝒞 (M, Θ ⋈ Λ)  ≅  Σ (t : Fill_𝒞 (M, Θ)), Fill_𝒞 ((M, t), Λ)
```

which is 11.4 for `Mod_𝒞`, a lemma rather than something built in. Slotwise
`Fill_𝒞 (M, Θ)` is the global sections of `⟦Θ⟧_M` — the external reading, which
is what `Datum` uses because it costs no universe at a `sort` entry, the two
agreeing only for small data.

**Checking the theory clause on generators.** Locally representable dependent
presheaves are closed under `Σ`, that being composition of context extensions, so
the clause need only be imposed at telescopes generating `𝒫` under `⋈`. For `𝒫`
generated by single rank-one `of`-entries with sorts in `R` — 1.5's fourth
filter, and `𝒫_MLTT` — it reduces to **`⟦S⟧_M` locally representable for each
`S ∈ R`**, one condition per hypothesisable sort.

**2.2.6 Why this is the right definition.**
Three readings, in increasing strength (none proven yet):

```
not too many   soundness: Γ ⊢ e ≈ e′ must give ⟦e⟧ = ⟦e′⟧
not too few    the syntax must be a model of itself
exactly right  initiality — Conjecture 2.4
```

**2.2.7 TODO.** Definition 2.2 is on **representatives**: `𝒯₀ Γ` and
`ℰ₀ Γ` are setoids (10.1, 12.1), not quotients, so nothing yet descends to
`≈`-classes. All `[conjecture]`:

1. **The semantic substitution lemma**, `⟦σ ⋆ e⟧_M = ⟦e⟧_M ∘ ⟦σ⟧_M` and the same
   for telescopes — the analogue of 8(3) and 8(4). Where the work is.
2. **Soundness**, `Γ ⊢ e ≈ e′ ⟹ ⟦e⟧_M = ⟦e′⟧_M` and likewise for telescopes.
   By induction on 6.5 it reduces to (1): reflexivity is trivial, the
   **hypothesis** clause holds by construction — a model of an ambient with an
   `eq` slot exists only if that equation holds — and the **substitution** clause
   is (1).
3. **Respect for `∼`**, so that `Mod_𝒞` is well defined on `Ctx`'s hom-setoids.
4. **`Fill_𝒞 (M, Θ) ≅ Γ(⟦Θ⟧_M)`**, holding only for small data.

**2.2.8 The same definition in Uemura's and Kaposi's terms.**

| here | Uemura | Kaposi–Xie |
|---|---|---|
| `𝒞` with terminal object | base category `S` (Def. 4.5) | `𝒞 : Cat_⋄` (Def. 18) |
| `PSh(𝒞)` | `DFib_S`, equivalent to it | `PSh(𝒞)` |
| **locally representable** (2.1) | **representable** (Def. 3.8) | `Ty⁺`, a type of `U⁺` |
| `Ξ` | the signature `Σ`, generating `R(Σ)` | the signature `Ω : Ty ⋄` |
| `Ctx_{(Ξ,𝒫)}` | `R(Σ)` | the slice of `ToS⁺` over `Ω` |
| `M : Mod_𝒞 (Ξ, 𝒫)` | a **model** (Def. 4.5) | a first-order model (Def. 18) |

Two rows turn steps of §2 into citations. **2.1 is his Def. 3.8**: he calls a map
of discrete fibrations representable when it has a **right adjoint as a functor**,
and under `DFib_S ≃ PSh(S)` the map `Σ_Γ A ⟶ Γ` has one exactly when `I ⊲ A`
exists with 2.1's bijection. And **2.6's transport of `Π` is his Prop. 3.21**:
for representable `f`, `f_* = (δ^f)^*`, so pushforward along a representable map
is itself a pullback, along context extension. That is what lets 2.6 build the
comparison across a `Π` whose domain is `𝒫`-representable, and it is also his
technical reason for stopping at rank two — the identity fails for
non-representable `f`.

**Uemura's model is the functorial form of Definition 2.2**: his Def. 4.5 asks
for a base category plus a representable map functor `T ⟶ DFib_S`, and 2.4
constructs exactly that. **Conjecture 2.4 is therefore the statement that the
elementwise and functorial forms agree**, not an extra hope. What does not
transfer is the level: for him a theory *is* a whole CwR, `Σ ↦ R(Σ)`; here it is
an object of one fixed `Ctx`, with `Ξ ↦ Ctx_{(Ξ,𝒫)}` as the analogue (4.2, 4.3).

**2.2.9 Do the known cases come out right?** All `[routine]` — unfolding, not new
mathematics.

*MLTT gives a natural model, i.e. a CwF.* `ty : sort` binds nothing, so `Datum`
there is a presheaf `Ty`. `tm : [A : ty] sort` has `D_tm = ⟦[A : of ty]⟧ = Ty`,
so `Datum` there is a dependent presheaf `Tm` **over `Ty`**. `R_MLTT = { tm A }`,
so the second clause demands `⟦tm A⟧` locally representable for every `A`, which
by stability is exactly that **`Tm ⟶ Ty` is a representable natural
transformation** — Awodey's Def. 1. And `ty ∉ R_MLTT`, so `Ty` is *not* required
representable: correct, since an MLTT context cannot be extended by a type
variable. Type formers come out in CwF form —
for `Π : [A : ty, B : [x : tm A] ty] ty`,

```
⟦[A]⟧  =  Ty          ⟦[A, B]⟧  =  Σ_Ty (Π_{Tm_A} Ty) = Σ (A : Ty), Ty(− ⊲ A)
```

the second step by Prop. 3.21, so `Datum` at `Π` is
`⟦Π⟧_Γ : (A : Ty Γ) → Ty (Γ ⊲ A) → Ty Γ`, the CwF formation rule, equivalently
Awodey's `Π : P_p(Ty) ⟶ Ty`. `β` and `η`, being `eq` slots, give *conditions* —
matching that a CwF imposes them strictly.

*Untyped `λ` gives a reflexive object, including the classical obstruction.* Take

```
Ξ_λ  =  [ tm  : sort
        , lam : [ f : [x : of tm] of tm ] of tm
        , app : [ g : of tm, a : of tm ] of tm
        , β   : [ f : [x : of tm] of tm, a : of tm ]  eq (app (lam f) a) (f a) ]
```

a theory of order 2 (3.1), with `𝒫 = {𝟙}` and `𝒞 = 1`, so presheaves are sets.
Then `⟦tm⟧ = T`, `⟦lam⟧ : T^T ⟶ T`, `⟦app⟧ : T ⟶ T^T`, and `β` says
`app ∘ lam = id`: `T^T` is a **retract of `T`**, Scott's reflexive object. In
`Set` that forces `|T| ≤ 1`, so **Definition 2.2 reproduces the classical fact
that untyped `λ` has no non-trivial set model**, rather than admitting junk —
the more informative half of the check. Enlarging `𝒫` to the rank-one `of tm`
telescopes makes `⟦tm⟧` locally representable and turns `⟦lam⟧` into
`⟦lam⟧_I : ⟦tm⟧(I ⊲ tm) ⟶ ⟦tm⟧(I)`, the first-order presentation with contexts
and substitution — Kaposi–Xie's Def. 4 — where non-trivial models exist.

*Monoids come out as monoids.* At `𝒞 = 1`, `𝒫 = {𝟙}`, `Ξ_mon` (`Ctx-CwR.md` §3.0)
gives a set `S`, an element `e`, a function `m : S × S → S` — `⟦[x, y]⟧` being
`S × S`, built by `Σ` alone since `Π_1` is trivial — and three subsingletons, so
`Mod_1(Ξ_mon, {𝟙})` is the monoids, the axioms appearing as *properties* rather
than chosen proof data.


### 2.3 Why the target need be no more than a category

`PSh(𝒞)` is a presheaf topos, hence locally cartesian closed and finitely
complete, so:

- **all `Π` exist** — arbitrary rank is definable at no cost;
- **all equalizers exist** — equational slots in any position cost nothing, and
  there is no need for a class of "equational displays" (15.1's second bullet;
  4.4 shows why looking for one would collapse);
- a **universe** is available at a size bump, needed only as 2.1 delimits.

The only thing not free is **local representability**, demanded exactly where a
boundary extends a context — at the sorts named by `R`. §3 is about where that
bites.

### 2.4 Functorial form, and initiality

For `σ : Ξ ⟶ Γ` and `M : Mod_𝒞 Ξ`, interpreting each slot `z` of `Γ` by
`⟦σ z⟧_M` gives

```
Mod_𝒞 : Ctx ⟶ Set     covariant,  Mod_𝒞 𝟙 = 1,  ⋈ ⟼ dependent sum
```

respecting `∼`, which compares exactly the slots carrying data. That is the
*collection* varying with the ambient. A **single** model is functorial in a
second way: `M : Mod_𝒞 Ξ` induces

```
⟦−⟧_M  :  Ctx_{(Ξ,𝒫)} ⟶ PSh(𝒞)          Ξ ⋈ Θ ⟼ ⟦Θ⟧_M
```

preserving the terminal object and base change along displays; and `M` lies in
`Mod_𝒞 (Ξ, 𝒫)` precisely when it also **sends representable maps to representable
maps**, which is 2.2's second clause and Uemura's Def. 4.5.

> **Conjecture 2.4** `[conjecture]`**.** For a theory `(Ξ, 𝒫)` and `𝒞` with a
> terminal object, naturally in `𝒞`,
> ```
> Mod_𝒞 (Ξ, 𝒫)   ≅   CwR( Ctx_{(Ξ,𝒫)} , PSh(𝒞) )
> ```
> equivalently, `Ctx_{(Ξ,𝒫)}` is the free such CwR on `Ξ`, and the syntactic
> model is initial.

Expected easy in both directions, the syntax having been built freely: a CwR
morphism out of `Ctx_{(Ξ,𝒫)}` is determined by where it sends the slots of `Ξ`,
every telescope being built from entries, every boundary from expressions, every
expression from `ap`; and it exists exactly when the declared equations hold, by
6.6.

### 2.5 The four translations at one stroke `[conjecture]`

Kaposi–Kovács define `–ᴬ` (algebra), `–ᴹ` (morphism), `–ᴰ` (displayed), `–ˢ`
(section) by four recursions, then prove them the `Con/Sub/Ty/Tm` columns of one
model of the theory of signatures valued in finite-limit cwfs (POPL 2019 §7.3;
Kovács thesis Thms. 1–2), with the payoff **induction ⟺ initiality**.

Here it should be cheaper, 2.2 being already one recursion: run it with target
`flCwF` rather than `Set` and the four translations are objects, morphisms,
displayed objects and sections of a single functor. `–ᴰ` and `–ˢ` should then
need no recursion at all — Bocquet–Kaposi–Sattler's Construction 11 turns a
displayed higher-order model over a first-order model into a displayed
first-order model, and defines a section of the former as a section of the
sconing. That is a construction on *models*, so it applies to `Mod_𝒞` as stated.

### 2.6 Morphisms of models

Definition 2.2 gives objects only. Morphisms are Uemura's Def. 4.14 elementwise.

> **Definition 2.6.** Let `M : Mod_𝒞 (Ξ, 𝒫)` and `N : Mod_𝒟 (Ξ, 𝒫)`. A
> **morphism** `M ⟶ N` is *a map of contexts, together with a comparison of the
> interpreted data, commuting and preserving context extension*. It consists of
> the following.
>
> **(a) A functor `F : 𝒞 ⟶ 𝒟` preserving the terminal object.** Write
> `F^* Y := Y ∘ F` for viewing `N`'s presheaves from `𝒞`. Everything below is
> compared **in `PSh(𝒞)`**, `M`'s side being there already and `N`'s brought over
> by `F^*`.
>
> **(b) A comparison at each slot `x` of `Ξ`, the slots taken in order.** `M` and
> `N` interpret `x` over *different* bases — `⟦x.binding⟧_M` in `PSh(𝒞)` and
> `⟦x.binding⟧_N` in `PSh(𝒟)` — so `N`'s datum is first transported to `M`'s
> base: apply `F^*`, then pull back along `α := α_{x.binding}` from (c). Writing
> `D := ⟦x.binding⟧_M` and `T(−) := α^* F^* (−)` for that transport,
>
> ```
> x : sort     a map        ⟦x⟧_M ⟶ T ⟦x⟧_N               in DPSh(D)
> x : of S     an equation  α_S ∘ ⟦x⟧_M  =  T ⟦x⟧_N        as sections over D
> x : eq l r   nothing
> ```
>
> where `α_S` is the comparison at the sort `S`, also from (c). Reading the
> second row: applying the comparison to `M`'s element gives `N`'s element.
>
> **(c) Comparisons everywhere else are determined, not given.** From (b) one
> constructs, by recursion mirroring 2.2 and in its order, comparisons at
> expressions and boundaries, and at each `Δ : 𝒯₀ Ξ` a map
>
> ```
> α_Δ  :  ⟦Δ⟧_M  ⟶  F^* ⟦Δ⟧_N
> ```
>
> with `α_𝟙 = id`. Following the telescope clause: the `Σ` transports
> **covariantly**, so `α` extends over it from the data already fixed; the `Π`
> is **contravariant in its domain** and transports *only when that domain is
> `𝒫`-representable* — there `Π_B C` is evaluation at an extension (2.2.8), and
> `F` carries `I ⊲ B` to `F I ⊲ B` by (d).
>
> This is well founded: `x.binding` lies over `Ξ.before x`, so `α_{x.binding}`
> needed in (b) at `x` involves only slots preceding `x`; and (c) and (d)
> interleave by rank, `𝒫`-telescopes being interpreted with no non-trivial `Π`.
>
> **(d) Preservation of `𝒫`-comprehension.** For `Θ ∈ 𝒫` and `I : 𝒞`, the two
> objects `F (I ⊲ ⟦Θ⟧_M)` and `F I ⊲ ⟦Θ⟧_N` come with a canonical comparison:
> `F` of the projection `I ⊲ ⟦Θ⟧_M ⟶ I` together with `α_Θ` applied to the
> generic element of `⟦Θ⟧_M` gives, by the universal property of `⊲` in `𝒟`, a
> map
>
> ```
> F (I ⊲ ⟦Θ⟧_M)  ⟶  F I ⊲ ⟦Θ⟧_N
> ```
>
> which is required to be an **isomorphism**. In words: **`F` takes a context
> extended by `Θ` to the extension by `Θ`'s image.**

**Where the definition can fail.** Everything in (a), (b), (d) is data or a
condition one can simply impose; (c) is the only clause that can refuse to
produce anything.

> **The construction in (c) goes through exactly when every `Π` occurring in
> `⟦Δ⟧` is along a `𝒫`-telescope.** Otherwise `α_Δ` is not determined by (b) and
> has no canonical value, so Definition 2.6 stops defining a homomorphism.

That is the precise form of Kaposi–Xie's observation (§2.3) that a homomorphism
of second-order models of untyped `λ` would need
`α (lam_M f) = lam_N (α ∘ f ∘ ?)`, "but we don't know what to put in place of the
`?`": the `?` is the missing `α_Δ` at `Δ = [f : [x : of tm] of tm]`, whose
interpretation is `T^T`.

**2.6.1 Two checks.** *Monoids*: `𝒞 = 𝒟 = 1`, `F = id`. The sort slot gives
`α : S ⟶ S′`; `⟦[x, y]⟧ = S × S` is built by `Σ` alone so `α_{[x,y]} = α × α`;
and the remaining clauses read `α (e) = e′` and `α (m (x,y)) = m′ (α x, α y)` —
**the usual monoid homomorphism**, at the minimal `𝒫`. *Untyped `λ`*:
`D_lam = T^T` is a `Π` along `⟦tm⟧ ∉ 𝒫`, so `α_{D_lam}` is not constructible from
`α`, and there is no morphism until `𝒫` is enlarged.

**2.6.2 How far the construction reaches** `[conjecture]`. Interpreting a
telescope of rank `n` takes `Π` along telescopes of rank up to `n−1`, so:

> An order-`n` theory has morphisms of models when `𝒯₀^{≤ n−1} ⊆ 𝒫`.

The two knobs of 4.1 are therefore **not independent**. Order-one theories need
only `𝒯₀^{≤0} = {𝟙} ⊆ 𝒫`, which always holds — hence monoids have homomorphisms
at the minimal `𝒫`, as 2.6.1 confirms. Rank-one contexts, what MLTT and every
SOGAT take, support order ≤ 2 and no further: **that is where the SOGAT boundary
comes from, derived rather than stipulated.** An order-3 theory such as 3.4's
`W`-without-`Π` needs `𝒯₀^{≤2} ⊆ 𝒫`, i.e. contexts admitting a **metavariable of
arity one**, which a logical framework has and MLTT does not. That is Q2.

**2.6.3 The minimal `𝒫`, and higher-order models.** `𝒫 = {𝟙}` gives a theory
**with no contexts**: representable maps are the isomorphisms, so `Ξ` is the only
object of `Ctx_{(Ξ,{𝟙})}` with representable terminal map and every other object
is a judgment; there are no hypothetical judgments, and `q|_𝒫` is the trivial
natural model.

**For an order-one theory this is the right choice, not a degenerate one.** The
mechanism is that `Π_1 C = C`: a rank-one telescope interprets by iterated `Σ`
with every `Π` trivial, hence covariantly. Granting 2.4, a model at `𝒞 = 1` is
then a **lex functor** `Ctx/Ξ ⟶ Set` — Cartmell's functorial semantics of a GAT,
and Uemura's Def. 7.1, "a theory over `T` is a cartesian functor `T ⟶ Set`". The
identification is of the *notion*, not the route: he starts from a `T` with
non-trivial `R` and forgets it, whereas here `R` is trivial from the outset. That
is why his Thm. 7.31, `Th_T ≃ Mod_T^dem` — the representability-forgetting notion
being equivalent to the **democratic** models — is a parallel and not a transfer:
it compares two notions over one `T` with its `R` intact, whereas the analogue
here would compare `Mod(Ξ, {𝟙})` with `Mod(Ξ, 𝒫)` over two different `𝒫`. Worth
chasing.

Taking `𝒫 = {𝟙}` also makes 2.2's second clause vacuous, and its first clause
then never mentions `𝒞` — by 2.3 it uses only finite limits and dependent
products, so it reads verbatim in any LCCC. That *generalisation* of Definition
2.2 is Bocquet–Kaposi–Sattler's **higher-order model** (FSCD 2023 Def. 1, "without
context extensions", classified by an LCCC), and it is where the reflexive-object
semantics of 2.2.9 lives. The name tracks how *binding* is represented — by an
exponential, versus by context extension — not how deeply `Ξ` binds; **the order
of a theory (3.1) and the order of a model are different axes.** Kaposi–Xie say
"second-order model" for what BKS call "higher-order"; the latter is the right
name here, rank being unbounded.

**2.6.4 Status** `[conjecture]`. That Definition 2.6 composes, so that models and
morphisms form a category; that it agrees with Uemura's Def. 4.14 under 2.4; and
2.6.2's reach. None is checked.

---

## 3. Rank

### 3.1 Definition

```
rank 1  =  0
rank Θ  =  max over  z : |Θ| ∋ Λ  of  (rank (Θ.binding z) + 1)
```

`[routine]` `≈`-invariant, since 7.4's first clause gives `|Θ| = |Θ'|` strictly;
`⋆`-invariant by 3.2.1; `rank (Θ ⋈ Λ) = max (rank Θ) (rank Λ)`.

Over the list carrier this is concrete: **`rank` is the height of the `Entry`
forest**, an entry binding nothing being a leaf of height 1. So it is computable
and decidable, and each `𝒯₀^{≤n}` is cut out by a decidable predicate on the
underlying list — which is what a proof assistant would need to check membership
of `𝒫`.

Mind one shift. §15.2 calls `Π : [A : ty, B : [x : tm A] ty] ty` a *rank-2
entry*, meaning its **binding telescope** has rank 2; the telescope `Ξ_MLTT`
containing it has rank 3. Say **`Ξ` is a theory of order `n`** when every entry's
binding telescope has rank ≤ n, i.e. `rank Ξ ≤ n+1`. MLTT is order 2; its
contexts are rank 1.

### 3.2 `Π` raises the rank

> **Conjecture 3.2** `[conjecture]` **— the risk gate.** For `Θ : 𝒯₀ Γ` and
> `Λ : 𝒯₀ (Γ ⋈ Θ)` there is `Π_Θ Λ : 𝒯₀ Γ` with one slot `z_w` per slot
> `w : |Λ| ∋ Ψ`, **binding `Θ ⋈ Λ.binding w`**, carrying `Λ`'s boundary at `w`
> translated as in (2) below; and `p (Π_Θ Λ)` is right adjoint to base change
> along `p Θ`.
>
> Then `rank (Π_Θ Λ) = max (rank Θ + 1) (rank Λ)`.

**The binding is `Θ ⋈ Λ.binding w`, not `Θ ⋈ Λ.before w ⋈ Λ.binding w`.** An
earlier draft of this note had the latter; it is wrong, and two independent
checks say so.

*Arities.* By 13.2 the adjunction unfolds, for `σ : Ξ ⟶ Γ`, to

```
Filling Ξ (σ ⋆ Π_Θ Λ)   ≅   Filling (Ξ ⋈ σ ⋆ Θ) ((σ, ν) ⋆ Λ)
```

A component of the right side at `w` is an expression in `|Ξ| ⋈ |Θ| ⋈ Ψ` — the
slots of `Λ.before w` are **not** in scope, being supplied by the filling rather
than bound. So the left side's component at `z_w` must live in `|Ξ| ⋈ |Θ| ⋈ Ψ`
too, forcing `z_w` to bind `|Θ| ⋈ Ψ`. Under the over-binding version the two
sides do not even have the same arities.

*Rank.* The corrected version gives
`max_w (max (rank Θ) (rank (Λ.binding w)) + 1) = max (rank Θ + 1) (rank Λ)`,
which is Arkor's `ord (X ⇒ Y)` on the nose (4.2). The over-binding version gives
`max (rank Θ + 1) (rank Λ + 1)`, which is not. That the corrected construction
reproduces the order formula exactly is the best evidence available that it is
the right one.

*What remains to be checked*, in increasing order of difficulty.

1. **The arity.** `|Π_Θ Λ|` is the arity whose slots are those of `|Λ|` with each
   binding arity prefixed by `|Θ|`:
   ```
   prefix Ω Γ  :  Arity        with    Γ ∋ α  ≃  prefix Ω Γ ∋ (Ω ⋈ α)
   ```
   Over an abstract carrier this is **not derivable** from 1.1's operations —
   `⋈`, `∋`, `before`/`after`, `inl`/`inr`/`copair`, `subWf` — and would have to
   be axiomatised. Over the list carrier the question is moot: it is `List.map`,
   ```
   prefix Ω Γ  :=  ofList ((underlyingList Γ).map (fun e => .mk (underlyingList Ω ++ e.arity)))
   ```
   and everything needed falls out of `map` commuting with `take`, `drop` and
   `++`:
   - slots correspond **at the same index**, since position `i` acquires arity
     `underlyingList Ω ++ underlyingList α = underlyingList (Ω ⋈ α)`;
   - `before` and `after` of a prefixed slot are the prefixings of `before` and
     `after` (`map`/`take`, `map`/`drop`), so `factor` transports;
   - `prefix Ω` is a monoid homomorphism (`map`/`++`), `prefix 1 = id`, and
     `prefix Ω ∘ prefix Ω' = prefix (Ω ⋈ Ω')` by associativity of `++`.

   So the obligation that looked hardest is the easiest, and 3.2's risk sits
   entirely in (2)–(4).
2. **The decoration.** Written out in the proof of 1.3(c): the substitution
   `θ_w` re-applies each earlier slot `v` to the `Θ`-block as `z_v (…)`, and
   consumes `|Θ| ⋈ |Λ.before w|` in one go so that the `Θ`-block can move past
   the earlier slots — which a substitution replacing `|Λ.before w|` alone
   cannot do. **The arities there are checked.**
3. **Well-formedness.** That `θ_w` is a well-formed substitution, whence
   `Γ ⊢ Π_Θ Λ` from `Γ ⋈ Θ ⊢ Λ`, and preservation of 7.4. **Not checked** —
   1.3(c), residual obligation 1.
4. **The adjunction respects the judgements.** The raw bijection is the identity
   on families, currying being `rfl`; what is open is that it carries 6.3's
   filling conditions and `∼` across. **Not checked** — 1.3(c), residual
   obligation 2.

*Sanity check.* `Γ = 𝟙`, `Θ = [x : sort]`, `Λ = [y : sort]`. Then
`Π_Θ Λ = [z : [x' : sort] sort]`, and both sides of the display are "an
expression in `|Ξ| ⋈ |Θ|` of boundary `sort`".

Granting it, each level of the chain has a closure description `[conjecture]`:

```
𝒫 = 𝒯₀^{≤1}      the representable maps — no Π
𝒯₀^{≤2}          closure of 𝒫 under composition (Σ) and Π-along-𝒫
𝒯₀^{≤n+1}        closure under Π-along-𝒯₀^{≤n}
𝒯₀               closure under Π along anything
```

Closure of `𝒯₀^{≤2}` under `Π`-along-`𝒫` is a computation: with `rank Θ = 1` and
`rank Λ ≤ 2`, `max(2, 2) = 2`. Iterating stays at 2. Rank 3 needs `rank Θ = 2`.

### 3.3 What rank measures

**How far out of `𝒫` the signature's `Π`s reach.** Semantically (2.3), `Π` along
a locally representable map preserves local representability; `Π` along a general
map does not. So a **rank ≤ 2** theory only ever pushes forward along
representables and stays inside its own natural model; a **rank ≥ 3** theory
leaves it and lives in `PSh(𝒞)` proper. Rank is the measure of that reach.

### 3.4 A theory of rank 3: `W` without `Π`

Gratzer–Sterling supply the canonical example (§1.1·3): "the **W-type**, whose
elimination rule apparently cannot even be written down without higher-level
hypothetical judgments **in the absence of dependent product types**."

```
W   : [ A : ty, B : [x : tm A] ty ] ty
sup : [ A, B, a : tm A, f : [b : tm (B a)] tm (W A B) ] tm (W A B)
rec : [ A, B,
        C : [w : tm (W A B)] ty,
        c : [ a : tm A,
              f : [b : tm (B a)] tm (W A B),
              h : [b : tm (B a)] tm (C (f b)) ] tm (C (sup A B a f)),
        w : tm (W A B) ] tm (C w)
```

Compute `rank` on `c`'s binding telescope: `a` binds nothing, contributing 1;
`f` and `h` each bind a rank-1 telescope, contributing 2. So `rank Δ_c = 2`, and
`c` contributes `2 + 1 = 3` to `rank Δ_rec`. **`rec` is a third-order operator.**

It is not expressible in Uemura's LF: `c`'s second argument has type
`(b : tm (B a)) → tm (W A B)`, which is `□`, and his product rule (4.2) admits
only `∗` domains.

Two honest caveats, both made by the sources themselves.

- **With `Π` present the example evaporates.** Curry `f` and `h` into single
  `of`-boundaried arguments of `Π`-type and `rec` drops to rank 2. Uemura,
  thesis Rem. 3.2.12: "higher-order variable binding can be performed by a
  combination of first-order variable binding and Π-types." So rank ≥ 3 is
  *forced* only for theories wanting higher-level rules without an internal
  function type — of which `W`-without-`Π` is the standard one.
- Gratzer–Sterling dismiss the other commonly cited example, "fun-split", as
  "strictly isomorphic to one not involving a higher-level judgment".

The proof-theoretic ancestor of all this is **Schroeder-Heister's higher-level
rules** — rules taking rules as premises (4.1).

---

## 4. Comparison

### 4.1 Two knobs

Every framework in the literature fixes both; this one leaves both open — but
not independently, see the end of this subsection.

| | contexts `𝒫` | signature rank | ambient notion |
|---|---|---|---|
| Lawvere | rank 1 | 1 | — |
| Fiore–Mahmoud | rank 1 | 2 | — |
| Arkor–Fiore `Lawₙ` | rank 1 | **n, graded** | — (simply typed) |
| Cartmell GAT | rank 1 | 1 | lex category |
| Uemura; Kaposi–Xie | rank 1 | **2** | CwR; CwF⁺ |
| Gratzer–Sterling | rank 1 | ω, **ungraded** | LCCC |
| **this framework** | **any `𝒫`** | **n, graded** | the chain of 0 |

Arkor–Fiore have the grading without dependency; Uemura and Kaposi have the
dependency and stop at 2; Gratzer–Sterling reach ω but drop the class of display
maps from the definition — and with it, per Bocquet, the categories of algebras.
**This framework is the pushout of the first two and the graded refinement of the
third.**

Attribute that last loss carefully: it is dropping `𝒫`, not reaching rank ω, that
costs the homomorphisms at rank 2 (2.6).

And the two knobs are **coupled**. By 2.6, an order-`n` theory has morphisms of
models only when `𝒯₀^{≤ n−1} ⊆ 𝒫`, so the column pair in the table is not free:
every row above is *on the diagonal*, taking rank-one contexts and stopping at
order 2 — the largest order rank-one contexts support. Going higher means richer
contexts, not just a richer signature. That the whole literature sits on one
diagonal entry is the observation this framework is built to generalise, and the
statement to prove is Q2.

Both gaps are stated as gaps by their authors. Arkor, thesis §4.1.1: "n-th order
algebraic theories for n ∉ {1,2} do not appear to have previously been studied";
§8.1: the inductive construction of `Law_{n+1}` "suggests a fruitful pursuit of
similar understandings for … generalised algebraic theories. That the latter in
particular might be understood this way is suggested by the work of Uemura."
Kaposi–Xie, FSCD 2024 §1: SOGATs allow "second-order (but not general
higher-order) operations".

**The oldest ancestor is proof-theoretic, and neither Arkor nor Kaposi cites
it.** Schroeder-Heister, *Structural Frameworks with Higher-level Rules*
(Habilitationsschrift, 1987), analyses **rules of higher level** — rules taking
rules as premises — which is the rank hierarchy 25 years before Fiore–Mahmoud.
Gratzer–Sterling invoke it, together with Martin-Löf's own logical framework, as
the tradition against which Uemura's one-level stratification is a restriction
(4.5). Any write-up should place it in this lineage paragraph.

### 4.2 Uemura — the bridge

Rank is Arkor–Fiore order on the nose. Writing a telescope as a product of its
entries and an entry as `binding ⇒ boundary`, Def. 3.1 of Arkor–McDermott reads

```
ord (X ⇒ Y) = max (ord X + 1) (ord Y)      ↔   rank (Π_Θ Λ) = max (rank Θ + 1) (rank Λ)
ord (X × Y) = max                          ↔   rank (Θ ⋈ Λ)  = max
ord B = 1  (B a base sort)                 ↔   a slot binding nothing has rank 1
```

And Uemura's `∗`/`□` cut **is** the first step of the chain. His LF has one
product rule and no other (arXiv:1904.04097, Fig. 1):

```
Σ | Γ ⊢ A : ∗     Σ | Γ, x : A ⊢ B : □
──────────────────────────────────────
      Σ | Γ ⊢ (x : A) → B : □
```

Domain representable, conclusion `□`, never `∗`. By 3.2: iterating with
representable domains stays at rank 2 — which is why `□` is closed under his rule
— and rank 3 needs a `□` domain, which the rule forbids. Hence

```
∗  =  𝒫 = 𝒯₀^{≤1}          □  =  𝒯₀^{≤2}
```

His thesis Rem. 4.1.1 says the same from the syntax side: "we are not allowed to
write a higher-order operator like `((A → B) → C) ⇒ D`" — that operator is order
3.

**The sharpest point.** Uemura's Rem. 3.2.11 — "we do not require that
representable maps in a CwR are closed under pushforwards" — is, in our terms,
exactly the jump `1 ↦ 2`: `Π_Θ Λ` for `Θ ∈ 𝒫` has rank `max(2, rank Λ)`, landing
in `𝒯₀` but leaving `𝒫`. He states it as a restriction he must live with; here it
is a computation.

His stated reasons for stopping (thesis Rem. 3.2.12) are that "variable binding
in a type theory only occurs at the 'first-order' level", and technically that
pushforward along a representable map of discrete fibrations is itself a pullback
(Prop. 3.21), which is what makes `Mod_T` compactly generated.

**`(Ctx, 𝒫)` is a CwR**, conditionally — checked axiom by axiom in
Proposition 1.3, whose only gap is exponentiability,
Conjecture 3.2 at the rank of `𝒫`. Note he demands exponentiability of `R` alone
and never of the general displays, so only the weakest case of 3.2 is needed.

Two further disanalogies, both in our favour:

- **Level.** For Uemura a theory *is* an entire CwR, built from a signature as
  `Σ ↦ R(Σ)`. Here a theory is an **object** of one fixed `Ctx`, and the bridge
  is the slice: `Ξ ↦ Ctx_{(Ξ,𝒫)}` is the analogue of `Σ ↦ R(Σ)`.
- **He pays a coherence cost we do not.** His Theorem 5.17 (freeness of `R(Σ)`)
  is proved using **Hofmann's splitting technique**, with an auxiliary pullback
  `R → U` over `(C/−)_r → (C/−)` separating representable from general types.
  CwR is a class-of-maps notion, hence non-split, so the universal property
  cannot be stated without reintroducing a splitting. Here `act_id` and
  `act_comp` are strict, `𝒯₀` is an honest presheaf, and that auxiliary pullback
  of his *is* the inclusion `𝒫 ↪ 𝒯₀` that 1.2 hands over for free. See 4.6.

His declaration cases (thesis §4.8.1) match our boundary constructors one for
one, which is strong evidence that 2.2's clauses are the right ones:

| Uemura | effect on `Cl(T)` | here |
|---|---|---|
| `⇒ Type` | freely adjoin a morphism | `sort`, head not in `R` |
| `⇒ type` | freely adjoin a **representable** map | `sort`, head in `R` |
| `⇒ K` | freely adjoin a section | `of S` |
| axiom `Φ ⇒ P` | freely **invert a monomorphism** | `eq l r`, monic by 13.3 |
| `⇒ Prop` / `⇒ prop` | adjoin a (representable) monomorphism | **no counterpart** |

Row four: taking the subobject as the new base is the same operation as inverting
the mono once one passes to the slice, so 13.3 is the exact syntactic form of his
equational clause. Row five is a genuine gap — he added `Prop`/`prop`,
proof-irrelevant judgment forms, for cubical cofibrations (Rem. 4.2.7). If those
are ever wanted here, that is a **fourth `Bd` constructor** parallel to `sort`,
not something to be arranged at the `𝒫` level.

### 4.3 Kaposi

**How signatures work in Kaposi's line of work**, since the encoding is what
makes their statements look opaque from outside. There is a type theory `ToS⁺`,
the *theory of signatures*, and:

```
a signature                 IS   a closed type  Ω : Ty ⋄  in the syntax of ToS⁺
giving signatures meaning   IS   choosing a model of ToS⁺
a model of the signature Ω  IS   an element of ⟦Ω⟧ in that model
```

The third line is the trick. `Ω` is an iterated `Σ`, one component per
declaration, with `Eq`-types for the equations; so an element of it is precisely
a tuple interpreting every symbol together with a proof of every equation.
"Model of `Ω`" and "inhabitant of `⟦Ω⟧`" are the same thing by construction.
(Kaposi–Kovács took signatures to be *contexts*; Kaposi–Xie switched to closed
types, which is the same information since `ToS⁺` has `⊤` and `Σ`. Ours are
ambients, i.e. closest to contexts.)

`ToS⁺` has two universes: `U` of sorts, and `U⁺ ⊆ U` of "the sub-universe of
sorts over which variables may be bound". **That is our `𝒫 ⊆ 𝒯₀^{≤2}` cut**, and
it is where `𝒞` enters their semantics: their model of `ToS⁺` is `PSh(𝒞)`,
interpreting `U` by dependent presheaves and `U⁺` by the **locally
representable** ones (Problem 17) — Definition 2.1 here, and their source for it.

So their Def. 18, unwound, is our 2.1 and 2.2: *a category `𝒞` with a terminal
object, plus an interpretation of every symbol in `PSh(𝒞)` satisfying every
equation, with the bindable sorts locally representable.* The semantic version
with a universal property is Bocquet's thesis §5.2 (`T ↦ T^fo` left adjoint to
`psh_–(–)`).

**Why their *naive* semantics and not their refinements.** They give three
notions — naive (Def. 18), *direct* (Def. 21, interpreting in `PSh(PSh(𝒞))`),
and the *GAT translation* (Constr. 26) — and prove all three isomorphic:
Thm. 22 (naive ≅ direct), Thm. 27 (direct ≅ GAT). "Naive" therefore names an
overhead in the **output signature**, not a defect in the notion of model: their
naive translation of untyped `λ` emits operations that are uncurried, carry
spurious `𝒞(I, ⋄)` arguments, and make `app` quantify over an extra object of
`𝒞` per argument. Their aim is a *readable* first-order GAT — "the GAT
descriptions that we obtain … do not contain occurrences of Yoneda as in usual
presheaf function spaces" — so they work to remove it.

We emit no signature. `Ctx`, `𝒯₀` and `q` already exist and 2.2 is written
against them directly, so the refinements buy nothing and the naive form is the
right one to imitate.

The construction to reuse rather than reprove is 2.5's; the argument that makes
`𝒫` indispensable is theirs, and is 2.6.

### 4.4 Joyal's clans — and why `Ctx` is a degenerate one

`Ctx` with the `𝒯₀`-displays satisfies Joyal's axioms (Def. 1.1.1): terminal
`𝟙`; base change 10.4; composition 11.4; and `Ξ ⟶ 𝟙` is `p 𝟙 Ξ` with `𝟙 ⋈ Ξ = Ξ`
definitionally, so **every object is fibrant** `[routine]`. Worth noting because
of North's observation (MSCS 29(9), Rem. 2.4): a display-map category modelling
**Σ** is precisely a clan, and one modelling **Σ and Π** is precisely a π-clan.
Read backwards, **11.4 is not an analogy with Σ-types, it is Σ-types**, and 3.2
is Π-types.

But the clan structure is degenerate, and it is worth knowing whose theorem that
is.

> **Proposition 4.4** `[routine]`**.** Every morphism of `Ctx` is a display.
>
> `f : X ⟶ Y` factors as `X ⟶ X × Y ⟶ Y` with the first map the base change of
> `Δ_Y` along `f × 1`, so `f` is a display as soon as `Δ_Y` is. By 1.3(a) `Ctx`
> has the finite limits this uses, and `Γ ≅ (Γ × Γ) ⋈ E(π₁, π₂)` over `Γ × Γ`
> identifies `Δ_Γ` with a projection. ∎

**Is `Ctx` cartesian?** In both senses, and they differ — a trap, since this note
quotes authors on either side of the convention. Joyal (Def. 1.1.2) calls a
category with finite **products** cartesian; Uemura (Convention 2.1.10) reserves
it for finite **limits**. By 1.3(a), `Ctx` has both: `𝟙` and `Γ ⋈ ⇑Δ` for the first,
and `Ξ ⋈ E(σ,θ)` for the second. Granting 3.2 it is moreover locally cartesian
closed — every map being a display, dependent products exist along all of them —
hence cartesian closed. Every universal property here holds **up to `∼`**, the
hom-setoids of 9.3 being where uniqueness is asserted; that is the right reading
for a setoid-enriched category and is why §9 is setoid-first (4.6).

The condition "every `δ(φ) : X → X ×_I X` is a display" is Jacobs'
**`(strong equality)`** (*CLTT*, Def. 10.4.1), the exact parallel of
`(strong sum)` = closure under composition. The collapse is Taylor, *PFM*,
Prop. 8.3.4:

> If all product projections and pullback diagonals are displays, then **every**
> map is (isomorphic to) a composite of displays, and `C` has all finite limits.

with Rem. 8.3.5 giving our case: "the classifying category of a generalised
algebraic theory has all finite limits (and all of its maps are isomorphic to
displays) **iff the theory has all equality types**." Object-wise the property is
called **separated** (Ahrens–Lumsdaine–North Thm. 36: the right adjoint to
`Lex ↪ Clan` is the full subcategory of separated objects). Gratzer–Sterling put
the dividing line plainly (§1.1·2):

> while a clan need not be finitely complete (the diagonal is not a display map
> except in extensional type theories), unrestricted pullback in representable
> map categories corresponds to the fact that type theory has judgmental
> equality.

Two consequences:

- Do **not** look for the semantic counterpart of equational slots in a subclass
  of *equational displays* (15.1, second bullet). That subclass is closed under
  the argument above and drags everything with it. The counterpart of `eq` is
  that the **target is lex** — which is exactly why CwRs are finitely complete
  and clans are not.
- `𝒯₀` **as a class of maps** carries nothing; `𝒯₀` **as a presheaf** carries a
  great deal, since different representable natural transformations on one
  category induce the same class of display maps (Awodey, Rem. 25). §13 is
  strictly more than a clan structure, and the chain of 0 lives entirely on the
  presheaf side.
- **Conversion in `Ctx` is undecidable** `[conjecture]`. Gratzer–Sterling
  (§1.2·2): "judgmental equality can only be decidable relative to a class of
  display maps that **does not include all diagonals**", citing
  Castellan–Clairambault–Dybjer's undecidability of equality in the free LCCC.
  But 4.4 makes every diagonal in `Ctx` a display, so granting 3.2 `Ctx` is an
  LCCC and the result applies. Decidability can only be expected relative to a
  `𝒫` excluding diagonals — i.e. relative to a theory in the sense of 1.4.

  This closes the loop on §15.2's closing question. The rank-1 restriction is
  mathematical — representability — **and** the practical consequence is
  downstream of it: `𝒫` is not a convenience for a future implementation, it is
  what stands between the implementation and an undecidable conversion problem.

So, ranked by informativeness:

```
Ctx is lex                            true; forgets everything
(Ctx, 𝒯₀-as-class) is a clan          true; degenerate by 4.4
(Ctx, 𝒫) is a CwR                     true (4.2, conditionally); the right bridge to Uemura
q and every q|_𝒫 are natural models   true; strictly more than all of the above
```

**CwR is the correct bridge, not the correct description.**

### 4.5 Gratzer–Sterling — rank ω without the grading

*Syntactic categories for dependent type theory: sketching and adequacy*
(arXiv:2012.10783). Two contributions.

**Sketches.** Following Kinoshita–Power–Takeyama, present syntactic categories by
generators and relations in a doctrine:

```
sketches in the doctrine of finite-product categories  present  algebraic theories
                             finite-limit categories   present  essentially algebraic theories
                             LCCCs                     present  dependent type theories
```

Their "walking type theory" is one generating morphism `$ : U̇ ⟶ U`; `Π` is a
square marked cartesian plus a marking making the left leg the polynomial
`P_$($)`. Sketches declare all generators up front and *mark* which formal
objects must later become real limits; a logical framework instead interleaves
generators, relations and derived structure (their §1.3).

**Adequacy (§5), the real content.** Let `Σ` be a signature in Uemura's LF,
generating a syntactic RMC `T`; forget the `∗`/`□` distinction to get a syntactic
LCCC `E` and a comparison `ℓ : T ⟶ E`.

> **Theorem (Gratzer–Sterling §5.3).** `ℓ` is fully faithful.

By Artin gluing: `N : E → Pr(T)`, `N(E) : X ↦ Hom_E(ℓX, E)`; glue to `gl : G → E`;
build a section `L : E → G` extending the Yoneda model `M : T → G`; `gl ∘ L ≅ id`
makes `L` faithful, and `M = L ∘ ℓ` transfers fullness and faithfulness to `ℓ`.
Same machinery as the sconing of 2.5 — one gluing infrastructure serves both.

So **rank 2 ↪ rank ω is conservative**, which is their licence to drop the
stratification entirely.

**Where this framework differs.** They drop it; we grade it. Their §1.1·3 is the
argument *for* rank, and 3.4 is their example:

> The fact that dependent products need exist only along representable maps
> corresponds to the way that dependent type theory is conventionally presented
> using **hypothetical judgments of one level only**. This realistic
> stratification, however, is not at all forced: Martin-Löf himself has promoted
> a presentation … that supports **hypothetical judgments of arbitrary level**.

But dropping the stratification is what Bocquet objects to (thesis §1.2.3):
unstratified higher-order theories "do not really have categories of algebras".
The chain of 0 is the third option neither has taken — reach rank ω *and* keep
the grading — and Q1 is the theorem that would justify it, generalising exactly
their §5.

Two further points of contact are recorded elsewhere: their post-facto argument
for separating contexts from the theory is 1.4, and their remark on decidability
is the last bullet of 4.4.

### 4.6 Split, not pseudo

`𝒯₀` is an honest presheaf: `act_id` and `act_comp` hold strictly, so 13.2's
natural model is **split**. Clans and display-map categories are the non-split
side (`CompCat_repl`); CwFs, CwAs and natural models the split side
(`CompCat_disc ≃ CompCat_{full,spl}`), related only by a splitting whose unit is
an equivalence but never an isomorphism (Lumsdaine–Warren §2.2; Streicher,
*Fibred Categories à la Jean Bénabou*, Thm. 3.1). The setoid-first discipline of
§9 keeps us on the split side, where syntax has to live. **Clan language is for
targets, not for `Ctx`** — and it is why 4.2's second disanalogy holds.

---

## 5. MLTT

`Ξ_MLTT` declares `ty : sort`, `tm : [A : ty] sort`, a former and eliminator per
connective, and the equations — the shape already built for `Σ` in
`examples/dependent/ML-Sigma.lean`. It is a theory of **order 2**, i.e.
`rank Ξ_MLTT = 3`.

```
𝒫_MLTT  =  telescopes whose every entry is
             rank 1                       binds nothing
             of-boundaried                no sorts, no hypothetical equations
             with sort in R = { tm A }    no type variables
```

Written out, with the four exclusions attributed one to a filter, in 1.5.

The first two are §15.2's; the third is 1.5's. All three are `≈`-closed and
`⋆`-stable over `Ctx/Ξ_MLTT`, so 1.2 gives the natural model and 1.4 gives the
theory `(Ξ_MLTT, 𝒫_MLTT)`.

Restricting further to **single**-entry telescopes returns the ordinary CwF:

```
Ty Γ    =  { S : ℰ₀ Γ  //  Γ ⊢ boundaryOf S ≈ .sort,  S ∈ R }
Tm Γ S  =  { e : ℰ₀ Γ  //  Γ ⊢ e : .of S }
```

with comprehension `Γ ⋈ [x : of S]`. So 12.4 resolves: `boundaryOf` is not
representable on all of `ℬ₀`, but its restriction to `of`-boundaries over `R` is,
and it *is* `q` cut down by 1.2. 12.4 makes that conditional on the carrier
supplying a one-slot, nothing-binding arity; the list carrier does — it is
`ofList [.mk []]` — so the condition is discharged and the recovery is
unconditional. **The ordinary natural model of MLTT is a link
in the chain**; the telescopic one over `𝒫_MLTT` is another, on the same category
of contexts.

Which answers §15.2's closing question: the rank-1 restriction is **not** a
practical matter for a future implementation. It is the representable/display
distinction Uemura's framework is built on, and here it is one instance of a
uniform mechanism.

---

## 6. Status

| # | statement | status |
|---|---|---|
| 1.2 | sub-presheaves are natural models | `[routine]` |
| 1.3(a) | `Ctx` has finite limits | `[routine]` |
| 1.3(b) | `𝒟_𝒫` has identities, composition, pullback-stability | `[routine]` |
| 1.3(d) | slices of CwRs are CwRs; hence `Ctx_{(Ξ,𝒫)}` | `[routine]` |
| 1.5 | the four filters are `≈`-closed, `⋆`-stable, `⋈`-closed | `[routine]` |
| 3.1 | `rank` is `≈`- and `⋆`-invariant; `rank (Θ ⋈ Λ) = max` | `[routine]` |
| 4.4 | every morphism of `Ctx` is a display | `[routine]`, given 1.3(a) |
| 4.4 | `Ctx` is a clan | `[routine]` |
| **3.2** | **`Π_Θ Λ` exists in `𝒯₀` and is right adjoint to base change** | **`[conjecture]` — the risk gate; arities checked in 1.3(c)** |
| 3.2 | the closure description of each `𝒯₀^{≤n}` | `[conjecture]`, given 3.2 |
| 4.2 | `∗ = 𝒯₀^{≤1}`, `□ = 𝒯₀^{≤2}` | `[conjecture]`, given 3.2 |
| 1.3(c) | arrows of `𝒟_𝒫` are exponentiable — hence `(Ctx, 𝒟_𝒫)` a CwR | `[conjecture]`, = 3.2; construction given, two obligations left |
| 2.2 | the interpretation is well defined | `[conjecture]` |
| 2.4 | soundness and initiality | `[conjecture]`, expected easy |
| 2.5 | the four translations from one recursion; `–ᴰ`/`–ˢ` by sconing | `[conjecture]` |
| 3.4 | `W`-without-`Π` has `rank Δ_rec = 3`, and is not a Uemura theory | `[routine]`, given 3.1 |
| 4.4 | conversion in `Ctx` is undecidable | `[conjecture]`, given 3.2 |
| 2.6.1 | Definition 2.6 unfolds to the usual monoid homomorphism | `[routine]` |
| 2.6.4 | morphisms compose; agreement with Uemura's Def. 4.14 | `[conjecture]` |
| 2.6.2 | order-`n` theories have morphisms of models iff `𝒯₀^{≤n−1} ⊆ 𝒫` | `[conjecture]` |
| 3.2 | `prefix` is `List.map`; its `before`/`after`/`factor` laws | `[routine]` |
| **Q1** | **`𝒯₀^{≤n} ↪ 𝒯₀^{≤n+1}` is fully faithful** | `[open]` — **two precedents** |
| Q2 | models above rank 2 live over the rank-`n` category, not over `Set` | `[open]` — one precedent |
| Q3 | the ∞-analogue | `[open]` |

Nothing above rewrites §§1–13; all of it sits on top.

---

## 7. What to prove, in order

1. **3.2** — `Π_Θ Λ` and its adjointness. The one genuinely new construction on
   the syntax side, and it decides whether the chain is a filtration *of*
   something. **Do this first**; if it fails, §§3–4 need rethinking. Its
   arity-level obligation is discharged by the list carrier (3.2(1)), so start at
   the decoration, 3.2(2), which is where the work is.
2. **1.2** — the sub-presheaf lemma. Short, and discharges most of §15.2.
3. **3.1** — `rank` and its invariance. Short.
4. **4.4** — `Ctx` lex, `Δ_Γ` a display. Needs 13.3's uniqueness half and
   `σ ⋆ ⇑Δ = ⇑Δ`.
5. **2.2** — the interpretation, in `Set` first (`𝒞 = 1`), then `PSh(𝒞)`.
6. **2.4** — soundness, then initiality.
7. **2.5** — the `flCwF`-valued instance, and sconing.

Then the open questions, the first of which is no longer speculation.

- **Q1. Conservativity of the chain.** Is `𝒯₀^{≤n} ↪ 𝒯₀^{≤n+1}` fully faithful?
  **Both neighbours have proved their own case**, which fixes the proof shape:
  Gratzer–Sterling do `rank 2 ↪ rank ω` by Artin gluing along the nerve (§5.3,
  and 4.5 here); Arkor–McDermott do the simply-typed graded version (Prop. 4.5,
  "each order is a faithful conservative extension of the previous"). This
  framework is where those become one theorem, and it is what licenses using the
  chain rather than collapsing it. Do this before Q2 — it is the cheaper of the
  two and the gluing infrastructure is shared with 2.5.
- **Q2. Do order-`n` theories have morphisms of models over rank-(n−1)
  contexts?** By 2.6 the obstruction is concrete and so is the proposed remedy:
  the `?` in `α (lam_M f) = lam_N (α ∘ f ∘ ?)` returns exactly when a `Π` is
  taken along a telescope outside `𝒫`, and is absorbed by `F` when it is inside.
  So the conjecture is `𝒯₀^{≤ n−1} ⊆ 𝒫` suffices — climbing `𝒫` and the rank
  together, one step apart. **Settling this decides whether the chain is a chain
  of categories of models or only of classes of them**, and it is the question
  the whole note turns on. Uemura's Beck–Chevalley clause is imposed only at representable
  arrows and says nothing there; his compact generation of `Mod_T` likewise rests
  on pushforward along a representable being a pullback (Prop. 3.21). Bocquet's
  "higher-order theories do not really have categories of algebras" (thesis
  §1.2.3) is the same observation.

  **The likely answer is not to patch homomorphisms but to move the base.** The
  simply-typed precedent says exactly that: `Law_{n+1}(S)` is a category of monads
  **on `Law_n(S)`** (Arkor–McDermott Thm. 8.2), with a coreflection
  `Law_n ⇄ Law_{n+1}` (Thm. 5.3 / Arkor Cor. 4.6.10). So models of a rank-(n+1)
  theory should live over the rank-`n` category rather than over `Set` — meaning
  the *elementwise* formulation 2.2 is simply the wrong one above rank 2, while
  the *functorial* formulation 2.4 is not. The dependent analogue would be **the
  main theorem**.

  This is also why the λ-calculus is modelled by cartesian closed *categories*
  and not by sets-with-operations: same contravariance, same fix.
- **Q3.** Is the ∞-analogue the same statement? Uemura's thesis Ch. 6 has
  ∞-CwRs; §9's setoid-first discipline was chosen so `≈` never becomes a
  quotient, which is precisely what would let it become a path. Worth deciding
  before §9 is formalized, not after.

---

## 8. References

```
Arkor & McDermott     Higher-order algebraic theories                  Def. 3.1, Thm. 3.6, Thm. 5.3
Arkor                 Monadic and Higher-Order Structure, Cambridge    Ch. 4; §4.1.1, §8.1 (the gap)
Fiore & Mahmoud       Second-order algebraic theories                  arXiv:1308.5409, Def. 4.1
Joyal                 Notes on clans and tribes                        arXiv:1710.10238, Def. 1.1.1, 2.4.1
North                 Identity types and WFS in Cauchy complete cats   MSCS 29(9), Rem. 2.4
Taylor                Practical Foundations of Mathematics             §8.3, Prop. 8.3.4, Rem. 8.3.5
Jacobs                Categorical Logic and Type Theory                Def. 10.4.1 (strong equality)
Ahrens, Lumsdaine,    Comparing semantic frameworks for                arXiv:2412.19946
  North                 dependently-sorted algebraic theories            Thm. 31, 36, Prop. 43
Awodey                Natural models of homotopy type theory           MSCS 28(2), Def. 1/3, Prop. 2, Rem. 25
Uemura                A general framework for the semantics of         arXiv:1904.04097
                        type theory                                      Def. 4.1, 4.2, 4.5, 6.7; Fig. 1; Thm. 5.17
Uemura                Abstract and Concrete Type Theories, thesis      Rem. 3.2.10-12, 4.1.1, 4.2.7; §4.8.1
Schroeder-Heister     Structural Frameworks with Higher-level Rules    Habilitationsschrift, 1987
Gratzer & Sterling    Syntactic categories for dependent type theory:  arXiv:2012.10783
                        sketching and adequacy                           §1.1, §1.2, §1.3, §4, Thm. §5.3
Kinoshita, Power,     Sketches                                        cited by Gratzer-Sterling for
  & Takeyama                                                             the 2-monadic sketch machinery
Castellan,            Undecidability of equality in the free           LMCS 13(4), 2017
  Clairambault,         locally Cartesian closed category
  & Dybjer
Kaposi & Xie          Second-order GATs: signatures and                FSCD 2024, Def. 12, 13, 18
                        first-order semantics                            Problem 17, Constr. 26, Thm. 27
Kaposi & Kovács       Signatures and induction principles for HIITs    LMCS 16(1:10); POPL 2019 §7.3
Kovács                Type-Theoretic Signatures…, thesis ELTE          arXiv:2302.08837, Thms. 1-2
Bocquet, Kaposi,      For the metatheory of type theory,               FSCD 2023, Constr. 11, Def. 12
  Sattler               internal sconing is enough
Bocquet               Relative induction principles for SOGATs, thesis §1.2.3, §5.2, Ch. 6
Lumsdaine & Warren    The local universes model                        ACM TOCL 16(3), §2.2, Thm. 3.4.1
Streicher             Fibred Categories à la Jean Bénabou              arXiv:1801.02927, Thm. 3.1
```
