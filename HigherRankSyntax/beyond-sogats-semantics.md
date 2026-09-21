# Beyond SOGATs

Whether the framework contains a theory that genuinely lies beyond second-order
generalised algebraic theories.

Marks: `[proved]`, `[routine]`, `[open]`.

---

## 0. The question

A higher-rank theory is a pair `(Ξ, 𝒫)`: a well-formed ambient `Ξ` together with
a subpresheaf `𝒫` over `Ctx / Ξ` naming the context extensions a model must
represent. For a small category `𝒞`,

```text
Mod_𝒞(Ξ, 𝒫)  :=  { M : 1 ⟶ J_𝒞(Ξ)  |  every 𝒫-display is locally representable }
```

a **set** (`semantics.md`, Definition 3.1). We ask whether some `(Ξ, 𝒫)` is not a
SOGAT in any reasonable sense.

---

## 1. How the comparison must be framed

**Definition 1.1 (Kaposi–Xie, Definition 18).** For a SOGAT signature `Ω : Ty ⋄`
of `ToS⁺`, a model of `Ω` in `PSh(𝒞)` is an element of `Tm_{PSh(𝒞)} ⋄ ⟦Ω⟧`. Write

```text
Mod_𝒞(Ω)  :=  Tm_{PSh(𝒞)} ⋄ ⟦Ω⟧
```

overloading the `Mod_𝒞(−)` of §0: on a pair `(Ξ, 𝒫)` it is Definition 3.1 of
`semantics.md`, on a `ToS⁺` signature it is this. The argument disambiguates.

**Definition 1.2 (Kaposi–Xie, Construction 26).** The *GAT translation* of `Ω` is
the `ToS` signature

```text
Σ Cat⋄ λ𝒞. ⟦Ω⟧_E(𝒞) ⋄_D(𝒞) tt              D := PSh(𝒞),  E := PSh(D)
```

**Remark 1.3.** Their Theorems 22 and 27 state that the naive, direct and GAT
semantics "result in isomorphic notions of models". The conclusion of the proof
of Theorem 27 is

```text
⟦Ω⟧_E ⋄_D ★  ≅  α^*⟦Ω⟧_{E′}[β_⋄] ⋄_D ★  =  ⟦Ω⟧_{E′} ⋄_{D′} ★
```

an isomorphism of **types**, not an equivalence of categories. The comparison is
built from a strict `CwF⁺`-morphism `α`, bijective on `Ty`, `Ty⁺`, `Tm`, and a
family `β` defined by induction on the syntax of `ToS⁺`.

**Remark 1.4.** Consequently the *category* of models of a SOGAT is not compared
but **imported**: it is the category of models of the translated GAT. Kaposi–Xie
say so immediately after Construction 26 — "we can reuse the semantics of GATs
for any SOGAT, e.g. there is a category of models with an initial object, notions
of dependent/displayed models, sections, induction is equivalent to initiality,
free models, cofree models". Morphisms of models of a SOGAT are nowhere
characterised on the naive or direct side.

**Remark 1.5.** Hence "the model categories are inequivalent" is not a statement
one can aim for: on the SOGAT side there is no model category prior to the
translation, and on the higher-rank side `semantics.md` Definition 3.2 is `[open]`
for the same reason. The statement to aim for is instead

> there are higher-rank theories admitting no GAT translation at all.

This is stronger, and it is the only shape in which both sides are the same kind
of object.

---

## 2. First-order presentations

Definition 1.2 has a shape: bases, then structure over a base. Definition 2.1
abstracts it.

**Definition 2.1.** A **first-order presentation** of `(Ξ, 𝒫)` consists of

1. a `ToS` signature `B` extending `Cat⋄` — the *bases*;
2. a type `S : Ty (⋄ ▷ B)` in the first-order syntax of `ToS`, so that
   `Σ B λ𝒞. S(𝒞)` is a `ToS` signature;
3. for each `B`-model `𝒞`, a bijection `θ_𝒞 : S(𝒞) ≅ Mod_𝒞(Ξ, 𝒫)`;
4. for each `B`-morphism `κ : 𝒞 ⟶ 𝒟`, the equality `θ_𝒞 ∘ S(κ) = κ^* ∘ θ_𝒟`,
   where `κ^*` is restriction of models along `κ`.

The **category of models** is then `Mod(Ξ, 𝒫) := Mod(Σ B λ𝒞. S(𝒞))`.

**Remark 2.2 (provenance).** (1) and (2) are the shape of Construction 26, with
`B = Cat⋄`. (3) is Theorems 22 and 27. Only (4) is added. It is a property of
their construction rather than an extra demand: `α` and `β` are defined by
induction on the syntax of `ToS⁺`, hence commute with substitution, and base
change in `Σ Cat⋄` is substitution. `[open]` — argued from the shape of the
induction, not verified against it.

**Remark 2.3.** (4) is necessary. Without it the notion is vacuous: given any
bijection of model-types one may transport the category structure across it, and
(1)–(3) cannot distinguish that from a presentation.

**Remark 2.4.** (4) asserts nothing about `(Ξ, 𝒫)`. Since `S` is a first-order
expression over `B`, its action `S(κ)` exists automatically; (4) only requires
that the presentation present the models *as indexed*. In particular (4) holds as
soon as `κ ↦ κ^*` is functorial at all. The asymmetry is the content: the left
side of (4) is functorial by construction, the right side may not be.

**Remark 2.4a.** With `B := Cat⋄`, Definition 2.1 *is* Definition 1.2 together
with Theorems 22/27 and clause (4). That it recovers Construction 26 on the
theories already second-order is Corollary 3.4 of `beyond-sogats-syntactic.md`,
which also shows the two classes differ. Note also that (3) determines the
objects of `Mod(Ξ,𝒫)` but not its morphisms: those come from `B`, so distinct
presentations may give distinct categories.

**Remark 2.5.** `B` is existentially quantified; a presentation may choose richer
bases. Enlarging `B` does not supply representability of a model's binder
domains, since `B` constrains the base and not the interpretation of `A`.
Requiring `B` to extend `Cat⋄` guarantees that `B`-models are categories and that
free `B`-algebras supply the base morphisms used in §3.

---

## 3. A theory with no first-order presentation

**Notation 3.1.** Put

```text
Θ₁ := [x : of A]                        rank 1
Θ₂ := [f : Bind(Θ₁, of A)]              rank 2
Θ₃ := [h : Bind(Θ₂, of A)]              rank 3
Ξ  := [A : sort,  Z : Bind(Θ₃, of A)]   rank 4,  order 3
```

so `Z : ((A → A) → A) → A`. For a model with sort `A`,

```text
⟦Θ₁⟧ = A        ⟦Θ₂⟧ = Π_A A        ⟦Θ₃⟧ = Π_{Π_A A} A
⟦Z⟧ ∈ Sect(Π_{⟦Θ₃⟧} A)
```

**Lemma 3.2.** Let `ι : 𝒞 ⟶ 𝒟` be a functor and `X ∈ PSh(𝒟)`. The canonical
comparison `ι^*(Π_X X) ⟶ Π_{ι^*X}(ι^*X)` is an isomorphism when `X` is locally
representable and `ι` preserves `− ⊲ X`, and is not in general.

*Proof sketch.* If `X` is locally representable then `Π_X Y = Y(− ⊲ X)`, and the
two sides at `I` are `Y(ι I ⊲ X)` and `Y(ι(I ⊲ ι^*X))`, equal precisely when `ι`
preserves the extension. For the failure, let `𝒟` have objects `0, 1` and one
non-identity arrow `0 → 1`, and let `ι : 1 ⟶ 𝒟` pick `1`. Then `よ1` is terminal,
so `(Π_X X)(1) = Nat(X, X)`, whereas `Π_{ι^*X}(ι^*X) = X(1)^{X(1)}`. A natural
transformation must also act at `0`, so the comparison is injective and not
surjective. ∎

**Proposition 3.3.** Let `Ξ` be as in 3.1 and let `𝒫` not contain `Θ₂`. Then
`(Ξ, 𝒫)` has no first-order presentation. `[open]`

*Proof sketch.* Suppose `(B, S, θ)` were one. `B` extends `Cat⋄`, so `Mod(B)` has
free algebras, and for a `B`-model `𝒞` the unit of the free extension by one
`A`-generator is a `B`-morphism `κ : 𝒞 ⟶ 𝒞[x : A]`. Let `N ∈ Mod_{𝒞[x:A]}(Ξ, 𝒫)`.
Clause (4) forces `κ^*` to commute with `S(κ)`, hence with the interpretation of
`Z`'s binder domain `⟦Θ₃⟧ = Π_{Π_A A} A`. Since `Θ₂ ∉ 𝒫`, the sort `Π_A A` is not
required locally representable, so Lemma 3.2 does not apply and the comparison
fails: the fresh object contributes natural transformations that `κ^*⟦Θ₃⟧_N` and
`⟦Θ₃⟧_{κ^*N}` do not share. Hence no such `θ_𝒞` exists. ∎

**Remark 3.4.** Two gaps. That the free `B`-extension by an `A`-generator is the
base morphism adjoining an object, uniformly in `B`, is asserted and not proved.
And Lemma 3.2's failure instance must be transported to the specific `κ` above.
Both are calculations; neither requires new theory. `[open]`

---

## 4. Theories that always have one

**Construction 4.1 (reification).** Let `z` be a slot of `Ξ` whose binding `Θ`
has rank `≥ 2`, and let `Ψ` be an innermost entry of `Θ` of the form
`Bind(Ψ', b)` with `rank Ψ' = 1`. Adjoin

```text
F   : sort
abs : Bind([g : Bind(Ψ', b)], of F)
app : Bind([p : of F] ⋈ Ψ', b)
      app (abs g) = g          abs (app p) = p
```

and replace the entry `Ψ` of `Θ` by `[p : of F]`. Write `R(Ξ)` for the result.

**Lemma 4.2.** `rank R(Ξ) = rank Ξ − 1`, and in any model in which `⟦Ψ⟧` is
locally representable, the two equations make `⟦F⟧ ≅ ⟦Ψ⟧`. `[routine]`

**Proposition 4.3.** Let `𝒫` contain every binding telescope of `Ξ`. Then
`(Ξ, 𝒫)` has a first-order presentation. `[open]`

*Proof sketch.* Induct on `rank Ξ`. If `rank Ξ ≤ 3` then `Ξ` is a SOGAT signature
and Definition 1.2 applies, with (4) by Remark 2.2. Otherwise apply 4.1 at a slot
of maximal rank. By 4.2 the rank drops, and `𝒫` being full supplies the local
representability that makes `F` a legal declared sort — `U⁺` requires it. The
two theories have the same models: from a model of `(Ξ, 𝒫)` take `⟦F⟧ := ⟦Ψ⟧`
with `abs`, `app` identities; conversely transport along `⟦F⟧ ≅ ⟦Ψ⟧`. The
bijection commutes with restriction because both sides are computed by
reindexing, so (4) is preserved. ∎

**Remark 4.4.** So rank alone is never the obstruction: with `𝒫` full every
finite-rank theory is a SOGAT up to first-order presentation, and the reduction
is Construction 26 continued upward. What separates is `𝒫`.

---

## 5. A natural instance

Worked examples are collected in `beyond-sogats-examples.md`: λ-syntax with a
case operator (whose model is verified, and whose binder is shown non-finitary,
supplying the input to Proposition 3.3), Brouwer ordinals, and large elimination.

---

## References

- Kaposi and Xie,
  [*Second-Order Generalised Algebraic Theories: Signatures and First-Order Semantics*](https://doi.org/10.4230/LIPIcs.FSCD.2024.10):
  Definition 18, Definition 21, Problem 24, Construction 26, Theorems 22 and 27.
- Uemura,
  [*A General Framework for the Semantics of Type Theory*](https://doi.org/10.1017/S0960129523000208):
  Remark 4.1.1 of the thesis for the exclusion of `((A → B) → C) ⇒ D`.
