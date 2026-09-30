# Initiality of positive theories: formalization plan (rough)

**Goal.** For a positive theory `T` and every model `N` of `T`, exactly one morphism
from the term model of `T` to `N`, as a `def`:

```lean
def Theory.initial (T : Theory) (hT : T.Positive) (N : T.Model) :
    Unique (Theory.Model.Hom (T.termModel hT) N)
```

Models live over small categories with chosen extensions, and morphisms preserve
them strictly. `Model.Hom` is heterogeneous in the universe of the base, since the
base of the term model lives in `Type`.

Marks: `[settled]` decided; `[paper]` argued on paper, not formalized; `[open]`.
Open design points are settled as they arise.

---

## 0. Settled

```text
theory       a signature Ξ : Ctx, and admissible entries: a predicate on Ctx.model
             types over objects of Ctx/Ξ, stable under substitution            [settled]
positivity   PositiveEntry, PositiveBinding, Positive: inductive on
             Ctx.model types                                                   [settled]
model        𝒞 small, chosen 1, a point M : 1 ⟶ J_𝒞 Ξ, chosen extensions by
             admissible entries at the points of Ξ ▷ c, c a chain of
             positive entries                                                  [settled]
morphism     F : 𝒞 ⥤ 𝒟 preserving 1 and the chosen extensions strictly, and
             maps on the sort slots commuting with the operations              [settled]
Mod T is a category                                                            [paper] §4
the condition at sort equations, on Russell universes                          [paper] §4
```

Extensions are required only at points of `Ξ ▷ c` with `c` positive, not at every
object of `Ctx/Ξ` as in semantics.md Def 3.1: a positive theory may admit `El Y` at
`Ξ ▷ [Y : sort]`, and Def 3.1 would then ask every small presheaf to be locally
representable.

---

## 1. Presheaf models of HrS

**Deliverable.** For `𝒞 : Type v` with `[SmallCategory 𝒞]`,

```lean
def PSh (𝒞 : Type v) [SmallCategory 𝒞] : HrS.Structure.{v+2}
def J (𝒞 : Type v) [SmallCategory 𝒞] : HrS.Morphism Ctx.model (PSh 𝒞) :=
  HrS.initialMorphism (PSh 𝒞)
```

Nothing in this pass mentions theories. Independent of everything below; the
largest single item.

### 1.1 Universes

```text
presheaves               obj : 𝒞 → Type (v+1)                 Ob  : Type (v+2)
dependent presheaves     fibres in Type (v+1)                  Ty  : Type (v+2)
substitutions, sections  data in Type (v+1)                    declared in Type (v+2)
universe 𝒰(I)            dependent presheaves over よI with fibres in Type v
```

Presheaves take values one universe up so that `𝒰` is one of them. `HrS.Structure`
puts its four sorts in one universe; substitutions and sections are structures
declared one universe above their fields, as `ULift` is. `HrS.Structure` is not
changed.

### 1.2 Representation

Hand-rolled structures; Mathlib supplies only the base category (and, in §4, the
functors between bases).

```lean
structure Presheaf (𝒞) : obj : 𝒞 → Type w
                         map : (J ⟶ I) → obj I → obj J,      map_id, map_comp
structure DPSh (Γ)     : fam : (I : 𝒞) → Γ.obj I → Type w
                         restrict : (f : J ⟶ I) → Γ.map f γ = γ' → fam I γ → fam J γ'
                         restrict_id, restrict_comp
structure Sub (Δ Γ)    : app : Δ.obj I → Γ.obj I,  naturality        maps from Δ to Γ
structure Section (a)  : app : (γ : Γ.obj I) → a.fam I γ,  naturality
```

A restriction takes its target point as a variable, together with an equation.
Transport between propositionally equal points is `restrict 𝟙 h`, never `▸` on a
fibre, and the functor laws of `DPSh` are homogeneous:

```text
restrict 𝟙 h x = x                         h : Γ.map 𝟙 γ = γ
restrict g h₂ (restrict f h₁ x) = restrict (g ≫ f) h₃ x
```

This is the category of elements, with the equation in the morphism.
Reindexing is precomposition:

```text
a[σ].fam I δ := a.fam I (σ.app δ)        t[σ].app δ := t.app (σ.app δ)
```

### 1.3 Which laws are `rfl`

```text
rfl            comp_assoc, identity_comp, comp_identity, toEmpty_unique
               substTy_identity, substTy_comp, substTm_identity, substTm_comp
               projection_pair, generic_pair (HEq.rfl), pair_eta, pair_comp
               U_subst, El_subst, IdSort_subst, IdElement_subst
propositional  functor laws of extend, 𝒰, El, Bind       map_id, map_comp of Γ; laws of 𝒞
               lam_unlam, unlam_lam                       id_comp; restrict 𝟙
               Bind_subst, lam_subst                      naturality of σ         §1.5
               IdSort_*, IdElement_* other than _subst    proof irrelevance, extensionality
```

With the substitution laws definitional, the casts in the other laws reduce
(definitional proof irrelevance, K-like reduction of `Eq.rec`), and the `HEq` laws
are `HEq.rfl` or `heq_of_eq`. The whole table is to be confirmed by probes before
the bulk is written.

### 1.4 Extension

```text
(Γ.extend a).obj I := Σ γ : Γ.obj I, a.fam I γ        map f ⟨γ, x⟩ := ⟨Γ.map f γ, a.restrict f rfl x⟩
projection a       := ⟨γ, x⟩ ↦ γ
generic a          := ⟨γ, x⟩ ↦ x                     a section of a[projection a]
pair σ t           := δ ↦ ⟨σ.app δ, t.app δ⟩
```

`map_id`, `map_comp` of the extension go through `Sigma.ext` and a lemma
comparing `restrict` at two targets; the pairing laws are `rfl` by Σ-eta.

### 1.5 Π

The fibre of `Bind a c` at `(I, γ)`:

```text
{ h : ∀ J (f : J ⟶ I) (x : a.fam J (Γ.map f γ)), c.fam J ⟨Γ.map f γ, x⟩  //  natural }
```

It is indexed by `f`, not by morphisms of the category of elements: with the
latter, the two sides of `Bind_subst` range over `Γ.obj J` and over `Δ.obj J`, and
their equality is not provable.

The fibre is defined as a function `Fib a c I e he` of a family of points
`e : ∀ J, (J ⟶ I) → Γ.obj J` with its coherence `he`. Restriction along `f′`
precomposes `e` with `− ≫ f′`, reindexing along `σ` postcomposes it with `σ.app`,
and a transport `Fib a c I e₁ ⟶ Fib a c I e₂` for `e₁ = e₂` is built from
`restrict 𝟙`. The two sides of `Bind_subst` at `(I, δ)` are then `Fib` at

```text
e₁ f := Γ.map f (σ.app δ)            e₂ f := σ.app (Δ.map f δ)
```

the second after unfolding `substTy` and `lift` definitionally. `e₁ = e₂` is the
naturality of `σ`, and `Bind_subst` and `lam_subst` are congruences along it: the
one hard lemma of the pass.

```text
lam e   := γ ↦ (f, x) ↦ e.app ⟨Γ.map f γ, x⟩                          cast-free
unlam t := ⟨γ, x⟩ ↦ (t.app γ) at f = 𝟙, with x and the result moved by restrict 𝟙
```

`unlam_lam` is the naturality of `e` along `𝟙`. `lam_unlam` is the naturality of
`t` together with `𝟙 ≫ f = f`, used through a lemma saying that the family depends
on `f` only up to transport.

### 1.6 Universe and decoding

```text
よI                 obj J := J ⟶ I,  map g u := g ≫ u              a Presheaf with values in Type v
𝒰.obj I             DPSh (よI), fibres in Type v
𝒰.map f X           X reindexed along よf : よJ ⟶ よI
U Γ                 𝒰, constant over Γ
El S at (I, γ)      ULift ((S.app γ).fam I (𝟙 I))
```

The functor laws of `𝒰` are propositional (`comp_id`, `assoc` of `𝒞`), proved by
extensionality of `DPSh`. The restriction of `El S` restricts inside `S.app γ` from
`𝟙 I` to `𝟙 J ≫ f`, landing definitionally in `(𝒰.map f (S.app γ)).fam J (𝟙 J)`,
then casts along the naturality of the section `S`, which is an equation in
`𝒰.obj J`. This is the one cast in the pass. The two sides of `El_subst` cast
along proofs of the same proposition, so `El_subst` is `rfl`.

### 1.7 Equality

```text
IdSort S S′ at (I, γ)     ULift (PLift (S.app γ = S′.app γ))
IdElement l r at (I, γ)   ULift (PLift (l.app γ = r.app γ))
```

The restriction is rewriting by the naturality of the two sections. `refl` is
`rfl`, irrelevance is proof irrelevance, and reflection is extensionality of
sections.

### 1.8 Files and order

```text
HrS/Presheaf/Basic.lean       Presheaf, DPSh, Sub, Section, reindexing, empty,
                              restriction at two targets, DPSh.ext, Section.ext
HrS/Presheaf/Extension.lean   extend, projection, generic, pair                    after Basic
HrS/Presheaf/Pi.lean          Fib and its transport, Bind, lam, unlam,
                              Bind_subst, lam_subst                                after Extension
HrS/Presheaf/Universe.lean    よ, 𝒰, U, El                                          after Basic
HrS/Presheaf/Identity.lean    IdSort, IdElement                                    after Universe
HrS/Presheaf/Model.lean       PSh 𝒞 : HrS.Structure, J 𝒞                           last
```

**Probes first**, a few lines each, left in place:

```text
P1  substTy_comp, comp_assoc                  rfl
P2  generic_pair, pair_comp                   HEq.rfl, rfl
P3  El_subst                                  rfl, with the cast in El's restriction
P4  Bind_subst                                the right side unfolds to Fib at e₂
```

If `rfl` fails or is slow, the fallback keeps the representation and proves those
laws through `DPSh.ext`.

### 1.9 For later passes

Points of `(J 𝒞).onOb X` at a stage are elements of its `obj`; fibres of
`(J 𝒞).onTy a` are `fam`; terms are `Section`s. Restriction of presheaves,
dependent presheaves and sections along a functor `𝒞 ⥤ 𝒟` is needed in §4 and is
defined there.

### 1.10 Not taken

- Mathlib's `𝒞ᵒᵖ ⥤ Type` with `Functor.Elements` and `CategoryOfElements.map`:
  the same table of laws, with `op` in every fibre index and functor equality
  through `Functor.ext`.
- Types as maps into a universe of families (natural models): reindexing becomes
  composition, but `Π` still restricts points, and terms cast along the unit laws of
  `𝒞`.

Size: of the order of `Ctx/Single.lean` through `Ctx/Identity.lean`. `[open]`

---

## 2. Theories and positivity

`Theory/Basic.lean`:

```text
Theory              signature : Ctx,  admissible,  admissible_subst
Theory.entry x      the class of ⟨α, Ξ.binding x, Ξ.declaration x, _⟩ over Ξ
Theory.ofSchemas    admissible = instances of finitely many schemas (Δ, e)
chains              HrS.Chain Ctx.model Ξ.toOb, admissible and positive ones
PositiveEntry, PositiveBinding, Positive
```

`Ctx/Inversion.lean`, needed to recurse over raw slot telescopes with class-level
positivity: `Bind` is injective; `Bind` is not an atom; the atoms `U`, `El`,
`IdSort`, `IdElement` are pairwise distinct. Also: over `Ξ ▷ c` with `c` positive,
every sort term is headed by a sort slot of `Ξ` (from `Ctx/Generation.lean`).
`[open]`

Examples, as tests of the definitions at their use sites: Freyd categories
(beyond-sogats-examples.md §4), untyped λ with `[x : of tm] ∈ 𝒫`; MLTT once writing
`Ξ_MLTT` as a raw ambient with its well-formedness proof is affordable. `[open]`

---

## 3. Models

`Theory/Model.lean`:

```text
Model T   𝒞 small, chosen terminal 1
          M   : (PSh 𝒞).Sub (PSh 𝒞).empty ((J 𝒞).onOb Ξ.toOb)
          ext : for c a chain of positive entries over Ξ, a admissible over Ξ ▷ c,
                I : 𝒞, g ∈ J(Ξ ▷ c)(I) over M:
                I ⊲ a,   p : I ⊲ a ⟶ I,   v ∈ J(a)(I ⊲ a, g·p),   universal
```

Unfolding lemmas (the components of `M` at sort, operation and equation slots,
semantics.md Lemma 3.3) as far as later passes need them. `[open]`

---

## 4. Morphisms and the category of models

**Relational model.** For `F : 𝒞 ⥤ 𝒟`, an HrS-structure `Rel F`: an object is a
presheaf over `𝒞`, a presheaf over `𝒟`, and a proof-relevant relation between the
first and the second restricted along `F`; types and terms likewise, componentwise.
The universe relates `X` and `Y` by the maps `El X ⟶ F*(El Y)`, and `El` of such a
map is its graph; `Bind` is the logical relation over the images of `F`. Its two
projections are strict HrS-morphisms by construction, so by `HrS.initial` the
composites of `J (Rel F)` with them are `J 𝒞` and `J 𝒟`: the fundamental lemma,
invariance under `≈` included.

- Not the direct route (comparisons by recursion on positive syntax): invariance
  under `≈` would need an induction on `Eq_e`, and `Eq_e.congr` has premises over
  `Ξ ⋈ Θ` for arbitrary `Θ`, where no comparison is defined. `J (Rel F)` is defined
  on classes.
- Not presheaves on the collage of `F`, which `Rel F` is up to iso: restriction to
  a sieve preserves `Π` only up to iso, so the projections would not be strict.

**Morphism.** `(F, r)` with `r` a point of `J (Rel F) Ξ` over `(M, N)`, and (ext):
at related points `F (I ⊲ a) = F I ⊲ a`, with projections and generic elements
related. The sort components of `r` are the maps `φ_y`; its operation components
are the commutation with operations; its components at sort equations are the
condition on sort equations.

**Functionality** `[paper]`. On a chain of positive entries, relatedness of points
over `M` and over `N` is the graph of a map, natural along `F`; for a composite it is
the composite. Induction on positivity:

```text
El S         related points give a map φ_S : El⟦S⟧_M → El⟦S⟧_N; relatedness is its graph
IdElement    l_M g = r_M g  ⟹  l_N g′ = φ(l_M g) = φ(r_M g) = r_N g′;  graph of ★ ↦ ★
Bind w c′    w admissible:  F(I ⊲ w) = FI ⊲ w′,  φ v = v′                    (ext)
             h′ is determined by  h′(p, v′) = φ_{c′}(h(p, v))                 Yoneda in 𝒟
             F⟨f, u⟩ = ⟨Ff, φu⟩,  so  h′(Ff, φu) = φ_{c′}(h(f, u))            related
```

Sort terms over `Ξ ▷ c` are headed by sort slots of `Ξ`, `c` having no sort entries,
so `φ_S` is computed from the `φ_y` and composes. Each excluded form fails in this
induction: an `IdSort` entry is not a graph, a sort entry is related by an arbitrary
map, a non-admissible binder has no generic element.

Then composition `(G, s) ∘ (F, r)`, identities, associativity: `Category T.Model`
in each universe. `[open]`

**Sort equations** `[paper]`. Russell universes, beyond-sogats-examples.md §10:

```text
e₁ : [n] eq (El (S n) (U n)) (Ty n)          φ_El(S n, U n) = φ_Ty(n)
e₂ : [n, A] eq (El (S n) (lift n A)) (El n A)   φ_El(S n, lift n A) = φ_El(n, A)
```

Well typed: sources agree by the equations in `M`; targets by commutation with `S`,
`U`, `lift` and the equations in `N`. Right: a code and the type it names are one
element, so the morphism treats them alike; likewise for cumulativity. Enough:
equations derived from `e₁`, `e₂` hold in `J (Rel F)` by soundness.

---

## 5. The term model

`Theory/TermModel.lean`:

```text
𝒞syn    objects: admissible chains over Ξ;  maps: Ctx maps over Ξ between their ends
1       the empty chain
M_syn   slot by slot, by recursion on the raw telescope of the slot:
        inputs read back through Yoneda at admissible binders, then args ↦ [ap x args]
ext     c ↦ c ▷ a,  universal property from the pairing of Ctx
```

Lemmas: at the points of positive chain objects over `M_syn` every element is
syntactic; `J(e)(M_syn) = [e]` for expressions over positive chain objects
(induction on `Expr.Subterm`); the declared equations of `Ξ` hold (`Eq_e.hyp`).
The riskiest item after §1. `[open]`

---

## 6. Existence

`F` on objects by recursion on chains, `F [] = 1`, `F (c ▷ a) = F c ⊲ a` in `N` at the
related point; on maps through `J 𝒟` at `N` and the universal property. The point
`r`: at sort slots, a syntactic sort goes to its interpretation in `N`; operation
components related by the lemma `J(e)(M_syn) = [e]` and soundness of `J 𝒟`. (ext) by
construction. `[open]`

---

## 7. Uniqueness

A morphism out of the term model is determined: on objects by (ext) and induction
on chains; on maps by its operation components and induction on expressions; its
point by the sort components, which functionality fixes on syntactic sorts. The
pattern is that of `Ctx/Generation.lean` and `HrS/Closed.lean`. `[open]`

---

## 8. Statement and instances

`Theory.initial`; instances for the examples of §2. `[open]`

---

## Order

```text
1 ──┐
    ├──> 3 ──> 4 ──────────┐
2 ──┘      └──> 5 ─────────┴──> 6 ──> 7 ──> 8
```

1 and 2 can proceed in parallel. Risks: 1 (a strict universe and `Π` in Lean) and 5
(reading inputs back).
