# `Ctx` is a category with representable maps

Companion to `semantics.md`, which states this as its Proposition 1.3 and uses it
throughout. Here it is proved, with the dependent products written out in full.
`equational-telescopes-core.md` is assumed; bare numbers — `1.6`, `3.4`, `13.2` —
refer to it, and `§n` to `semantics.md`.

**Standing assumption.** The carrier is the list carrier of
`examples/ListCarrier.lean`: an arity is a list of `Entry`, an `Entry` is a list
of `Entry` — its binding arity. So an arity is a forest, a slot is a position in
the top-level list, `before` and `after` are `take` and `drop`, and the
decomposition `Γ ⋈ [z]` into all-but-the-last and the last is unique.

**Status marks.** `[proved]` here; `[argued]` — the argument is given, the
transports are not checked; `[open]`.

---

## 1. Categories with representable maps

**Definition 1.1** (Uemura, arXiv:1904.04097 Def. 4.1–4.2; thesis Def. 3.2.1,
where it is a **CwR**). A **category with representable maps** is a category `C`
with finite limits together with a class `R` of arrows such that

- identities lie in `R`, and `R` is closed under composition;
- `R` is **pullback-stable**: for `f ∈ R` and any `g` into its codomain, the
  pullback of `f` along `g` exists and lies in `R`;
- every `f : X ⟶ Y` in `R` is **exponentiable**: `f^* : C/Y ⟶ C/X` has a right
  adjoint `Π_f`.

Arrows of `R` are **representable**. A **CwR morphism** preserves finite limits,
representable arrows, and pushforwards along representable arrows.

**1.2 Two deliberate omissions.**

`X ⟶ 1` **is not required to be representable.** An object whose terminal map is
representable is a **context**; the rest are **judgments**. That is what
separates a CwR from a clan, in which every object is fibrant, and why Uemura
writes (thesis Rem. 3.2.10) that clans and display map categories "are considered
as models of a type theory" whereas CwRs "are considered as type theories
themselves".

`R` **is not required to be closed under pushforward.** Exponentiability asserts
that `Π_f` exists, not that it lands back in `R`. Uemura declines the closure
deliberately (Rem. 3.2.11). §3.5 below shows what the omission is: `Π` along a
rank-one display has rank two.

---

## 2. The category and the class

Throughout, `𝒫` is as in §1.2: an assignment `𝒫 Γ ⊆ 𝒯₀ Γ`, closed under
`Γ ⊢ − ≈ −`, stable under `σ ⋆ −`, with `𝟙 ∈ 𝒫 Γ` for every `Γ`, and closed
under `⋈` in the dependent sense — `Θ ∈ 𝒫 Γ` and `Λ ∈ 𝒫 (Γ ⋈ Θ)` imply
`Θ ⋈ Λ ∈ 𝒫 Γ`. Write

```
𝒟_𝒫  :=  { p Γ Θ  :  Γ : Ctx,  Θ ∈ 𝒫 Γ }
```

### 2.1 Finite limits `[argued]`

**Proposition 2.1.** `Ctx` has finite limits.

*Terminal object.* `𝟙`. For any `Ξ`, `Hom Ξ 𝟙 = Filling Ξ (⇑𝟙) = Filling Ξ 𝟙`,
which has exactly one element, the empty family.

*Binary products.* `Γ × Δ := Γ ⋈ ⇑Δ`. By 13.2,

```
Hom(Ψ, Γ ⋈ ⇑Δ)  ≅  Σ (σ : Hom Ψ Γ), Filling Ψ (σ ⋆ ⇑Δ)
```

and `σ ⋆ ⇑Δ = ⇑Δ`, since `⇑Δ` is `Δ` base-weakened and its decoration names no
slot of `Γ`, so `σ` acts on nothing. Hence the right side is
`Hom(Ψ,Γ) × Hom(Ψ,Δ)`, with the projections `p` and the evident second component.

*Equalizers.* For `σ, θ : Ξ ⟶ Γ` let `E(σ,θ) : 𝒯₀ Ξ` carry one entry per
non-equational `z : |Γ| ∋ Λ`, binding `(σ ↾ z) ⋆ (⇑Γ).binding z` and with boundary
`.eq (σ z) (θ z)`. Then `p Ξ E(σ,θ) : Ξ ⋈ E(σ,θ) ⟶ Ξ` equalizes `σ` and `θ`, and
is universal: by 13.3 a filling of an all-equational telescope is unique up to `∼`
and exists exactly when the instantiated equations hold, and "they hold after `κ`"
is literally `κ ≫ σ ∼ κ ≫ θ`.

Uniqueness is **up to `∼`** throughout, `Ctx` being enriched in setoids (9.3).
That is the right reading of a universal property here and is why §9 of the core
note is setoid-first. ∎

**2.1.1 Consequence.** Every morphism of `Ctx` is a display, so the *clan*
structure on `Ctx` is the trivial one (Taylor, *PFM*, Prop. 8.3.4: if product
projections and pullback diagonals are displays then every map is a composite of
displays). The content therefore sits in `𝒟_𝒫`, not in the class of all displays
— which is exactly why the CwR notion, and not the clan notion, is the right one
here. See §4.4 for the full discussion.

### 2.2 Identities, composition, pullback-stability `[proved]`

**Proposition 2.2.** `𝒟_𝒫` contains identities, is closed under composition, and
is pullback-stable.

*Identities.* `p Γ 𝟙 = id_Γ`, and `𝟙 ∈ 𝒫 Γ` by hypothesis.

*Composition.* For `Θ ∈ 𝒫 Γ` and `Λ ∈ 𝒫 (Γ ⋈ Θ)`, associativity of `⋈` gives

```
p Γ Θ  ∘  p (Γ ⋈ Θ) Λ   =   p Γ (Θ ⋈ Λ)
```

and `Θ ⋈ Λ ∈ 𝒫 Γ` by the dependent closure. This is 11.4 restricted to `𝒫`,
which §1.2 shows is a submonoid.

*Pullback-stability.* 10.4's square exhibits, for `σ : Ξ ⟶ Γ`, the pullback of
`p Γ Θ` along `σ` as `p Ξ (σ ⋆ Θ)` with the lifted substitution as the top edge;
and `σ ⋆ Θ ∈ 𝒫 Ξ` because `𝒫` is stable under `σ ⋆ −`. ∎

---

## 3. Dependent products

The remaining axiom. Fix `Γ : Ctx`, `Θ : 𝒯₀ Γ` and `Λ : 𝒯₀ (Γ ⋈ Θ)`; the task is
to construct `Π_Θ Λ : 𝒯₀ Γ` right adjoint to base change along `p Γ Θ`.

### 3.0 Why they should exist at all

**A telescope is a signature, and an entry is a symbol *with an arity*.** So
`Π_Θ Λ` is not a new construction: it is `Λ` **with every symbol given `Θ` more
arguments** — a parameterised signature.

Let `Λ` be the signature of a monoid and `Θ = [A : ty]`:

```
Λ  =  [ M     : sort
      , e     : of M
      , m     : [x : of M, y : of M] of M
      , assoc : [x, y, z : of M] eq (m (m x y) z) (m x (m y z)) ]

Π_Θ Λ  =  [ M     : [A : ty] sort
          , e     : [A : ty] of (M A)
          , m     : [A : ty, x : of (M A), y : of (M A)] of (M A)
          , assoc : [A : ty, x, y, z : of (M A)]
                      eq (m A (m A x y) z) (m A x (m A y z)) ]
```

That is the signature of an **`A`-indexed family of monoids**. Of course it is a
signature — it was obtained by adding a parameter to every symbol. **There is
nothing to construct.**

The two halves of the work are visible in the display.

- Every symbol's **arity grew by `Θ`**. That is `prefix` (3.1), and it is
  trivial.
- Every **mention** of an earlier symbol became an **application**: `M` became
  `M A`, `m` became `m A`. That is `θ_w` (3.2), and it is the only real content —
  the dependency between `Λ`'s entries has to be re-expressed at the same
  parameter.

**Why this fails one level down**, which is what makes it non-obvious. In a
rank-one framework — a GAT, a Lawvere theory — an entry is a *variable*, with no
arity field, so there is nowhere to put the parameter. To say "an `A`-indexed
monoid" there you must postulate a new type former, which is exactly what MLTT's
`Π` is: a *symbol*, added by hand. The syntactic category of the theory of
monoids genuinely has no dependent products, and neither does MLTT-without-`Π`
(§3.4 of `semantics.md`).

`Ctx` has them because **its entries carry arities, and those arities are
unbounded**. The function space is not a type one has to postulate; it is the
arity field, present from the start. That is what higher rank buys, and why `Π`
should exist here and not below.

Two consequences worth carrying forward.

- **`Π` costs rank, necessarily.** `M : sort` binds nothing; `M : [A : ty] sort`
  binds a rank-one telescope. The parameter was paid for with one level of rank
  — which is 3.5's formula and Uemura's non-closure (1.2) at once.
- **It is conjectural only because of `θ_w`.** That one may add a parameter to
  every symbol is not in doubt. What needs proof is that rewriting every
  cross-reference as an application is coherent — that `m A (m A x y) z` is
  really what `assoc` should say — and that is precisely obligation 3.6 and
  Lemma 3.7.1.

### 3.0.1 Four readings of the same fact

*`Π` distributes over a dependent telescope.* Naming what 3.0 displayed: adding a
parameter to a **single** symbol is free, and splitting the addition across a
telescope whose entries depend on each other is the type-theoretic distributivity
law

```
Π_{t : Θ} Σ (v : β_v) β_w(v)   ≅   Σ (f : Π_{t : Θ} β_v) Π_{t : Θ} β_w(f t)
```

and **`θ_w` is exactly the `f t` on the right** — every earlier slot re-applied
to the same `Θ`. So the content of the conjecture is that *this law holds in
`Ctx` on the nose, uniformly in `Θ` and `Λ`*. It is also what rules out the
obvious wrong guess: letting `z_w` bind `Θ ⋈ Λ.before w ⋈ Λ.binding w` leaves `v`
free instead of applying `f` to `t`, which is the uncurried form and has the
wrong rank (3.5).

*Hypothetical judgments of every level.* `Π_Θ Λ` reifies "given `Θ`, derive `Λ`"
as an object. Level one is ordinary context extension; `Π` along a rank-one
telescope is level two; `Π` along anything is arbitrary level. This is
Schroeder-Heister's higher-level rules, and the tradition Gratzer–Sterling invoke
against the one-level stratification (§3.4, §4.5).

*`Ctx` becomes a model of extensional type theory.* Every morphism of `Ctx` is a
display (2.1.1), so `Π` along displays is `Π` along everything and `Ctx` is
locally cartesian closed — hence, by Seely as corrected by Clairambault–Dybjer,
**the framework's own contexts model extensional dependent type theory**. The
sting is §4.4's: equality in the free LCCC is undecidable
(Castellan–Clairambault–Dybjer), so conversion in `Ctx` is too, and decidability
can be expected only relative to a `𝒫`.

*The chain becomes a chain.* `⋈` preserves rank (`max`); by 3.5, `Π` is the only
rank-raising operation. So `𝒯₀^{≤n+1}` is the closure of `𝒯₀^{≤n}` under `Σ` and
`Π`-along-`𝒯₀^{≤n}`. **Without `Π` the filtration is a grading with nothing
moving between its levels** — a filtration of nothing — which is why this section
is the risk gate for all of `semantics.md`, and why §4.2's `∗ = 𝒯₀^{≤1}`,
`□ = 𝒯₀^{≤2}` depends on it: `□` is *defined* by closure under Uemura's product
rule.

### 3.1 The arity: `prefix` `[proved]`

**Definition 3.1.** For arities `Ω` and `Δ`,

```
prefix Ω Δ  :=  ofList ((underlyingList Δ).map (fun e => .mk (underlyingList Ω ++ e.arity)))
```

**Proposition 3.1.** `prefix` satisfies

1. `Δ ∋ α  ≃  prefix Ω Δ ∋ (Ω ⋈ α)`, **at the same index**: position `i` of
   `underlyingList Δ` carries arity `underlyingList α`, and position `i` of
   `prefix Ω Δ` carries `underlyingList Ω ++ underlyingList α`, which is
   `underlyingList (Ω ⋈ α)`. Write `z_w` for the slot matching `w`.
2. `before z_w = prefix Ω (before w)` and `after z_w = prefix Ω (after w)`, since
   `map` commutes with `take` and with `drop`; hence `factor` transports.
3. `prefix Ω (Δ ⋈ Δ') = prefix Ω Δ ⋈ prefix Ω Δ'`, since `map` commutes with `++`.
4. `prefix 1 Δ = Δ` and `prefix Ω (prefix Ω' Δ) = prefix (Ω ⋈ Ω') Δ`, by
   `[] ++ ℓ = ℓ` and associativity of `++`.

*Over an abstract carrier `prefix` is not derivable* from `⋈`, `∋`,
`before`/`after`, `inl`/`inr`/`copair`, `subWf`, and would have to be
axiomatised — items 1–4 being the axioms. Over the list carrier it is `List.map`
and they are `List` lemmas. This is the one place the standing assumption is
load-bearing. ∎

### 3.2 The substitution `θ_w`

Everything turns on one substitution. Fix `w : |Λ| ∋ Ψ` and abbreviate

```
Π_<w  :=  Π_Θ (Λ.before w)          the recursive call, on a shorter list
```

**Definition 3.2.**

```
θ_w  :  (|Θ| ⋈ |Λ.before w|)  ⇒  (|Γ| ⋈ |Π_<w| ⋈ |Θ|)

θ_w (C.inl t)  :=  Expr.η t                         t : |Θ| ∋ β, taken in the trailing block
θ_w (C.inr v)  :=  ap z_v (Subst.ofRenaming ι_v)    v : |Λ.before w| ∋ Ψ_v
```

where `ι_v : |Θ| ⋈ Ψ_v →ʳ |Γ| ⋈ |Π_<w| ⋈ |Θ| ⋈ Ψ_v` hits the last two blocks.

It does two things at once, and both are needed.

**It re-applies the earlier slots.** In `Λ` the slot `v` is a variable of arity
`Ψ_v`; in `Π_Θ Λ` the corresponding `z_v` binds `|Θ| ⋈ Ψ_v`, so every mention of
`v` costs an application, its arguments being the identity on both blocks. This
is the η-expansion every logical-framework encoding performs.

**It moves the `Θ`-block.** This is the point that is easy to miss. The boundary
available sits over

```
|Γ| ⋈ |Θ| ⋈ |Λ.before w| ⋈ Ψ
```

and the one needed over

```
|Γ| ⋈ |Π_<w| ⋈ |Θ| ⋈ Ψ
```

— the `Θ`-block has **moved past** the earlier slots. `Subst.act` holds its
prefix fixed, so **no substitution replacing `|Λ.before w|` alone can produce
this.** Consuming `|Θ| ⋈ |Λ.before w|` in one block, with replacement
`|Π_<w| ⋈ |Θ|`, puts both sides in the shape `|Γ| ⋈ (−) ⋈ Ψ` that 3.6 wants.
Every re-bracketing involved is `rfl` by 1.6.

**Lemma 3.2.1 (compatibility)** `[argued]`**.** For `v` preceding `w`,
`θ_w ↾ (C.inr v) = θ_v`. Immediate from the uniformity of Definition 3.2: the
clauses at a slot do not mention `w`, and `Π_<v` is the restriction of `Π_<w`
along `C.inclusion` by 3.1(2).

### 3.3 The definition `[proved: shapes]`

**Definition 3.3.** `Π_Θ Λ : dTel |Γ|` is given by recursion on the length of
`Λ`, through its three projections (3.4) at each slot `z_w`:

```
|Π_Θ Λ|               :=  prefix |Θ| |Λ|                        z_w binds |Θ| ⋈ Ψ
(Π_Θ Λ).before   z_w  :=  Π_<w
(Π_Θ Λ).binding  z_w  :=  ⇑Θ ⋈ (θ_w ⋆ Λ.binding w)              θ_w at Φ = 1
(Π_Θ Λ).boundary z_w  :=  θ_w ⋆ Λ.boundary w                    θ_w at Φ := Ψ
```

**The types line up.** For the binding:
`Λ.binding w : dTel (|Γ| ⋈ |Θ| ⋈ |Λ.before w|)` of arity `Ψ`, so
`θ_w ⋆ Λ.binding w : dTel (|Γ| ⋈ |Π_<w| ⋈ |Θ|)`, still of arity `Ψ` by 3.2.1 of
the core note; concatenating after `⇑Θ : dTel (|Γ| ⋈ |Π_<w|)` of arity `|Θ|`
yields a `dTel (|Γ| ⋈ |Π_<w|)` of arity `|Θ| ⋈ Ψ` — which is what `z_w` binds by
3.1(1). For the boundary, `Bd.act θ_w Ψ` sends

```
Bd (|Γ| ⋈ (|Θ| ⋈ |Λ.before w|) ⋈ Ψ)   ⟶   Bd (|Γ| ⋈ (|Π_<w| ⋈ |Θ|) ⋈ Ψ)
```

which are exactly the type of `Λ.boundary w` and the type required of
`(Π_Θ Λ).boundary z_w`.

**The order `⇑Θ` first is forced**, not chosen: `Λ.binding w` may name the slots
of `Θ`, so they must already be in scope.

**3.3.1 `Π` exists along every map, not only along `𝒫`-displays.** Definition 3.3
nowhere uses `Θ ∈ 𝒫`: `prefix` and `θ_w` are defined for any `Θ`, and 3.6 asks
only `Γ ⊢ Θ` and `Γ ⋈ Θ ⊢ Λ`. Since every morphism of `Ctx` is a display (2.1.1),
**`Ctx` is locally cartesian closed**, granting 3.6 and 3.7.1. The `𝒫` in 1.1's
exponentiability axiom is only what a CwR *demands*; the construction gives more.

Do not confuse this with the genuine asymmetry: `Π_Θ Λ` **need not lie in `𝒫`**
even when `Θ` and `Λ` do, by the rank computation of 3.5. `Π` exists everywhere;
`𝒫` is not closed under it. The second is Uemura's omission (1.2).

### 3.4 The decoration, path by path `[argued]`

Definition 3.3 gives the three projections; a `dTel` is a `Decoration`, so it is
worth seeing that the two agree. Recall

```
Decoration Ω Δ  :=  ∀ ⦃Φ α⦄, SlotPath Δ Φ α → Bd (Ω ⋈ Φ ⋈ α)
```

A path into `prefix |Θ| |Λ|` is one of:

**`here z_w`.** Then `Φ = before z_w = prefix |Θ| |Λ.before w|` by 3.1(2) and
`α = |Θ| ⋈ Ψ`; the boundary required is
`Bd (|Γ| ⋈ |Π_<w| ⋈ |Θ| ⋈ Ψ)`, which is `(Π_Θ Λ).boundary z_w`.

**`nested z_w p`, with `p` entering the `|Θ|`-half of `|Θ| ⋈ Ψ`.** Slots of a
product split by `C.inl`/`C.inr`, and `before (C.inl t) = before t` by
`C.before_inl`, so `p` is a path of `|Θ|` and the accumulated `Φ` is unchanged.
The boundary is `Θ.decoration` at that path, weakened by the block `|Π_<w|`
inserted after `|Γ|`.

**`nested z_w p`, with `p` entering the `Ψ`-half.** Here
`before (C.inr y) = |Θ| ⋈ before y`, so the accumulated prefix already carries
`|Θ|`; the boundary is `(Λ.binding w).decoration` at the corresponding path,
transported by `θ_w` at the matching suffix.

These are precisely the two halves that `Decoration.concatenate` produces for
`⇑Θ ⋈ (θ_w ⋆ Λ.binding w)`. **So Definition 3.3 is faithful**: the projection
presentation and the path presentation define the same decoration.

### 3.5 Rank `[proved]`

With `rank 1 = 0` and `rank Δ = max over z of (rank (Δ.binding z) + 1)` (§3.1):

```
rank (Π_Θ Λ)  =  max over w of ( rank (Θ ⋈ Λ.binding w) + 1 )
              =  max ( rank Θ + 1 ) ( rank Λ )
```

using `rank (Θ ⋈ Λ') = max (rank Θ) (rank Λ')`. **This is Arkor–McDermott's
`ord (X ⇒ Y) = max (ord X + 1) (ord Y)` on the nose** (Def. 3.1), which is the
best evidence available that Definition 3.3 is the right construction: had `z_w`
bound `Θ ⋈ Λ.before w ⋈ Λ.binding w` — the obvious wrong guess — the rank would
be `max (rank Θ + 1) (rank Λ + 1)`, and the two sides of the adjunction would not
even have the same arities (§3.7).

**Consequence, and the reason for 1.2's second omission.** `Π` along a rank-one
display produces slots binding a rank-one telescope, hence rank two. So
representable maps are *not* closed under pushforward, and a **rank-one framework
— Cartmell's GATs — is not locally cartesian closed.** Uemura must therefore
*assume* exponentiability rather than derive it: his product rule takes a domain
in `∗` to a conclusion in `□`, and nothing lands back in `∗`. Here it is derived,
and the escape from `𝒫` is exactly the rank jump `1 ↦ 2`.

### 3.6 Well-formedness `[argued]`

**Proposition 3.6.** If `Γ ⊢ Θ` and `Γ ⋈ Θ ⊢ Λ` then `Γ ⊢ Π_Θ Λ`.

Everything reduces to one statement about `θ_w`. Write
`Ξ_w := Γ ⋈ Π_<w ⋈ ⇑Θ`.

**Claim.** `Ξ_w ⊢ θ_w : ⇑(Θ ⋈ Λ.before w)`.

*Argument.* Induction over the slots of `Θ ⋈ Λ.before w` in precedence order,
checking 6.3 at each.

- At `C.inl t`: `θ_w (C.inl t) = Expr.η t` with `t` a slot of the trailing `⇑Θ`
  block of `Ξ_w`. By 8(5), `Expr.η` of a non-equational slot is well formed and
  its `boundaryOf` is that slot's declared boundary; both sides are
  `Θ.boundary t` weakened, so the required `≈` holds.
- At `C.inr v`: `θ_w (C.inr v) = ap z_v (Subst.ofRenaming ι_v)`. Well-formedness
  by 6.4 needs (i) `z_v` non-equational and (ii) `Ξ_w ⊢ ι_v-substitution :
  ⇑(Ξ_w.binding z_v)`. For (i), `z_v`'s boundary is `θ_v ⋆ Λ.boundary v` and
  `Bd.act` preserves the constructor (2.3), so `z_v` is equational exactly when
  `v` is — the guard matches on both sides. For (ii), `Ξ_w.binding z_v` is
  `⇑Θ ⋈ (θ_v ⋆ Λ.binding v)` by Definition 3.3, and the identity fills it, which
  is 8(5) slotwise.
  The boundary condition is 4.2: `boundaryOf (ap z_v args) = args ⋆ ⇑(boundary of z_v)`,
  and with `args` the identity this is `θ_v ⋆ Λ.boundary v`. What must match it
  is `(θ_w ↾ C.inr v) ⋆ Λ.boundary v`, and `θ_w ↾ C.inr v = θ_v` by Lemma 3.2.1.

Granting the Claim, `Γ ⊢ Π_Θ Λ` follows by checking 7.1 at each `z_w`: the first
bullet, `Γ ⋈ Π_<w ⊢ ⇑Θ ⋈ (θ_w ⋆ Λ.binding w)`, from 8(8) on the `⇑Θ` factor and
8(9) on the other; the boundary bullet from 8(9) likewise, the three cases of 7.1
being preserved because `Bd.act` preserves the constructor. ∎

**This is the one substantive obligation** and is not checked. It is the natural
place for the construction to fail.

### 3.7 The adjunction `[argued]`

**Proposition 3.7.** For `σ : Ξ ⟶ Γ`, naturally in `Ξ`,

```
Filling Ξ (σ ⋆ Π_Θ Λ)   ≅   Filling (Ξ ⋈ σ ⋆ Θ) (σ⁺ ⋆ Λ)
```

where `σ⁺` is `σ` lifted over `Θ`. Equivalently, `p Γ (Π_Θ Λ)` is right adjoint
to base change along `p Γ Θ`, so `p Γ Θ` is exponentiable.

*The raw bijection is the identity.* A component of the left side at `z_w` lives
in `Expr (|Ξ| ⋈ (|Θ| ⋈ Ψ))`; the matching component of the right side at `w`
lives in `Expr ((|Ξ| ⋈ |Θ|) ⋈ Ψ)`. By 1.6 these arities are **definitionally
equal**, `⋈` being associative on the nose and `Expr` free over the raw arity.
**Currying is `rfl`.** Note also that the slots of `Λ.before w` are *not* in
scope on the right — a filling supplies them, it does not bind them — which is
what forces `z_w` to bind `|Θ| ⋈ Ψ` and nothing more (§3.5).

*What has to be checked* is that the identity carries the judgements across.
6.3's condition at `z_w`, writing `κ := τ ↾ z_w`, is stated over the ambient
`Ξ ⋈ κ ⋆ (Π_Θ Λ).binding z_w`, which by Definition 3.3 is

```
Ξ ⋈ (κ ⋆ ⇑Θ) ⋈ ((κ ⋆ θ_w) ⋆ Λ.binding w)
```

while the corresponding condition on the right is stated over
`(Ξ ⋈ Θ) ⋈ κ′ ⋆ Λ.binding w` for the matching restriction `κ′`. The two agree
provided

**Lemma 3.7.1** `[argued]`**.** `κ ⋆ ⇑Θ = Θ` and `κ ⋆ θ_w = ⟨η_Θ, κ′⟩`.

**This should reduce to lemmas already scheduled.** `θ_w` is built from `Expr.η`
on the `Θ`-block and `ap z_v (identity)` elsewhere, so computing `κ ⋆ θ_w` needs
exactly

```
ap x args = args ⋆ Expr.η x            ⟨η, args⟩ ⋆ e = args ⋆ e
```

and these are the two raw-layer lemmas **8.2 identifies as needed for congruence
(8(6))**, with `act_idOfη` (`Instantiation.lean`) and `act_interchange.aux`
(`Interchange.lean`) named there as their nearest existing relatives. So 3.7.1 is
likely an instance of work the formalization plan already carries, not new
work.

The first is weakening followed by a substitution naming no slot of `Π_<w`. The
second is where Definition 3.2 earns itself: substituting a filling into `θ_w`
turns each `ap z_v (identity)` into the filling's own component at `v`, so `θ_w`
composed with a filling *is* the pairing of the identity on `Θ` with the induced
filling of `Λ.before w`. Prove 3.7.1 and the adjunction follows, the `∼`-clause
being slotwise on both sides.

Equational slots are the easy case: a `Θ`-indexed family of conditions is a
condition quantified over `Θ`, which is what an `eq` slot with a binding
telescope already means, and 9.2 compares components at neither side.

### 3.8 Worked instances `[proved]`

**(a) One slot, no dependency — `θ_w` empty.**
`Γ = 𝟙`, `Θ = [x : sort]`, `Λ = [y : sort]`. Then `prefix |Θ| |Λ|` is a
one-entry arity whose entry has binding arity `|Θ|`, so

```
Π_Θ Λ  =  [ z : [x′ : sort] sort ]
```

and both sides of 3.7 are "an expression in `|Ξ| ⋈ |Θ|` of boundary `sort`" —
`θ_w` is empty, there being no earlier slot, and the two arities coincide on the
nose. Rank: `max (rank Θ + 1) (rank Λ) = max (0 + 1 + 1) 1 = 2`, and indeed
`Π_Θ Λ` has a slot binding a rank-one telescope.

**(b) Two slots with a dependency — where `θ_w` does the work.** Over an ambient
declaring `ty : sort` and `tm : [A : ty] sort`, take

```
Θ = [ A : ty ]                Λ = [ B : ty,  e : tm B ]
```

Then

```
Π_Θ Λ  =  [ F : [A : ty] ty,   g : [A : ty] tm (F A) ]
```

and the entire content sits in `g`'s boundary, which is `tm (F A)` and **not**
`tm B`. Computing it from Definition 3.2 at `w := e`:

```
Λ.before e = [B]           Π_<e = [ F : [A : ty] ty ]

θ_e  :  ([A] ⋈ [B])  ⇒  (|Γ| ⋈ [F] ⋈ [A])
θ_e A  =  Expr.η A                      the trailing A
θ_e B  =  ap F ⟨η A⟩  =  F A            B re-applied to the Θ-block

(Π_Θ Λ).boundary z_e  =  θ_e ⋆ (of (tm B))  =  of (tm (F A))
```

This is the distributivity law of §3, instantiated:

```
Π_{A : ty} Σ (B : ty) (tm B)   ≅   Σ (F : Π_A ty) Π_{A : ty} tm (F A)
```

and it exhibits the wrong guess concretely. Had `z_e` bound `Θ ⋈ Λ.before e`, the
result would be `[ g : [A : ty, B : ty] tm B ]` — a function of `A` **and an
arbitrary `B`**, with nothing tying `B` to `F A`, so the two components would be
unrelated. `Π` into a telescope requires the later component to land in the fibre
the earlier one picks out, and that is exactly what `θ_w` arranges.

---

## 4. Slices `[proved]`

**Proposition 4.** If `(C, R)` is a CwR and `X : C`, then `C/X` with the arrows
whose underlying map lies in `R` is a CwR.

Slices of categories with finite limits have finite limits. The three class
conditions are computed in `C` and transport verbatim, pullbacks in a slice being
pullbacks in the base. For exponentiability, `(C/X)/f ≅ C/dom f` identifies the
pullback functor of the slice with the one of `C`, so it has the same right
adjoint. ∎

**Corollary.** For a theory `(Ξ, 𝒫)` in the sense of §1.4, the classifying CwR
`Ctx_{(Ξ,𝒫)} = Ctx / Ξ` — with representable maps the projections `p Γ Θ`,
`Θ ∈ 𝒫 Γ` — is a CwR, granting Proposition 3.7.

---

## 5. Status

| # | statement | status |
|---|---|---|
| 2.1 | `Ctx` has finite limits | `[argued]` |
| 2.2 | `𝒟_𝒫`: identities, composition, pullback-stability | `[proved]` |
| 3.1 | `prefix` and its four laws | `[proved]` over the list carrier |
| 3.3 | `Π_Θ Λ` is well typed — every arity checked | `[proved]` |
| 3.4 | projection and path presentations agree | `[argued]` |
| 3.5 | `rank (Π_Θ Λ) = max (rank Θ + 1) (rank Λ)` | `[proved]` |
| **3.6** | **`θ_w` is well formed, hence `Γ ⊢ Π_Θ Λ`** | **`[argued]` — the gap** |
| 3.7.1 | `κ ⋆ θ_w = ⟨η_Θ, κ′⟩` | `[argued]` — reduces to 8.2's raw lemmas |
| 4 | slices of CwRs are CwRs | `[proved]` |

**What to do first.** 3.1 and 3.3 are mechanical and can be written immediately;
they are what makes `Π_Θ Λ` a definition rather than a hope. Then 3.7.1, which
should fall out of 8.2's two raw lemmas and decides whether the adjunction is
real. Then 3.6, the bulk, and the only place a genuine obstruction is likely. Only after
3.6 and 3.7.1 may `Ctx` be called a CwR, and with it everything in §§2–4 of
`semantics.md` that rests on Proposition 1.3(c).
