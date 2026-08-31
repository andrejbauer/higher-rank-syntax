# Semantics for higher-rank theories

This note contains three things: what a **higher-rank theory** is, what a
**model** of one is, and the argument that these are the right notions.
`equational-telescopes.md` is assumed; bare numbers — `13.2`, `3.2.1` —
refer to it.

**Standing assumptions.** The carrier is the list carrier of
`examples/ListCarrier.lean`. `Ctx` and `𝒯` are taken **quotiented**, not
setoid-enriched, so `Ctx` is an ordinary category and `𝒯` a `Set`-valued
presheaf. Nothing beyond §§9–13 is assumed of `Ctx`: the category structure, the
extension `Γ ⋈ Θ` with its projection, and the monoid law of 11.4.

In particular **`Ctx` is not required to be a CwR**.

---

## 1. The framework in the target

**Sizes.** Fix Grothendieck universes `𝒰₀ ∈ 𝒰₁`. Throughout, `𝒞` is a
`𝒰₀`-small category with a terminal object, and

```text
PSh(𝒞)  :=  [ 𝒞ᵒᵖ , Set_{𝒰₁} ]
```

A presheaf or dependent presheaf is **small** when its values are `𝒰₀`-sets. The
universe `𝒰` of 1.2 classifies the small dependent presheaves; it is
`Set_{𝒰₁}`-valued, hence an object of `PSh(𝒞)`.

Smallness is demanded at exactly one point: clause (iv) of 1.3 asks that an
expression of `sort`-boundary interpret as a *section of `𝒰`*. So **a model's
sorts are `𝒰₀`-small**, and that is the whole content of the size discipline.

Read `PSh(𝒞)` as the **judgments** over `𝒞`'s **contexts**.

> **Basic definitions.** A **dependent presheaf** `A` over `Γ : PSh(𝒞)` consists
> of a set `A I γ` for each `I : 𝒞` and `γ ∈ Γ I`, together with a **restriction**
>
> ```text
> (−) · f  :  A I γ ⟶ A J (γ · f)          for each  f : J ⟶ I
> ```
>
> satisfying `a · id_I = a` and `(a · f) · g = a · (f ∘ g)` for `g : K ⟶ J`.
> Equivalently, a presheaf on the category of elements `∫Γ`. Write `DPSh(Γ)` for
> these. Note the two uses of `·`: on the left of the display it is `A`'s
> restriction, inside `A J (γ · f)` it is `Γ`'s.
>
> A **section** of `A ∈ DPSh(Γ)` is a family assigning to each `I : 𝒞` and each
> `γ ∈ Γ I` an element
>
> ```text
> s I γ  ∈  A I γ
> ```
>
> **natural** in the sense that for every `f : J ⟶ I`,
>
> ```text
> (s I γ) · f   =   s J (γ · f)
> ```
>
> the left `·` being `A`'s restriction and the right `Γ`'s. Write `Sect_Γ(A)` for
> the set of sections.
>
> Since `1 I` is a singleton for every `I`, a dependent presheaf over `1` is the
> same thing as a presheaf — `DPSh(1) ≅ PSh(𝒞)` — and a section over `1` is
> called a **global element**.
>
> `Σ` and `Π` denote the dependent sum and product of `PSh(𝒞)`, written out in
> 1.2.

> **Definition 1.1 (locally representable).** `A ∈ DPSh(Γ)` is **locally
> representable** when every `I : 𝒞` and `γ ∈ Γ I` admit an object `I ⊲ A` of `𝒞`
> with a bijection natural in `J`,
>
> ```text
> 𝒞(J, I ⊲ A)   ≅   Σ (f : 𝒞(J, I)), A J (γ · f)
> ```

In words: **a context can be extended by `A`**. A general dependent presheaf is a
judgment; a locally representable one is a judgment one may hypothesise. This is
Uemura's Def. 3.8 — a map of discrete fibrations is representable when it has a
right adjoint as a functor — under `DFib_𝒞 ≃ PSh(𝒞)`.

Note that the displayed bijection makes `A` **small**: its left side is a
`𝒰₀`-set, `𝒞` being `𝒰₀`-small. So a locally representable dependent presheaf is
automatically small, and the condition of 3.1 needs no separate size
hypothesis.

### 1.2 Dependent sums, products, and the universe, explicitly

All of the following are standard; they are written out so that Definition 1.3
can be read as a specification. Throughout `f : J ⟶ I` and `g : K ⟶ J` in `𝒞`.

**Reindexing.** For `u : Δ ⟶ Γ` in `PSh(𝒞)`,

```text
u^*  :  DPSh(Γ) ⟶ DPSh(Δ)

(u^* A) I δ   :=  A I (u_I δ)
a · f         :=  a · f                                    the restriction of A
```

The second clause is well typed by the chain

```text
a · f  ∈  A J ((u_I δ) · f)  =  A J (u_J (δ · f))  =  (u^* A) J (δ · f)
```

whose first equality is naturality of `u` and whose second is the first clause.

**Dependent sum.** Two operations, related below. For `Γ ∈ PSh(𝒞)`,

```text
Σ_Γ  :  DPSh(Γ) ⟶ PSh(𝒞)

(Σ_Γ A) I     :=  Σ (γ ∈ Γ I), A I γ
(γ, a) · f    :=  (γ · f, a · f)
π : Σ_Γ A ⟶ Γ,   π (γ, a) := γ
```

and, for `Γ ∈ PSh(𝒞)` and `A ∈ DPSh(Γ)` fixed, the *dependent* form

```text
Σ_A  :  DPSh(Σ_Γ A) ⟶ DPSh(Γ)

(Σ_A B) I γ   :=  Σ (a ∈ A I γ), B I (γ, a)
(a, b) · f    :=  (a · f, b · f)
```

The two agree in the evident sense: `Σ_Γ (Σ_A B) = Σ_{Σ_Γ A} B`.

**Dependent product.** For `Γ ∈ PSh(𝒞)` and `A ∈ DPSh(Γ)` fixed,

```text
Π_A  :  DPSh(Σ_Γ A) ⟶ DPSh(Γ)

(Π_A B) I γ   :=  { b  |  b assigns to every  f : J ⟶ I  and  a ∈ A J (γ · f)
                          an element  b f a ∈ B J (γ · f, a),
                          subject to  (b f a) · g  =  b (f ∘ g) (a · g) }
(b · h) f a   :=  b (h ∘ f) a                         h : I′ ⟶ I
```

so `Π_A B ∈ DPSh(Γ)`. Note `Π_{1} B = B` when `A` is terminal, since then `a` is
uniquely determined.

**Universe.** For `I : 𝒞` write `よI := 𝒞(−, I)`. The Hofmann–Streicher universe
is

```text
𝒰 I           :=  { A ∈ DPSh(よI)  |  A is 𝒰₀-small }
(A · f) K u   :=  A K (f ∘ u)                          u ∈ 𝒞(K, J)
```

`𝒰` is a presheaf, whereas `Sect_Γ(−)` takes a *dependent* presheaf over `Γ`. The
two are reconciled by **weakening**: for any `X ∈ PSh(𝒞)` and any `Γ`, regard `X`
as an object of `DPSh(1)` by `DPSh(1) ≅ PSh(𝒞)` and reindex along the unique
`! : Γ ⟶ 1`, giving

```text
!^* X ∈ DPSh(Γ),      (!^* X) I γ  =  X I,     with X's restriction
```

Below, `𝒰` written where a dependent presheaf over `Γ` is expected means `!^* 𝒰`.
With that, the **decoding** is

```text
El  :  Sect_Γ(𝒰) ⟶ DPSh(Γ)

(El S) I γ    :=  (S I γ) I (id_I)
```

Sections of `𝒰` over `Γ` correspond to `𝒰₀`-small elements of `DPSh(Γ)`.

**Equalizer.** For `A ∈ DPSh(Γ)`,

```text
Eq  :  Sect_Γ(A) × Sect_Γ(A) ⟶ DPSh(Γ)

Eq(s, t) I γ  :=  { ★  |  s I γ = t I γ }
```

a subterminal: inhabited exactly where `s` and `t` agree, and then by one element.

### 1.3 The framework interpretation

> **Definition 1.3.** We define a functor
>
> ```text
> J  =  J_𝒞  :  Ctx ⟶ PSh(𝒞)
> ```
>
> — the **framework interpretation**, sending an ambient to the presheaf of its
> structures — together with three auxiliary families, by simultaneous recursion:
>
> ```text
> (i)    J Γ      ∈ PSh(𝒞)       for an ambient Γ           J on objects
> (ii)   ⟦Δ⟧_Γ    ∈ DPSh(J Γ)    for Δ : 𝒯 Γ
> (iii)  ⟦β⟧_Γ    ∈ DPSh(J Γ)    for β a boundary over Γ
> (iv)   ⟦e⟧_Γ                   for e an expression over Γ:
>          a section of 𝒰 over J Γ            when boundaryOf e is .sort
>          a section of El ⟦S⟧_Γ over J Γ     when boundaryOf e is .of S
> ```
>
> Of these only (i) and the action on morphisms below are part of `J`; (ii)–(iv)
> are what the recursion needs in order to state (i). The whole of Definition 1.3
> is made **once**, uniformly in `𝒞`.
>
> **Ambients.** An ambient is a list, so we can define:
> ```text
> J 𝟙            :=  1                        the terminal presheaf
> J (Γ ⋈ [z])    :=  Σ_{J Γ} ⟦[z]⟧_Γ
> ```
>
> **(v) Concatenation.** Alongside (i)–(iv) one constructs, by induction on `Θ`,
> a canonical isomorphism
>
> ```text
> c_{Γ,Θ}  :  J (Γ ⋈ Θ)  ≅  Σ_{J Γ} ⟦Θ⟧_Γ
> ```
>
> natural in `Γ`. At `Θ = 𝟙` it is the unitor `Σ_{J Γ} 1 ≅ J Γ`, at a single slot
> the identity, and at `Θ ⋈ [z]` the associator composed with the previous stage.
>
> **Telescopes.** For `Δ : 𝒯 Γ`, again by the last entry:
>
> ```text
> ⟦𝟙⟧_Γ          :=  1                        terminal in DPSh(J Γ)
> ⟦Δ ⋈ [z]⟧_Γ    :=  Σ_{⟦Δ⟧_Γ} ( Π_{B_z} C_z )
> ```
>
> where, `z` being the last slot of `Δ ⋈ [z]`, so that `z.binding : 𝒯 (Γ ⋈ Δ)`
> and `z.boundary` is a boundary over `Γ ⋈ Δ ⋈ z.binding`,
>
> ```text
> B_z  :=  ⟦z.binding⟧_{Γ ⋈ Δ}    ∈ DPSh( J (Γ ⋈ Δ) )  =  DPSh( Σ_{J Γ} ⟦Δ⟧_Γ )
> C_z  :=  ⟦z.boundary⟧_{Γ ⋈ Δ ⋈ z.binding}
>                                 ∈ DPSh( J (Γ ⋈ Δ ⋈ z.binding) )
>                                 =  DPSh( Σ_{J (Γ ⋈ Δ)} B_z )
> ```
>
> so `Π_{B_z} C_z ∈ DPSh(J (Γ ⋈ Δ))` and `Σ_{⟦Δ⟧_Γ} (Π_{B_z} C_z) ∈ DPSh(J Γ)`,
> as required.
>
> **Both displayed identifications of bases are (v)**, and neither is free. For
> `Π_{B_z}` to accept `C_z` its base must be `Σ_{J (Γ ⋈ Δ)} B_z`, whereas `C_z`
> is given over `J (Γ ⋈ Δ ⋈ z.binding)`; and for the outer `Σ_{⟦Δ⟧_Γ}` to accept
> the result, `B_z`'s base must be `Σ_{J Γ} ⟦Δ⟧_Γ`, whereas it is given over
> `J (Γ ⋈ Δ)`. Each gap is closed by `c_{Γ,Δ}` and `c_{Γ ⋈ Δ, z.binding}`
> respectively, available at the smaller arguments the recursion has already
> reached. **In a formalization these are transports, not `rfl`.**
>
> This is the one place where the syntax and the semantics part company on
> strictness: `Γ ⋈ 𝟙 = Γ` and associativity of `⋈` hold definitionally in the
> syntax (1.6), whereas on the semantic side `Σ_{J Γ} 1 ≅ J Γ` only up to the
> unitor. Coherence of the `c`'s — that the two ways of reassociating a triple
> agree — is part of 1.3.1.
>
> **Boundaries.**
>
> ```text
> ⟦.sort⟧_Γ      :=  !^* 𝒰                    weakened to J Γ, as in 1.2
> ⟦.of S⟧_Γ      :=  El ⟦S⟧_Γ
> ⟦.eq l r⟧_Γ    :=  Eq( ⟦l⟧_Γ , ⟦r⟧_Γ )
> ```
>
> The `eq` clause typechecks because 7.1 requires `l` and `r` to have the same
> boundary, so `⟦l⟧_Γ` and `⟦r⟧_Γ` are sections of one and the same dependent
> presheaf.
>
> **Expressions.** Every expression over `Γ` is `ap x args` with `x : |Γ| ∋ α`
> and `args : α ⇒ |Γ|`; by 4.1 `args` is a filling of the telescope `x` binds.
> Write `Γ_{<x} := Γ.before x` and factor `Γ` at `x` (3.4),
>
> ```text
> Γ  =  Γ_{<x} ⋈ [x] ⋈ Γ_{>x}
> ```
>
> so `x.binding : 𝒯 Γ_{<x}` and `x.boundary` is a boundary over
> `Γ_{<x} ⋈ x.binding`. Put
>
> ```text
> B_x  :=  ⟦x.binding⟧_{Γ_{<x}}                 ∈ DPSh(J Γ_{<x})
> C_x  :=  ⟦x.boundary⟧_{Γ_{<x} ⋈ x.binding}    ∈ DPSh(Σ_{J Γ_{<x}} B_x)
> ```
>
> the second typing by (v) at `(Γ_{<x}, x.binding)`.
>
> *The component at `x`.* Let `p : Γ ⟶ Γ_{<x}` be the projection of `Ctx`, so
> `J p : J Γ ⟶ J Γ_{<x}`, and put `γ_{<x} := (J p)_I γ` for `γ ∈ (J Γ) I`.
> Applying (v) twice to the factorisation above,
>
> ```text
> J Γ  ≅  Σ_{J (Γ_{<x} ⋈ [x])} ⟦Γ_{>x}⟧
> J (Γ_{<x} ⋈ [x])  ≅  Σ_{J Γ_{<x}} (Π_{B_x} C_x)
> ```
>
> so `γ` determines, along these isomorphisms, a component
>
> ```text
> γ_x  ∈  (Π_{B_x} C_x) I γ_{<x}
> ```
>
> *The arguments.* Following the telescope clause, a filling of `x.binding` is a
> tuple with one component per slot of it; interpreting each component by (iv)
> and assembling by induction on `x.binding` gives
>
> ```text
> ⟦args⟧  ∈  Sect_{J Γ} ( (J p)^* B_x )
> ```
>
> so that `⟦args⟧ I γ ∈ B_x I γ_{<x}`.
>
> *The clause.* By the description of `Π` in 1.2, `γ_x` accepts an `f : J ⟶ I`
> together with an element of `B_x J (γ_{<x} · f)`; taking `f := id_I`,
>
> ```text
> ⟦ap x args⟧ I γ  :=  γ_x (id_I) (⟦args⟧ I γ)   ∈  C_x I (γ_{<x}, ⟦args⟧ I γ)
> ```
>
> and `C_x` at `(γ_{<x}, ⟦args⟧ I γ)` is `x`'s declared boundary instantiated at
> `⟦args⟧`, which by 4.2 is `boundaryOf (ap x args)`. So (iv)'s typing is
> preserved.
>
> **`J` on morphisms.** A map `σ : Ξ ⟶ Γ` of `Ctx` is a filling of `⇑Γ` over `Ξ`
> (9.3), so it assigns to each slot `z` of `Γ` an expression `σ z` over `Ξ`
> extended by `z`'s binding arity. Define
>
> ```text
> J σ  :  J Ξ ⟶ J Γ
> ```
>
> componentwise: `(J σ) I M` is the tuple whose `z`-component is `⟦σ z⟧`
> evaluated at `M`, which by (iv) lands in the factor `Π_{B_z} C_z` that the
> telescope clause placed at `z`. Functoriality, `J id = id` and `J` of a
> composite the composite of the `J`s, is `act_id` and `act_comp`; it is part of
> 1.3.1.

**Termination.** The recursion is on the pair (nesting depth, length),
lexicographically, nesting well-founded by `C.subWf` as in §7. The clause for
`⟦Δ ⋈ [z]⟧_Γ` calls `⟦Δ⟧_Γ` at the same depth and shorter length, and
`⟦z.binding⟧` and `⟦z.boundary⟧` at strictly smaller depth — `z.binding` is
reached by entering a slot, which is what `C.subWf` measures. Note the latter two
calls are at *longer* ambients, `Γ ⋈ Δ` and `Γ ⋈ Δ ⋈ z.binding`, so length alone
would not do: the drop in depth is what pays for the growth in length.

`J` is covariant on `Ctx`: a map `σ : Ξ ⟶ Γ` is a filling of `Γ` over `Ξ`, so it
turns a `Ξ`-structure into a `Γ`-structure.

> **Proposition 1.3.1** `[conjecture]`**.** Definition 1.3 is well posed and `J`
> is a functor `Ctx ⟶ PSh(𝒞)`, with:
>
> **(a)** `J 𝟙 = 1`, so `J` preserves the terminal object, `𝟙` being terminal in
> `Ctx` (9.3);
>
> **(b)** for `p : Γ ⋈ Θ ⟶ Γ` the projection of `Ctx` (10.4),
>
> ```text
> J p  =  π ∘ c_{Γ,Θ}   :   J (Γ ⋈ Θ)  ⟶  J Γ
> ```
>
> where `c_{Γ,Θ} : J (Γ ⋈ Θ) ≅ Σ_{J Γ} ⟦Θ⟧_Γ` is the isomorphism of (v) and
> `π : Σ_{J Γ} ⟦Θ⟧_Γ ⟶ J Γ` is the first projection of 1.2 — so **the semantic
> projection is `J` of the syntactic one**;
>
> **(c)** `⟦−⟧` commutes with substitution: for `σ : Ξ ⟶ Γ` and `Θ : 𝒯 Γ`,
>
> ```text
> ⟦σ ⋆ Θ⟧_Ξ  ≅  (J σ)^* ⟦Θ⟧_Γ
> ```
>
> canonically and compatibly with `c`.

Well-definedness is the substance, and there are two parts. The clauses must
respect the quotients: `𝒯 Γ` and `ℰ Γ` are quotients by the generated
equivalences, so one needs the **semantic substitution lemma**
`⟦σ ⋆ e⟧ = ⟦e⟧ ∘ ⟦σ⟧` and its telescope form — the analogues of 8(3) and 8(4) —
from which soundness follows: declared equations are sent to equalities because
`⟦.eq l r⟧` is inhabited only where `⟦l⟧ = ⟦r⟧`, and the rest of `≈` is generated
by substitution and congruence. And functoriality of `J` on `Ctx` must be checked
against `act_id` and `act_comp`.

### 1.4 `J` exists for every `𝒞`

Reading off what Definition 1.3 asks of the target:

```text
sort         a universe          Hofmann–Streicher; any small 𝒞
of S         El S                from the universe
eq l r       an equalizer        PSh(𝒞) is a topos
telescopes   Σ                   ✓
binding      Π                   PSh(𝒞) is locally cartesian closed
higher rank  more Π              ✓
```

Every item is available in **any** presheaf topos, so the condition on `𝒞` is:
be small, and have a terminal object. The price is one Grothendieck universe.
`J` is therefore not a parameter to be supplied or a hypothesis to be checked but
canonical infrastructure.

---

## 2. Theories

> **Definition 2.1 (theory).** A **theory** is a pair `(Ξ, 𝒫)`: a well-formed
> ambient `Ξ`, together with an assignment `𝒫` sending each object `(Γ, γ)` of
> the slice `Ctx / Ξ` to a set `𝒫 (Γ, γ) ⊆ 𝒯 Γ`, such that
>
> - `𝒫` is stable under the morphisms of `Ctx / Ξ`: if `σ : (Γ, γ) ⟶ (Δ, δ)` and
>   `Θ ∈ 𝒫 (Δ, δ)` then `σ ⋆ Θ ∈ 𝒫 (Γ, γ)`;
> - `𝟙 ∈ 𝒫 (Γ, γ)` at every object;
> - `𝒫` is closed under `⋈`: `Θ ∈ 𝒫 (Γ, γ)` and `Λ ∈ 𝒫 (Γ ⋈ Θ, γ ∘ p)` imply
>   `Θ ⋈ Λ ∈ 𝒫 (Γ, γ)`.
>
> We write `𝒫 Γ` when `γ` is clear. Members of `𝒫` are the **admissible context
> extensions** of the theory.

`Ξ` is the signature; `𝒫` says what the object theory may hypothesise.

**Why `𝒫` is part of the data.** `Ξ` alone does not determine a theory. Over
`Ξ_MLTT`, taking `𝒫` to be all telescopes gives a logical framework in which one
may hypothesise a fresh sort and a hypothetical equation; taking it to be the
rank-one `of`-boundaried telescopes over the sort `tm` gives MLTT. Both are
legitimate and they have different models.

**Why `𝒫` lives over the slice.** An object of `Ctx / Ξ` is a pair `(Γ, γ)` with 
`γ : Γ ⟶ Ξ` a filling of `Ξ` over `Γ`, so `Γ` **arrives with an interpretation of 
`Ξ`'s symbols**, and a condition naming them can be stated by naming their images 
under `γ`. For MLTT the condition on an entry is that its boundary be `.of S` with 
`S ≈ γ(tm) A` for some `A` of boundary `.of γ(ty)`.

Over a bare `Γ : Ctx` that condition does not even **parse**: a `Γ` with no `ty`
and no `tm` — `𝟙`, say — offers nothing for `S` to be compared against. Nor can
it be patched at such `Γ`. Taking `𝒫 Γ = ∅` violates `𝟙 ∈ 𝒫 Γ`; taking
`𝒫 Γ = {𝟙}` breaks stability, since a `σ : Γ ⟶ Δ` out of such a `Γ` carries a
genuine MLTT context `Θ ∈ 𝒫 Δ` to `σ ⋆ Θ`, which by 3.2.1 has the same arity as
`Θ` and so is not `𝟙`. The slice is moreover the *exact* domain, not merely a
large enough one: `Hom Γ Ξ` is inhabited precisely when `Γ` interprets `Ξ`'s
symbols.

**The example.** For `Ξ_MLTT`, declaring `ty : sort` and `tm : [A : ty] sort`
among its slots,

```text
R (Γ, γ)   =  { S : ℰ Γ  //  Γ ⊢ S ≈ γ(tm) A  for some A with Γ ⊢ A : .of γ(ty) }

𝒫_MLTT (Γ, γ)  =  { Θ : 𝒯 Γ  //  every entry z of Θ has
                                    Θ.binding z  = 𝟙          rank one
                                    Θ.boundary z = .of S      with S ∈ R }
```

so `Θ ∈ 𝒫_MLTT Γ` says exactly that `Θ` is a list `[x₁ : of (tm A₁), …]` — an
MLTT context. Each clause excludes something different, and all three are needed:

| excluded | what it would be | by |
|---|---|---|
| `[X : sort]` | a context postulating a new sort | `of`-boundaried |
| `[q : eq l r]` | a hypothetical equation | `of`-boundaried |
| `[F : [x : of (tm A)] of ty]` | a metavariable of arity one | rank one |
| `[X : of ty]` | **a type variable** | sort in `R` |

The fourth passes the first three and is caught only by `R`, which is why `R` is
needed at all. `R` is stable as Definition 2.1 requires: MLTT declares no equation
between **sorts**, so `≈` between sorts is generated by congruence and preserves
heads; and a morphism of the slice satisfies `σ ≫ δ ∼ γ`, so it carries `δ(tm)` to
`γ(tm)`.

---

## 3. Models

Fix a global element `M : 1 ⟶ J_𝒞 (Ξ)` — equivalently, a natural family
`M_I ∈ (J Ξ) I`. Two constructions depend on it, and are needed to state
Definition 3.1.

> **Notation.** Let `(Γ, γ)` be an object of `Ctx / Ξ`, so `J γ : J Γ ⟶ J Ξ`.
>
> **Structures over `M`.** `⟦Γ⟧_M ∈ PSh(𝒞)` is the pullback of `J γ` along `M`,
> concretely the subpresheaf of `J Γ` cut out by `M`:
>
> ```text
> ⟦Γ⟧_M I   :=  { g ∈ (J Γ) I  |  (J γ)_I g  =  M_I }
> g · f     :=  the restriction taken in J Γ
> ```
>
> well defined because `J γ` and `M` are natural.
>
> **Fillings over `M`.** For `Θ : 𝒯 Γ`, Definition 1.3 gives
> `⟦Θ⟧_Γ ∈ DPSh(J Γ)`. Since `⟦Γ⟧_M ⊆ J Γ`, put
>
> ```text
> ⟦Θ⟧_M  :=  ι^* ⟦Θ⟧_Γ                                    ∈ DPSh(⟦Γ⟧_M)
> ```
>
> where `ι : ⟦Γ⟧_M ↪ J Γ` is the inclusion and `ι^*` is reindexing (1.2). Since
> `ι` is an inclusion this changes nothing fibrewise —
> `⟦Θ⟧_M I g = ⟦Θ⟧_Γ I g` for `g ∈ ⟦Γ⟧_M I` — it only cuts the base down.

**What these are.** `J γ : J Γ ⟶ J Ξ` takes a `Γ`-structure to the `Ξ`-structure
it induces, so `⟦Γ⟧_M` collects the `Γ`-structures inducing exactly `M`. Two
instances say what that amounts to, and by §2 every object of `Ctx / Ξ` is the
second up to isomorphism.

```text
(Ξ, id)        ⟦Ξ⟧_M      =  1          a point: the model M itself
(Ξ ⋈ Θ, p)     ⟦Ξ ⋈ Θ⟧_M  ≅  ⟦Θ⟧_M      the fillings of Θ in the model M
```

The second is the one to hold on to. A `(Ξ ⋈ Θ)`-structure is an `Ξ`-structure
together with a filling of `Θ`, and `J p` forgets the filling; so cutting down to
the fibre over `M` leaves **the ways of extending `M` by `Θ`**. For MLTT and
`Θ = [x : of (tm A)]`, `⟦Θ⟧_M` is the presheaf of terms of type `A` in `M`.

That is what makes Definition 3.1's condition say the intended thing: requiring
`⟦Θ⟧_M` to be locally representable is requiring `𝒞` to contain the context
obtained by extending with `Θ` — for MLTT, that `Γ ⊲ A` exists.

> **Definition 3.1 (model).** Let `(Ξ, 𝒫)` be a theory and `𝒞` a small category
> with a terminal object. A **model of `(Ξ, 𝒫)` in `𝒞`** is a global element
>
> ```text
> M  :  1  ⟶  J_𝒞 (Ξ)
> ```
>
> such that for every object `(Γ, γ)` of `Ctx / Ξ` and every `Θ ∈ 𝒫 (Γ, γ)`, the
> dependent presheaf `⟦Θ⟧_M ∈ DPSh(⟦Γ⟧_M)` is **locally representable** (1.1).
>
> Write `Mod_𝒞 (Ξ, 𝒫)` for the models.

**A model is a point, and nothing more.** All of the framework — sorts,
telescopes, binding, equations — is interpreted once by `J`, uniformly in `𝒞` and
independently of `Ξ`. What a model contributes is a single element of `J(Ξ)`,
together with a condition, and the condition is not extra data: local
representability is a property.

> **Definition 3.2 (morphism).** A morphism `(𝒞, M) ⟶ (𝒟, N)` is a functor
> `F : 𝒞 ⟶ 𝒟` preserving the terminal object, together with a comparison
> `J_𝒞 ⟶ F^* J_𝒟` carrying `M` to `N`, and satisfying the **Beck–Chevalley
> condition at locally representable maps** — equivalently, `F` preserves the
> context extensions `I ⊲ A` that the `𝒫`-clause of 3.1 produces.

`[open]` Hofmann–Streicher universes are not strictly preserved by `F^*`, so the
comparison `J_𝒞 ⟶ F^* J_𝒟` requires a coherence argument. Uemura imposes
Beck–Chevalley only at representable arrows (Def. 4.14) and glosses it (thesis
Def. 3.2.5) as "a morphism between models of a type theory is required to preserve
context comprehension"; Kaposi–Xie avoid the issue by taking morphisms at the
translated first-order level. This is the one place the definition is not yet
complete.

### 3.3 What a model is, concretely

> **Lemma 3.3** `[conjecture]`**.** Unfolding Definition 1.3 along the slots of
> `Ξ`, a model of `(Ξ, 𝒫)` is exactly: for each slot `x` of `Ξ`, taken in order
> and writing `D_x := ⟦Ξ.binding x⟧_M`,
>
> ```text
> x : sort     a dependent presheaf over D_x
> x : of S     a section of ⟦S⟧_M over D_x
> x : eq l r   the requirement that ⟦l⟧_M = ⟦r⟧_M
> ```
>
> subject to the local-representability condition of 3.1.

This is immediate from Definition 1.3, `J(Ξ)` being an iterated `Σ` with one
factor per slot of `Ξ`; the content is in Proposition 1.3.1, that `J` is
well defined.

---

## 4. Why these are the right notions

### 4.1 What would count as correct

Three tests, in increasing strength.

```text
not too many   soundness: Γ ⊢ e ≈ e′ must give equal interpretations
not too few    the syntax must be a model of itself
exactly right  the classification: models are exactly the slotwise data
```

Soundness is not an obligation on Definition 3.1 at all: `𝒯` is quotiented, so
derivably equal expressions are a single arrow of `Ctx`, and `J` sends it
somewhere. It is an obligation on **1.3.1**, that `J` be well defined — which is
where the substitution lemma lives.

### 4.2 The empty-signature test

The sharpest single check, and the one that rules out the obvious alternative.

Take `Ξ = 𝟙` and any `𝒫`. Then `J(𝟙) = 1` and a global element of the terminal
presheaf is unique: **the empty theory has exactly one model.** As it must.

Compare the alternative of defining a model as a CwR morphism
`Ctx / Ξ ⟶ PSh(𝒞)`. Since `𝟙` is terminal in `Ctx`, `Ctx / 𝟙 ≃ Ctx`, and functors
out of `Ctx` are very far from unique — `Hom_{Ctx}(A, −)` preserves all limits and
is a CwR morphism when the representable classes are trivial, and taking `A` with
two sort slots makes it non-constant, distinguishing it from the constant functor.
So that definition classifies **an interpretation of the whole framework together
with an interpretation of `Ξ`**, not an interpretation of `Ξ`.

The root cause is worth naming: in this framework `sort` is a boundary
constructor available at *every* ambient, so `𝒯 𝟙` is already the whole of `Ctx`.
Uemura's `R(())` is a single object because a new sort can only come from a
declared symbol. Fixing `J` removes the difficulty at the source — the framework's
sorts are interpreted once, so a model chooses nothing about them.

### 4.3 Fixing `J` also forces the intended reading of binders

A second and independent reason to fix `J` rather than quantify over
interpretations of the framework.

Take untyped `λ`, with `lam : [ f : [x : of tm] of tm ] of tm`, and write
`Φ := [ f : [x : of tm] of tm ]` for its argument telescope. What is the object of
possible `f`s?

```text
full      ⟦Φ⟧ = T^T     every function from terms to terms
Henkin    ⟦Φ⟧ = B       a designated family of unary operations, with an evaluation map
```

Under Definition 1.3, `⟦Φ⟧` is **computed**: `Π_{⟦[x : of tm]⟧} ⟦of tm⟧ = T^T`.
The full reading, on the nose.

Had a model been a functor out of `Ctx / Ξ`, the answer would depend on `𝒫`. Such
a functor preserves pushforwards only along *representable* maps; `Φ` is the
pushforward of `of tm` along `p_x : Ξ_λ ⋈ [x : of tm] ⟶ Ξ_λ`; so unless
`[x : of tm] ∈ 𝒫`, nothing forces `⟦Φ⟧ ≅ T^T`, and `β` gives only
`app♯ ∘ ⟦lam⟧ = ev♯ : B ⟶ T^T`, which does not exhibit `T^T` as a retract of `T`.
One would obtain Henkin models — a real notion, but not the one intended, and one
that would have made the answer depend on a filter that has nothing to do with
binders.

### 4.4 Instances

*MLTT gives a natural model, i.e. a CwF.* By 3.3: `ty : sort` binds nothing, so
its datum is a presheaf `Ty`; `tm : [A : ty] sort` has `D_tm = Ty`, so its datum
is a dependent presheaf `Tm` over `Ty`; and `R_MLTT = { tm A }` makes 3.1's clause
say exactly that **`Tm ⟶ Ty` is representable** — Awodey's Def. 1. Note `Ty` is
*not* required representable, `ty ∉ R_MLTT`, which is correct: an MLTT context
cannot be extended by a type variable. Type formers come out in CwF form; for
`Π : [A : ty, B : [x : tm A] ty] ty` the telescope clause gives
`⟦[A, B]⟧ = Σ (A : Ty), Ty(− ⊲ A)`, the second factor by local representability,
so the datum is

```text
⟦Π⟧_Γ  :  (A : Ty Γ) → Ty (Γ ⊲ A) → Ty Γ
```

the CwF formation rule. `β` and `η`, being `eq` slots, give conditions — matching
that a CwF imposes them strictly.

*Monoids give monoids.* At `𝒞 = 1`, so presheaves are sets, `Ξ_mon` gives a set
`S`, an element `e`, a function `m : S × S ⟶ S` — the interpretation of
`[x : of M, y : of M]` being `S × S`, built by `Σ` alone since both slots bind
nothing — and three conditions. So `Mod_1(Ξ_mon, 𝒫)` is the monoids, with the
axioms appearing as *properties* rather than chosen proof data.

*Untyped `λ`.* By 4.3, `⟦lam⟧ : T^T ⟶ T` and `⟦app⟧ : T ⟶ T^T` with
`app ∘ lam = id`, so `T^T` is a retract of `T` — Scott's reflexive object.

### 4.5 Precedents

**Kaposi–Xie is this definition.** Their Def. 18 reads
`(𝒞 : Cat_⋄) × Tm_{PSh(𝒞)} ⋄ ⟦Ω⟧_{PSh(𝒞)}`, in two steps: their Problems 16–17
make `PSh(𝒞)` a model of the theory of signatures `ToS⁺`, uniformly in `𝒞` — that
is `J` — and a model is a **term** of `⟦Ω⟧` — that is the point. Their `U⁺`, the
sub-universe of sorts over which variables may be bound, interpreted by the
locally representable types, is `R`. Kaposi–Kovács do the same for QIITs: `–ᴬ`
interprets the theory of signatures in a fixed model, and an algebra is an element
of `Γᴬ`.

**Uemura takes the other route**, and is not a precedent for this shape: his
`R(Σ)` is built *freely from `Σ`*, so there is no framework-classifying category
to slice, and models are representable map functors out of `R(Σ)` (Def. 4.5). The
split is structural rather than a matter of taste:

```text
signatures as generators   Uemura, Lawvere     classifying category built freely from Σ
                                                models = functors out of it
signatures as objects      Kaposi, here        framework interpreted once
                                                models = points of ⟦Ξ⟧
```

This framework is a signatures-as-objects framework — a theory **is** an ambient,
an object of `Ctx` — so the point formulation is the one that fits. Adopting
Uemura's would mean giving that up.

**Cartmell** is the degenerate case. A GAT is first-order, every judgment is a
context, and models are lex functors into any lex category. Here that is the case
where no binder occurs: the telescope clause's `Π` is trivial, everything is built
by `Σ`, and the monoid instance of 4.4 is exactly Cartmell's functorial semantics.
What his notion cannot express is binding — `lam : (Tm → Tm) → Tm` is not a GAT
operation — which is the whole reason for `Π`, `𝒫`, and local representability.

### 4.6 What needs to be proven

```text
1.3.1  J is a well-defined functor              [conjecture] — the substance
3.2   the comparison J_𝒞 ⟶ F^* J_𝒟            [open] — universe coherence
3.3   the classification                        [conjecture] — expected easy
—     realization: every slotwise structure arises        [conjecture]
—     initiality of the syntactic model                   [open]
```

Freeness is not initiality, and soundness follows from 1.3.1 rather than standing
beside it. The one genuine gap in the *definition*, as opposed to the theory built
on it, is 3.2.

---

## References

```text
Lawvere              Functorial semantics of algebraic theories, thesis 1963
Cartmell             Generalised algebraic theories and contextual categories, APAL 32 (1986)
Gabriel & Ulmer      Lokal präsentierbare Kategorien, LNM 221 (1971)
Awodey               Natural models of homotopy type theory, MSCS 28(2), Def. 1
Hofmann & Streicher  Lifting Grothendieck universes
Uemura               A general framework for the semantics of type theory, arXiv:1904.04097
                       Def. 3.8, 4.2, 4.5, 4.14, 6.7, Thm. 5.17, Thm. 6.10, Prop. 3.21
Uemura               Abstract and Concrete Type Theories, thesis, Rem. 3.2.10–12, Def. 3.2.5
Kaposi & Xie         Second-order GATs: signatures and first-order semantics, FSCD 2024
                       Def. 4, Def. 18, Problems 16–17
Kaposi & Kovács      Signatures and induction principles for HIITs, LMCS 16(1:10)
Bocquet              Relative induction principles for SOGATs, thesis, §5.2
```
