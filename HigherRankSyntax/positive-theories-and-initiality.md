# Positive theories and initiality

This note fixes the definitions behind the next formalization passes and proves,
on paper, the result they aim at:

> **Main theorem (7.5).** For a positive theory `T`, the tautological model `𝒮_T`
> is an initial object of the category `Mod(T)` of models of `T`.

| § | content |
|---|---|
| 1 | the syntax `Ctx` and its initiality among HrS structures |
| 2 | presheaf semantics: the HrS structure `PSh(𝒞)`, points, extensions |
| 3 | theories, positivity |
| 4 | models of a positive theory |
| 5 | morphisms of models, the category `Mod(T)` |
| 6 | the tautological model `𝒮_T` |
| 7 | initiality of `𝒮_T` |
| 8 | status: what is in Lean, what the main theorem uses |
| A | morphisms as logical relations |

**Marks.** **[Lean]**: formalized, no `sorry`. **[routine]**: a componentwise
check, omitted. Everything else is proved here.

**Conventions.**

```text
Γ Δ Θ Ξ Ψ      contexts, telescopes, chains        σ θ κ        maps of Ctx (substitutions)
x y z          slots                               a b c        types
s t u          terms                               S            terms of U ("sorts")
𝒞 𝒟            base categories                     I J K        objects of 𝒞, 𝒟
f g h          maps of 𝒞, 𝒟                        ξ·f          restriction of an element ξ along f
```

---

## 1. The syntactic framework

### 1.1 HrS structures

An **HrS structure** `𝓜` is a category with families with five type formers,
each strictly stable under reindexing.

```text
contexts        a category 𝓜 with a terminal object ⋄
types, terms    Ty(Γ), Tm(Γ, a), with reindexing a[σ], t[σ]
extension       Γ.a, with  p : Γ.a → Γ  and  v ∈ Tm(Γ.a, a[p]),  such that
                  maps Δ → Γ.a   ≅   pairs (σ : Δ → Γ, t ∈ Tm(Δ, a[σ])),    written ⟨σ, t⟩

sorts           U ∈ Ty(Γ)
elements        El S ∈ Ty(Γ)                 for S ∈ Tm(Γ, U)
binding         Bind(a, c) ∈ Ty(Γ)           for a ∈ Ty(Γ), c ∈ Ty(Γ.a),   with
                  lam : Tm(Γ.a, c) ≅ Tm(Γ, Bind(a, c)) : unlam
sort equation   IdSort(S, S') ∈ Ty(Γ)        for S, S' ∈ Tm(Γ, U),   with
                  Tm(Γ, IdSort(S, S')) = {★} if S = S',  ∅ otherwise
element eq.     IdElement(l, r) ∈ Ty(Γ)      for l, r ∈ Tm(Γ, El S),   with
                  Tm(Γ, IdElement(l, r)) = {★} if l = r,  ∅ otherwise
```

The domain `a` of `Bind(a, c)` is arbitrary; it may be `U`. A **morphism** of HrS
structures is a functor with maps on types and terms preserving all of the above
on the nose.

**Notation.**

- `[b₁, …, b_k] c := Bind(b₁, Bind(b₂, … Bind(b_k, c)))`.
- **Application.** For `s ∈ Tm(Γ, Bind(a, c))` and `u ∈ Tm(Γ, a)`,
  `s u := unlam(s)[⟨id, u⟩] ∈ Tm(Γ, c[⟨id, u⟩])`. Iterated: `s ū = s u₁ … u_k`.
- **Chains.** A chain `Θ = (a₁, …, a_k)` over `Γ` is a list with
  `a_j ∈ Ty(Γ.a₁.….a_{j−1})`. Its extension is `Γ ▷ Θ := Γ.a₁.….a_k`, with
  projection `p_Θ : Γ ▷ Θ → Γ`. A map `Δ → Γ ▷ Θ` is a tuple `⟨σ, t₁, …, t_k⟩`.
  Chains are the telescopes of `𝓜` **[Lean: `HrS.Chain`]**.

### 1.2 The syntax `Ctx`

`Ctx` is the HrS structure of higher-rank syntax.

- A **context** is a list of **slots** `x : [B_x] β_x`. The **binder** `B_x` is a
  telescope over the preceding slots; `β_x` is one of four **atoms**:
  `sort`, `of S`, `S ≡ S'`, `l ≡ r`.
- An **expression** is a **slot application** `x(ū)`: a slot `x` of the context
  applied to arguments `ū` that fill its binder `B_x`.
- A **type** over `Γ` is a single entry `[Θ] β` over `Γ`: a telescope, then an
  atom.
- A **term** of `[Θ] β` is a filling over `Γ` extended by `Θ`. For `β = sort` or
  `β = of S`, it is an expression of that shape. For an equation atom, it is `★`,
  which exists exactly when the equation holds there.
- Everything is taken up to judgmental equality. Judgmental equality includes
  the equation slots: a slot `e : [B] l ≡ r` forces `l[ū] = r[ū]` for every `ū`
  filling `B`, and likewise for `S ≡ S'`.

The HrS operations are as follows.

```text
Γ.a                 Γ with one more slot, of type a
U                   [] sort
El S                [] of S
IdSort(S, S')       [] S ≡ S'
IdElement(l, r)     [] l ≡ r
Bind(a, [Θ] β)      [a, Θ] β
lam, unlam          identities on fillings
```

A slot `x` of `Γ` is itself a term `v_x ∈ Tm(Γ, [B_x] β_x)`, and
`x(ū) = v_x ū` (§1.1, application).

**Proposition 1.1 (shape of types)** **[Lean: `Ctx/Inversion.lean`]**. Every type
of `Ctx` is `[b₁, …, b_k] β` with `β ∈ {U, El S, IdSort(S, S'), IdElement(l, r)}`.
`Bind` is injective, and `Bind(a, c)` is never an atom. Hence the decomposition
is unique.

**Proposition 1.2 (atomic terms).** This holds by construction of the syntax.

- Every `S ∈ Tm(Γ, U)` is `y(ū)` for a slot `y : [B_y] sort` of `Γ`.
- Every `s ∈ Tm(Γ, El S)` is `x(ū)` for a slot `x : [B_x] of S_x` of `Γ`, with
  `S_x[ū] = S`.

**Theorem 1.3 (initiality of `Ctx`)** **[Lean: `Initiality/Initial.lean`]**. For every
HrS structure `𝓜` there is exactly one morphism `J_𝓜 : Ctx → 𝓜`.

### 1.3 Signatures and the slice over them

A **signature** is a context `Ξ`. Its slots fall into four kinds, by their atom:

| atom `β_x` | kind of slot `x` |
|---|---|
| `sort` | **sort slot** |
| `of S` | **operation slot** |
| `S ≡ S'` | **sort-equation slot** |
| `l ≡ r` | **element-equation slot** |

The **slot type** of `x` is `E_x := [B_x] β_x`, weakened to a type over `Ξ`
**[Lean: `Ctx.entry`]**.

`Ctx/Ξ` is the slice category **[Lean: Mathlib `Over Ξ`]**.

- An object is a pair `X = (Y, κ : Y → Ξ)`.
- A map `σ : (Y', κ') → (Y, κ)` is a map `σ : Y' → Y` with `κ ∘ σ = κ'`.
- For a type `a` over `Y`, `X.a := (Y.a, κ ∘ p)`.
- A **chain over `X`** is a chain over `Y`, read with these slice structures.
- For a chain `Θ` over `Ξ`, write `⌜Θ⌝ := (Ξ ▷ Θ, p_Θ)`.

**Example (untyped λ-terms).** This signature is formalized in
`Theory/Examples.lean`.

```text
Ξ_λ  =  tm  : sort,
        app : [f : of tm, a : of tm] of tm,
        lam : [b : [x : of tm] of tm] of tm

E_tm = U        E_app = [El tm, El tm] El tm        E_lam = [[El tm] El tm] El tm
```

---

## 2. Presheaf semantics

### 2.1 The presheaf model

Let `𝒞` be a small category. Presheaves on `𝒞` form an HrS structure `PSh(𝒞)`
**[Lean: `HrS/Presheaf/*.lean`]**. No assumption on `𝒞` is needed.

```text
contexts      presheaves Γ on 𝒞;  ⋄ is the one-point presheaf
types         A ∈ Ty(Γ): sets A(I, ξ) for ξ ∈ Γ(I), with restrictions A(I, ξ) → A(J, ξ·f)
terms         t ∈ Tm(Γ, A): elements t(ξ) ∈ A(I, ξ), natural in I
Γ.A           (Γ.A)(I) = { (ξ, x) | ξ ∈ Γ(I), x ∈ A(I, ξ) }
U             U(I, ξ) = presheaves on the slice 𝒞/I
El S          (El S)(I, ξ) = S(ξ)(id_I)
Bind(A, C)    Bind(A, C)(I, ξ) = families  b(f, x) ∈ C(J, (ξ·f, x))
                for f : J → I and x ∈ A(J, ξ·f),   natural:  b(f, x)·g = b(f∘g, x·g)
IdSort(S, S')     IdSort(S, S')(I, ξ) = {★ | S(ξ) = S'(ξ)}
IdElement(l, r)   IdElement(l, r)(I, ξ) = {★ | l(ξ) = r(ξ)}
```

- Restriction in `U` along `f : J → I` precomposes with
  `𝒞/J → 𝒞/I, (K, g) ↦ (K, f∘g)`.
- `lam(t)(ξ)(f, x) = t(ξ·f, x)` and `unlam(b)(ξ, x) = b(ξ)(id_I, x)`. Hence
  application is evaluation at the identity: `(s u)(ξ) = s(ξ)(id_I, u(ξ))`.

**Interpretation.** `J_𝒞 : Ctx → PSh(𝒞)` is the unique morphism of Theorem 1.3
**[Lean: `Presheaf.interpretation`]**. Write `⟦Γ⟧, ⟦a⟧, ⟦t⟧, ⟦σ⟧`. Strict
preservation gives:

```text
⟦Γ.a⟧(I)       = { (ξ, x) | ξ ∈ ⟦Γ⟧(I), x ∈ ⟦a⟧(I, ξ) }
⟦a[σ]⟧(I, ξ)   = ⟦a⟧(I, ⟦σ⟧ξ)              ⟦t[σ]⟧(ξ) = ⟦t⟧(⟦σ⟧ξ)
⟦El S⟧(I, ξ)   = ⟦S⟧(ξ)(id_I)
⟦s u⟧(ξ)       = ⟦s⟧(ξ)(id_I, ⟦u⟧ξ)
```

An element `m ∈ ⟦Ξ⟧(I)` is a tuple `(m_x)` over the slots of `Ξ`, with
`m_x ∈ ⟦E_x⟧(I, m)`. A slot application is interpreted by applying the slot's
component: `⟦x(ū)⟧(m) = m_x ⟦ū⟧(m)`.

### 2.2 Points over a global element

From here on `𝒞` has a terminal object `1`. Write `!_I : I → 1`. A **global
element** of `⟦Ξ⟧` is an `M ∈ ⟦Ξ⟧(1)`. Write `M_I := M·!_I`.

**Definition 2.1 (points).** Let `X = (Y, κ) ∈ Ctx/Ξ`. The presheaf of **points
of `X` over `M`** is the subpresheaf of `⟦Y⟧` given by

```text
⟦X⟧_M(I)  :=  { γ ∈ ⟦Y⟧(I) | ⟦κ⟧(γ) = M_I }.
```

- A slice map `σ : X' → X` restricts to `⟦σ⟧ : ⟦X'⟧_M → ⟦X⟧_M`.
- For a chain `Θ = (a₁, …, a_k)` over `Ξ`, write `⟦Θ⟧_M := ⟦⌜Θ⌝⟧_M`. Its points
  at `I` are the tuples `(M_I, x₁, …, x_k)` with
  `x_j ∈ ⟦a_j⟧(I, (M_I, x₁, …, x_{j−1}))`.
- The empty chain has exactly one point at each stage: `M_I`.

### 2.3 Extensions

**Definition 2.2 (extension).** Let `γ ∈ ⟦Y⟧(I)` and `a ∈ Ty(Y)`. An **extension
of `I` by `a` at `γ`** consists of:

- an object `I ⊲_γ a`;
- a map `p : I ⊲_γ a → I`;
- an element `v ∈ ⟦a⟧(I ⊲_γ a, γ·p)`.

It is required that for every `f : J → I` and `x ∈ ⟦a⟧(J, γ·f)` there is exactly
one map `⟨f, x⟩ : J → I ⊲_γ a` with `p ∘ ⟨f, x⟩ = f` and `v·⟨f, x⟩ = x`.

Equivalently, the dependent presheaf `⟦a⟧`, pulled back along `γ : y(I) → ⟦Y⟧`,
is representable over `y(I)`. This is the local representability of
`semantics.md`, Def. 1.1.

- `⟨f, x⟩ ∘ g = ⟨f∘g, x·g⟩`, by uniqueness.
- `(γ·p, v) ∈ ⟦Y.a⟧(I ⊲_γ a)` is the **generic point** of the extension.

**Lemma 2.3 (binding over an extension).** Let `(I ⊲_γ a, p, v)` be an extension
of `I` by `a` at `γ`, and let `c ∈ Ty(Y.a)`. Then the following map is a
bijection:

```text
⟦Bind(a, c)⟧(I, γ)  ⟶  ⟦c⟧(I ⊲_γ a, (γ·p, v)),        b  ↦  b(p, v).
```

Its inverse sends `c₀` to the family `(f, x) ↦ c₀·⟨f, x⟩`.

*Proof.* Let `b` be in the domain. By naturality of `b`,
`b(f, x) = b(p ∘ ⟨f, x⟩, v·⟨f, x⟩) = b(p, v)·⟨f, x⟩`. So `b` is determined by
`b(p, v)`.

Conversely, the family `(f, x) ↦ c₀·⟨f, x⟩` is natural because
`⟨f, x⟩ ∘ g = ⟨f∘g, x·g⟩`. Its value at `(p, v)` is `c₀·⟨p, v⟩ = c₀·id = c₀`. ∎

So over an extension, an element of `[a] c` at `I` is just an element of `c` at
`I ⊲_γ a`. Without an extension, an element of `⟦Bind(a, c)⟧(I, γ)` is a family
over all stages `J → I`, and no single stage controls it. Positivity (§3)
restricts binders to the types that have extensions.

---

## 3. Theories and positivity

### 3.1 Theories

**Definition 3.1 (theory)** **[Lean: `Theory`]**. A **theory** `T` consists of:

- a signature `Ξ`;
- for each `X = (Y, κ) ∈ Ctx/Ξ`, a set `Adm(X) ⊆ Ty(Y)` of **admissible** types.

It is required that `a ∈ Adm(X)` and a slice map `σ : X' → X` give
`a[σ] ∈ Adm(X')`.

The admissible types are the types by which a model must be able to extend its
stages (Def. 4.1). Stability says that an instance of an admissible type is
admissible.

**Schemas** **[Lean: `Theory.Schema`, `Theory.ofSchemas`]**. A **schema** is a pair
`(X, a)` with `X = (Y, κ) ∈ Ctx/Ξ` and `a ∈ Ty(Y)`. A family of schemas `(X_i, a_i)_{i ∈ ι}`, with `ι`
arbitrary, generates the theory with

```text
Adm(X)  =  { a_i[σ] | i ∈ ι,  σ : X → X_i  in Ctx/Ξ }.
```

**Admissible chains** **[Lean: `Theory.AdmissibleChain`]**. A chain
`Θ = (a₁, …, a_k)` over `X` is **admissible** when
`a_j ∈ Adm(X.a₁.….a_{j−1})` for every `j`.

### 3.2 Positivity

**Definition 3.2 (positive types, positive binders)** **[Lean:
`Theory.PositiveEntry`, `Theory.PositiveBinding`]**. Fix a theory `T`. For
`X ∈ Ctx/Ξ`, the sets `Pos(X)` of **positive** types and `PB(X)` of types **with
positive binders** are defined inductively:

```text
(P1)   El S ∈ Pos(X)
(P2)   IdElement(l, r) ∈ Pos(X)
(P3)   a ∈ Adm(X),   a ∈ Pos(X),   c ∈ Pos(X.a)    ⟹    Bind(a, c) ∈ Pos(X)

(B1)   U,  El S,  IdSort(S, S'),  IdElement(l, r)  ∈ PB(X)
(B2)   a ∈ Pos(X),   c ∈ PB(X.a)                   ⟹    Bind(a, c) ∈ PB(X)
```

Prop. 1.1 turns these into conditions on the normal form `a = [b₁, …, b_k] β`.
Write `X_j := X.b₁.….b_{j−1}`.

- `a ∈ Pos(X)` iff `β ∈ {El S, IdElement(l, r)}` and every
  `b_j ∈ Adm(X_j) ∩ Pos(X_j)`.
- `a ∈ PB(X)` iff every `b_j ∈ Pos(X_j)`.

**Definition 3.3 (positive theory)** **[Lean: `Theory.Positive`]**. `T` is
**positive** when both of the following hold.

- (i) Every slot type has positive binders: `E_x ∈ PB(Ξ, id)` for every slot `x`
  of `Ξ`.
- (ii) Every admissible type is positive: `Adm(X) ⊆ Pos(X)` for every `X`.

A chain is **positive** when each entry is positive over the extension by the
entries before it **[Lean: `Theory.PositiveChain`]**. By (i), the binder `B_x` of
every slot is a positive chain over `Ξ`.

**Lemma 3.4** **[Lean: (a)–(d), `Theory/Positive.lean`]**.

- (a) If `Bind(a, c) ∈ Pos(X)`, then `a ∈ Adm(X) ∩ Pos(X)` and `c ∈ Pos(X.a)`.
- (b) If `Bind(a, c) ∈ PB(X)`, then `a ∈ Pos(X)` and `c ∈ PB(X.a)`.
- (c) `U ∉ Pos(X)` and `IdSort(S, S') ∉ Pos(X)`.
- (d) In a positive theory, every admissible chain is positive.
- (e) If `a ∈ Pos(X)` and `σ : X' → X` is a slice map, then `a[σ] ∈ Pos(X')`.

*Proof of (e).* Induction on `a ∈ Pos(X)`. Substitution commutes with `El` and
`IdElement`, and `Bind(b, c)[σ] = Bind(b[σ], c[σ⁺])` with
`σ⁺ := ⟨σ∘p, v⟩ : X'.b[σ] → X.b`. Here `b[σ] ∈ Adm(X')` by stability of `Adm`. ∎

**Lemma 3.5 (no sort variables in positive chains).** Let `Δ` be a positive chain
over `Ξ`.

- (a) Every `S ∈ Tm(Ξ ▷ Δ, U)` is `y(ū)` for a sort slot `y` of `Ξ` and a map
  `ū : ⌜Δ⌝ → ⌜B_y⌝` of `Ctx/Ξ`.
- (b) Every `s ∈ Tm(Ξ ▷ Δ, El S)` is `x(ū)` for `x` either an operation slot of
  `Ξ` or an entry of `Δ`.

*Proof.* The slots of `Ξ ▷ Δ` are the slots of `Ξ` and the entries of `Δ`. An
entry of `Δ` has a positive type, whose atom is `El` or `IdElement` (Def. 3.2). So
no entry of `Δ` is a sort slot. Now apply Prop. 1.2. ∎

### 3.3 Examples

**Positive theories.**

| theory | signature | generating schemas |
|---|---|---|
| untyped λ-terms | `Ξ_λ` (§1.3) | `((Ξ_λ, id), El tm)` |
| monoids | `mon : sort,  e : of mon,  mul : [x y : of mon] of mon`, three element-equation slots | `((Ξ, id), El mon)`, or none |
| dependent types with Π | `Ty : sort,  Tm : [A : of Ty] sort,  Pi : [A : of Ty, B : [x : of Tm(A)] of Ty] of Ty`, `lam`, `app`, and element-equation slots for β and η | `((Ξ.El Ty, p), El Tm(A))` |

In each case the binders are `El`-types, or `Bind`s over admissible `El`-types:

- `lam`'s binder `[El tm] El tm` is positive by (P3), because `El tm` is
  admissible.
- `Pi`'s binder `[El Tm(A)] El Ty` is positive by (P3), because `El Tm(A)` is
  admissible.

**Theories that are not positive.**

| slot or choice | violates |
|---|---|
| `Ξ_λ` with no schemas | `[El tm] El tm ∉ Pos`: `El tm` is not admissible |
| `all : [b : [X : sort] of tm] of tm` | `U ∉ Pos`: no binder may range over sorts |
| `cast : [A B : of Ty, e : Tm(A) ≡ Tm(B), u : of Tm(A)] of Tm(B)` | `IdSort ∉ Pos` |
| a schema `(X, U)` | (ii): `U` is never positive |

Positivity constrains only the binders. The atom of a slot, its result, can be
anything (B1).

---

## 4. Models

Fix a positive theory `T` with signature `Ξ`.

**Definition 4.1 (model).** A **model** `𝒮 = (𝒞, 1, M, ⊲)` of `T` consists of
four pieces of data.

- **(M1)** A small category `𝒞` with a chosen terminal object `1`.
- **(M2)** A global element `M ∈ ⟦Ξ⟧(1)`, the interpretation of the signature.
- **(M3)** Chosen extensions. For every positive chain `Δ` over `Ξ`, every point
  `γ ∈ ⟦Δ⟧_M(I)` and every `a ∈ Adm(⌜Δ⌝)`, a chosen extension
  `(I ⊲_γ a, p, v)` of `I` by `a` at `γ` (Def. 2.2).
- **(M4)** Stability. Let `Δ, Δ'` be positive chains over `Ξ`, let
  `σ : ⌜Δ'⌝ → ⌜Δ⌝` be a slice map, and let `γ' ∈ ⟦Δ'⟧_M(I)` and
  `a ∈ Adm(⌜Δ⌝)`. Then
  ```text
  I ⊲_{γ'} a[σ]  =  I ⊲_{⟦σ⟧γ'} a,        with the same p and v.
  ```

Both sides of (M4) are defined:

- `a[σ] ∈ Adm(⌜Δ'⌝)` by stability of `Adm`.
- `⟦a[σ]⟧(J, γ'·f) = ⟦a⟧(J, ⟦σ⟧γ'·f)`. So both sides extend `I` by the same
  dependent presheaf over `y(I)`.

**Remarks.**

- *Why extensions at points of positive chains.*
  - (ext) (Def. 5.2) compares the extension at `γ` with the extension at `φγ`,
    and a morphism `φ` acts on the points of positive chains.
  - The chains must include non-admissible ones. Example: a slot
    `g : [x : of s₁, b : [y : of s₂(x)] of s₃] of s₄`, with `El s₂(x)` admissible
    over `Ξ.El s₁` but `El s₁` not admissible. For Prop. 5.3 at the argument
    `b`, Lemma 2.3 is needed at points of the chain `(El s₁)`.
- *Why (M4).*
  - The tautological model has stable extensions (§6).
  - A morphism out of it forces (M4) on the target at the target's generic points
    (see the proof of Prop. 7.3).
  - In the dependent-types example, `El Tm(t) = El Tm(A)[⟨p, t⟩]`. So (M4) gives
    `I ⊲_γ El Tm(t) = I ⊲_{(M_I, ⟦t⟧γ)} El Tm(A)`. The extension depends only on
    the semantic type `⟦t⟧γ ∈ ⟦Ty⟧(I)`, exactly as comprehension does in a CwF.
- *Why `1`.* It is the stage of the empty chain. Morphisms preserve it (Def. 5.2),
  and the construction of §7 starts from it.

**The data of `M`, slot by slot.** Take the slots of `Ξ` in order. Write `x(v̄)`
for a slot `x` applied to the variables of its binder, and let
`β ∈ ⟦B_x⟧_M(I)`.

- For a sort slot `y`, `M_y(β) := ⟦El y(v̄)⟧(I, β)` is the set of elements of
  sort `y` at the arguments `β`.
- For an operation slot `f`, `M_f(β) := ⟦f(v̄)⟧(β)`.

**[routine]** By Yoneda for `U`, `M` amounts to the following.

| slot | data |
|---|---|
| `y : [B_y] sort` | a dependent presheaf `M_y` over `⟦B_y⟧_M`, with restrictions `M_y(β) → M_y(β·f)` |
| `f : [B_f] of S` | elements `M_f(β) ∈ ⟦El S⟧(I, β)`, natural in `I` |
| `e : [B_e] l ≡ r` | the equation `⟦l⟧(β) = ⟦r⟧(β)` for all `β` |
| `e : [B_e] S ≡ S'` | the equation `⟦S⟧(β) = ⟦S'⟧(β)` for all `β` |

Where `B_x` binds an admissible type, Lemma 2.3 turns the corresponding argument
into an element at an extension.

**Examples.**

- **Untyped λ-terms.**
  - Every admissible type is `El tm[κ]`. So by (M4) all extensions are
    `I ⊲ tm := I ⊲_{M_I} El tm`.
  - A model is a category `𝒞` with `1`, a presheaf `Tm`, and representations
    `y(I ⊲ tm) ≅ y(I) × Tm` over `y(I)`.
  - It also has operations `app : Tm × Tm → Tm` and `lam_I : Tm(I ⊲ tm) → Tm(I)`
    (Lemma 2.3), natural in `I`.
- **Monoids, with `El mon` admissible.**
  - The presheaf `M_mon` is represented by `N₀ := 1 ⊲ mon`, and
    `I ⊲ mon = I × N₀`.
  - A model is a category with `1`, an object `N₀` with chosen products
    `I × N₀`, and a monoid structure on `N₀`.
- **Dependent types with Π.**
  - The data are presheaves `Ty`, `Tm` over `Ty`, and comprehension `I ⊲ A` for
    `A ∈ Ty(I)`.
  - There are also `Pi_I(A, B) ∈ Ty(I)` for `B ∈ Ty(I ⊲ A)` (Lemma 2.3), together
    with `lam`, `app`, β and η. This is a CwF with Π-types.

---

## 5. Morphisms and the category `Mod(T)`

A morphism of models is a functor between the base categories, together with a
map from the points over `M` to the points over `N`. The map is natural in the
chain and in the stage, and it preserves the chosen extensions.

### 5.1 The functor of points

**Definition 5.1.** `P_T` is the full subcategory of `Ctx/Ξ` on the objects
`⌜Δ⌝`, for `Δ` a positive chain over `Ξ`. A model `𝒮 = (𝒞, 1, M, ⊲)` has the
**functor of points**

```text
⟦-⟧_M : P_T → PSh(𝒞),        ⌜Δ⌝ ↦ ⟦Δ⟧_M,        σ ↦ ⟦σ⟧.
```

It is well defined because slice maps preserve points (Def. 2.1).

### 5.2 Morphisms

Let `𝒮 = (𝒞, 1, M, ⊲)` and `𝒮' = (𝒟, 1, N, ⊲)` be models. For a functor
`F : 𝒞 → 𝒟` and a presheaf `Q` on `𝒟`, write `F*Q := Q ∘ F^op`, so that
`(F*Q)(I) = Q(FI)`.

**Definition 5.2 (morphism).** A **morphism** `(F, φ) : 𝒮 → 𝒮'` consists of:

- a functor `F : 𝒞 → 𝒟` with `F1 = 1`;
- a natural transformation `φ : ⟦-⟧_M ⇒ F*⟦-⟧_N` of functors `P_T → PSh(𝒞)`.

It must satisfy **(ext)**: for every positive chain `Δ`, every
`γ ∈ ⟦Δ⟧_M(I)` and every `a ∈ Adm(⌜Δ⌝)`,

```text
F(I ⊲_γ a) = FI ⊲_{φγ} a,        F(p) = p,        φ(γ·p, v) = ((φγ)·p, v).
```

In the last equation, `(γ·p, v)` is a point of `Δ.a`, which is positive by
Def. 3.3 (ii).

**Unpacking.** `φ` consists of maps `φ : ⟦Δ⟧_M(I) → ⟦Δ⟧_N(FI)`, one for each
positive chain `Δ` and each `I ∈ 𝒞`, such that

```text
(nat-I)   φ(γ·f) = (φγ)·Ff            for f : J → I in 𝒞
(nat-Δ)   φ(⟦σ⟧γ) = ⟦σ⟧(φγ)           for σ : ⌜Δ⌝ → ⌜Δ'⌝ in P_T
```

Three instances of (nat-Δ) are used throughout.

- **Projections** `p : ⌜Δ.a⌝ → ⌜Δ⌝`. They give `φ(γ, x) = (φγ, φx)` for a map
  `x ↦ φx` from `⟦a⟧(I, γ)` to `⟦a⟧(FI, φγ)`. In this notation, the last
  equation of (ext) reads `φv = v`.
- **Sections** `⟨id, t⟩ : ⌜Δ⌝ → ⌜Δ.a⌝`, for `t ∈ Tm(Ξ ▷ Δ, a)` with `a`
  positive. They give `φ(⟦t⟧γ) = ⟦t⟧(φγ)`.
- **The empty chain.** It has the single point `M_I`, so `φ(M_I) = N_{FI}`.

### 5.3 Morphisms slot by slot

For a sort slot `y`, the chain `B_y.El y(v̄)` is positive: `B_y` by
Def. 3.3 (i), and `El y(v̄)` by (P1). Its points are the pairs `(β, x)` with
`β ∈ ⟦B_y⟧_M(I)` and `x ∈ M_y(β)` (§4). Write

```text
φ_y : M_y(β) → N_y(φβ)
```

for the action of `φ` on its last entry.

**Proposition 5.3 (morphisms slot by slot).** Let `(F, φ)` be a morphism.

- **(a)** `φ` is determined by `F` and the maps `φ_y`. Precisely, let `Δ` be a
  positive chain, `γ ∈ ⟦Δ⟧_M(I)`, `a ∈ Pos(⌜Δ⌝)` and `x ∈ ⟦a⟧(I, γ)`. Then:

  | `a` | `φx` |
  |---|---|
  | `El S`, with `S = y(ū)` (Lemma 3.5) | `φ_y(x)`, for `x ∈ ⟦El S⟧(I, γ) = M_y(⟦ū⟧γ)` |
  | `IdElement(l, r)` | `★` |
  | `Bind(b, c)` | the element that Lemma 2.3 assigns, at the extension `FI ⊲_{φγ} b = F(I ⊲_γ b)`, to `φ(x(p, v))` |

- **(b)** The maps `φ_y` commute with the operations and respect the sort
  equations:
  ```text
  (op)     φ(M_f(β)) = N_f(φβ)                for an operation slot f
  (sort)   φ_y at ⟦ū⟧β  =  φ_z at ⟦ū'⟧β        for a sort-equation slot e : [B_e] y(ū) ≡ z(ū')
  ```
  By (a), the left side of (op) is a value of `φ_y`, for the sort slot `y` that
  heads the sort of `f`.

*Proof of (a).*

- *`El S`.* The map `ū⁺ := ⟨ū∘p, v⟩ : ⌜Δ.El S⌝ → ⌜B_y.El y(v̄)⌝` is a map of
  `P_T`, and `⟦ū⁺⟧(γ, x) = (⟦ū⟧γ, x)`. Apply (nat-Δ) along `ū⁺` and compare
  last entries.
- *`IdElement`.* `⟦a⟧(FI, φγ)` has at most one element.
- *`Bind(b, c)`.* Let `ε : ⌜Δ.Bind(b, c).b[p]⌝ → ⌜Δ.b.c⌝` be the slice map with
  `⟦ε⟧(γ, x, z) = (γ, z, x(id, z))`. It exists because application is
  evaluation at the identity (§2.1). Both chains are positive, by
  Lemma 3.4 (a) and (e).
  1. Apply (nat-Δ) along `ε` and compare last entries. This gives
     `φ(x(id, z)) = (φx)(id, φz)`.
  2. Take the stage `I ⊲_γ b`, the element `x·p` and `z = v`. By (nat-I),
     `F(p) = p` and `φv = v`:
     ```text
     φ(x(p, v))  =  φ((x·p)(id, v))  =  (φ(x·p))(id, φv)  =  ((φx)·p)(id, v)  =  (φx)(p, v).
     ```
  3. By (ext), `FI ⊲_{φγ} b` is an extension of `FI` by `b` at `φγ`. So, by
     Lemma 2.3 in `𝒟`, `φx` is determined by `(φx)(p, v)`.

*Proof of (b).*

- *(op).* Apply (nat-Δ) along the section `⟨id, f(v̄)⟩ : ⌜B_f⌝ → ⌜B_f.El S⌝`.
  Here `M_f(β) = ⟦f(v̄)⟧β` and `N_f(φβ) = ⟦f(v̄)⟧(φβ)`.
- *(sort).* The slot `e` makes `y(ū) = z(ū')` over `⌜B_e⌝`. So `B_e.El y(ū)`
  and `B_e.El z(ū')` are one object of `P_T`; apply (a) to it twice. ∎

So a morphism is determined by a functor that preserves `1` and the chosen
extensions, together with maps `φ_y` between the sorts; these maps commute with
the operations.

### 5.4 The category of models

**Definition 5.4 (identities, composition).** Let `(F, φ) : 𝒮 → 𝒮'` and
`(G, ψ) : 𝒮' → 𝒮''` be morphisms, with `𝒮'' = (ℰ, 1, L, ⊲)`.

```text
id_𝒮             :=  (id_𝒞, id)
(G, ψ) ∘ (F, φ)  :=  (G ∘ F, ψ ∘ φ),        (ψ ∘ φ)(γ) := ψ(φγ)
```

The composite is a morphism.

- *Naturality.* `ψ ∘ φ : ⟦-⟧_M ⇒ F*⟦-⟧_N ⇒ F*G*⟦-⟧_L` is natural, and
  `F*G* = (GF)*`.
- *(ext).* We have
  - `GF(I ⊲_γ a) = G(FI ⊲_{φγ} a) = GFI ⊲_{ψφγ} a`;
  - `GF(p) = p`;
  - `ψφ(γ·p, v) = ψ((φγ)·p, v) = ((ψφγ)·p, v)`.

**Theorem 5.5.** Models of `T` and their morphisms form a category `Mod(T)`.

*Proof.* Composition is associative and unital, because composition of functors
and of natural transformations is. ∎

### 5.5 Where positivity enters

- Def. 5.2 and Thm. 5.5 use only clause (ii) of Def. 3.3, which makes (ext) well
  typed.
- Clause (i) puts every binder `B_x` into `P_T`, so that Prop. 5.3 applies at
  every slot.
- In §6, positivity makes every point of a positive chain over the term model
  syntactic (Prop. 6.2). §7 rests on that.

**Remark 5.6 (why positive chains).** A morphism acts on the points of positive
chains only. On a chain built with an excluded former, the action cannot be
required. Take `𝒞 = 𝒟 = 1`, `F = id`, and the signature `y, z : sort` with no
admissible types. Then the action fails to exist or to be unique:

| chain | models and maps `φ_y`, `φ_z` | failure |
|---|---|---|
| `(U)` | `𝒮 = 𝒮'`, the identity | `φ` would send sorts to sorts, constrained only at the sorts `y`, `z`; it could swap two other sorts. Not unique |
| `(IdSort(y, z))` | `M_y = M_z = 1`; `N_y = 1`, `N_z = 2`; any maps | `★` is a point over `M`, and there is none over `N`. No `φ` |
| `([El y] El z)` | `M_y = M_z = ∅`; `N_y = 1`, `N_z = ∅`; the empty maps | the chain has the point `∅^∅ = 1` over `M`, and none over `N`, since `∅^1 = ∅`. No `φ` |

---

## 6. The tautological model

Fix a positive theory `T`.

### 6.1 The base category

**Definition 6.1.** `𝒞_T` is the full subcategory of `Ctx/Ξ` on the objects
`⌜Θ⌝`, for `Θ` an admissible chain over `Ξ`.

- A map `Θ' → Θ` is a slice map `⌜Θ'⌝ → ⌜Θ⌝`, a substitution that is the identity
  on `Ξ`.
- The empty chain is terminal, because `⌜[]⌝ = (Ξ, id)`.
- By Lemma 3.4 (d), `𝒞_T` is a full subcategory of `P_T`.

For a positive chain `Δ`, write `P(Θ, Δ) := Hom_{Ctx/Ξ}(⌜Θ⌝, ⌜Δ⌝)`. This is a
presheaf in `Θ ∈ 𝒞_T` by precomposition, and a functor in `Δ ∈ P_T` by
postcomposition.

### 6.2 The tautological point

**Proposition 6.2 (tautological point).** There are two pieces of data:

- a global element `M_T` of `⟦Ξ⟧` in `PSh(𝒞_T)`;
- for every positive chain `Δ` over `Ξ`, a bijection
  ```text
  ev : P(Θ, Δ)  ≅  ⟦Δ⟧_{M_T}(Θ),
  ```
  natural in `Θ` and in `Δ`. That is, `ev(θ ∘ f) = (ev θ)·f` and
  `ev(σ ∘ θ) = ⟦σ⟧(ev θ)`.

They satisfy the following.

- **(a) Pairs.** `ev⟨θ, t⟩ = (ev θ, ev t)`. Here, for `a` positive over `⌜Δ⌝`,
  `ev : Tm(Ξ ▷ Θ, a[θ]) ≅ ⟦a⟧(Θ, ev θ)` is described in (b)–(d).
- **(b) `El`.** For a sort `S` over `⌜Δ⌝`, the presheaf `⟦S⟧(ev θ)` on `𝒞_T/Θ`
  is
  ```text
  Syn(S[θ]) :  (f : Θ' → Θ)  ↦  Tm(Ξ ▷ Θ', El S[θ∘f]),        restriction = substitution.
  ```
  In particular `⟦El S⟧(Θ, ev θ) = Tm(Ξ ▷ Θ, El S[θ])`, and `ev` is the identity
  on `El`-types.
- **(c) `IdElement`.** `ev ★ = ★`.
- **(d) `Bind`.** Let `a = Bind(b, c)`, with `b` admissible. Then `Θ.b[θ]` is an
  admissible chain. With its projection and with `v := ev(v_b)`, it is an
  extension of `Θ` by `b` at `ev θ`. `ev t` is the element that Lemma 2.3 assigns
  to `ev(unlam t) ∈ ⟦c⟧(Θ.b[θ], (ev θ·p, v))`.
- **(e) Slots.**
  - For a sort slot, `M_{T,y}(ev ū) = Tm(Ξ ▷ Θ, El y(ū))`.
  - For an operation slot, `M_{T,f}(ev ū) = f(ū)`.

*Proof.* Proceed along the slots of `Ξ`; at each slot only the earlier slots are
involved, and this bookkeeping is suppressed. For each slot, argue by
simultaneous induction on chains, positive types and expressions.

- **Slot components (e).**
  - *Sort slot `y`.* Its binder `B_y` is a positive chain over earlier slots, so
    `ev` is a bijection on it. Define `M_{T,y}(ev ū) := Tm(Ξ ▷ Θ, El y(ū))`,
    restricted by substitution. By Yoneda for `U`, this determines the
    component.
  - *Operation slot `f : [B_f] of S`.* Put `M_{T,f}(ev ū) := f(ū)`. This lies in
    `⟦El S⟧(Θ, ev ū)` by (b).
  - *Equation slot `l ≡ r`.* `l[ū] = r[ū]` in `Ctx`, so
    `⟦l⟧(ev ū) = ev(l[ū]) = ev(r[ū]) = ⟦r⟧(ev ū)` by the term clause below.
    Sort equations work the same way, by (b).
- **Chains.**
  - *Empty chain.* `P(Θ, []) = {p_Θ}`, and `⟦[]⟧_{M_T}(Θ) = {M_{T,Θ}}`.
  - *`Δ.a`.* The maps `⌜Θ⌝ → ⌜Δ.a⌝` are the pairs `⟨θ, t⟩` with
    `t ∈ Tm(Ξ ▷ Θ, a[θ])`. Use (a) and the bijection on `a`.
- **Positive types.**
  - *`El S`.* By Lemma 3.5, `S = y(ū)`. Then
    ```text
    ⟦El S⟧(Θ, ev θ) = M_{T,y}(⟦ū⟧(ev θ)) = M_{T,y}(ev(ū∘θ)) = Tm(Ξ ▷ Θ, El S[θ]).
    ```
    The same computation at every `f : Θ' → Θ` gives (b).
  - *`IdElement(l, r)`.* Both sides are `{★}` exactly when `l[θ] = r[θ]`, that
    is, when `⟦l⟧(ev θ) = ⟦r⟧(ev θ)`.
  - *`Bind(b, c)`.* Since `b[θ] ∈ Adm(⌜Θ⌝)`, `Θ.b[θ]` is an object of `𝒞_T`. Maps
    `Θ' → Θ.b[θ]` over `f` are the `⟨f, u⟩` with `u ∈ Tm(Ξ ▷ Θ', b[θ∘f])`. By
    the induction hypothesis for `b`, `ev` matches these with
    `⟦b⟧(Θ', (ev θ)·f)`. So `Θ.b[θ]` is an extension. Then
    ```text
    Tm(Ξ ▷ Θ, Bind(b, c)[θ])  ≅  Tm(Ξ ▷ Θ.b[θ], c[θ⁺])         unlam
                              ≅  ⟦c⟧(Θ.b[θ], (ev θ·p, v))      induction hypothesis for c
                              ≅  ⟦Bind(b, c)⟧(Θ, ev θ)          Lemma 2.3
    ```
- **Terms.** `⟦t⟧(ev θ) = ev(t[θ])`, by induction on `t`. With chains and
  Lemma 3.4 (e), this gives naturality in `Δ`.
  - *Operation slot of `Ξ`.*
    `⟦f(ū)⟧(ev θ) = M_{T,f}(ev(ū∘θ)) = f(ū∘θ)`.
  - *Entry `x` of `Δ`.* `⟦x(ū)⟧(ev θ)` is `ev(θ_x)` applied at the identity to
    `ev(ū∘θ)`. By (d), this is `ev(θ_x (ū∘θ))`.
  - *`lam`, `★`.* These follow from (d) and (c).
- **Naturality in `Θ`.** Restriction along `f` matches substitution by `f` in
  each clause **[routine]**. ∎

### 6.3 The model

**Definition 6.3 (extensions of `𝒮_T`).** Let `Δ` be a positive chain. By
Prop. 6.2, every point of `Δ` at `Θ` is `ev θ` for a unique `θ`. For
`a ∈ Adm(⌜Δ⌝)`, set

```text
Θ ⊲_{ev θ} a  :=  Θ.a[θ],        with p the projection and v := ev(v_a).
```

This is an extension, by the `Bind`-case of the proof of Prop. 6.2.

**Theorem 6.4.** `𝒮_T := (𝒞_T, [], M_T, ⊲)` is a model of `T`.

*Proof.* (M1)–(M3) are Def. 6.1, Prop. 6.2 and Def. 6.3. For (M4), let
`σ : ⌜Δ'⌝ → ⌜Δ⌝`. Then

```text
Θ ⊲_{ev θ'} a[σ]  =  Θ.a[σ][θ']  =  Θ.a[σ∘θ']  =  Θ ⊲_{ev(σ∘θ')} a  =  Θ ⊲_{⟦σ⟧(ev θ')} a,
```

and `p` and `v` are the same on both sides. ∎

**Definition 6.5 (tautological points).** `τ_Θ := ev(id) ∈ ⟦Θ⟧_{M_T}(Θ)`.

By naturality in `Δ`, every point is the image of a tautological point:

```text
ev θ  =  ⟦θ⟧(τ_Θ)        for every θ : ⌜Θ⌝ → ⌜Δ⌝.
```

`τ_{Θ.a}` is the generic point of `Θ ⊲_{τ_Θ} a = Θ.a`:

```text
τ_{Θ.a}  =  ev⟨p, v_a⟩  =  (τ_Θ·p, v).
```

---

## 7. Initiality

Fix a positive theory `T` and a model `𝒮 = (𝒟, 1, N, ⊲)`.

**Lemma 7.1 (generic points).** Define, by induction on admissible chains, an
object `FΘ ∈ 𝒟` and a point `γ_Θ ∈ ⟦Θ⟧_N(FΘ)`:

```text
F[]    :=  1,                       γ_[]    :=  N
F(Θ.a) :=  FΘ ⊲_{γ_Θ} a,            γ_{Θ.a} :=  (γ_Θ·p, v)
```

Then for every `J ∈ 𝒟`, `h ↦ γ_Θ·h` is a bijection
`Hom_𝒟(J, FΘ) ≅ ⟦Θ⟧_N(J)`.

*Proof.* (M3) applies: `Θ` is admissible, hence positive (Lemma 3.4 (d)), and
`a ∈ Adm(⌜Θ⌝)`. The bijection is proved by induction on `Θ`.

- *Empty chain.* Both sides are singletons.
- *`Θ.a`.* A map `J → FΘ ⊲_{γ_Θ} a` is a pair `(h : J → FΘ, x ∈ ⟦a⟧(J, γ_Θ·h))`
  (Def. 2.2). By the induction hypothesis this is a point `(γ_Θ·h, x)` of `Θ.a`
  at `J`. ∎

**Definition 7.2 (the functor `F : 𝒞_T → 𝒟`).** On objects, `F` is given by
Lemma 7.1. For `σ : Θ' → Θ`, `Fσ` is the unique map with

```text
γ_Θ · Fσ  =  ⟦σ⟧(γ_{Θ'}).
```

`⟦σ⟧` preserves points over `N`, because `σ` is a slice map. `F` preserves
identities and composition by uniqueness, and `F[] = 1`.

**Proposition 7.3 (existence).** Put

```text
φ(ev θ)  :=  ⟦θ⟧(γ_Θ)        for θ : ⌜Θ⌝ → ⌜Δ⌝,  Δ a positive chain.
```

Then `(F, φ)` is a morphism `𝒮_T → 𝒮` (Def. 5.2).

*Proof.* `φ` is well defined because `ev` is bijective (Prop. 6.2).

**Naturality in `Θ`.** For `f : Θ' → Θ`:

```text
φ((ev θ)·f) = φ(ev(θ∘f)) = ⟦θ⟧(⟦f⟧γ_{Θ'}) = ⟦θ⟧(γ_Θ·Ff) = φ(ev θ)·Ff.
```

**Naturality in `Δ`.** For `σ : ⌜Δ⌝ → ⌜Δ'⌝`:

```text
φ(⟦σ⟧(ev θ)) = φ(ev(σ∘θ)) = ⟦σ⟧(⟦θ⟧γ_Θ) = ⟦σ⟧(φ(ev θ)).
```

**(ext).** Let `a ∈ Adm(⌜Δ⌝)`.

```text
F(Θ ⊲_{ev θ} a)  =  F(Θ.a[θ])  =  FΘ ⊲_{γ_Θ} a[θ]  =  FΘ ⊲_{⟦θ⟧γ_Θ} a  =  FΘ ⊲_{φ(ev θ)} a
                    Def. 6.3     Lemma 7.1           (M4) in 𝒮
```

By (M4), the projections and generic elements also agree.

- `F(p) = p`, since `γ_Θ·F(p) = ⟦p⟧(γ_{Θ.a[θ]}) = γ_Θ·p`.
- The generic point of `Θ ⊲_{ev θ} a` is `ev θ⁺`, with
  `θ⁺ = ⟨θ∘p, v_a⟩ : ⌜Θ.a[θ]⌝ → ⌜Δ.a⌝`. Then
  ```text
  φ(ev θ⁺)  =  ⟦θ⁺⟧(γ_Θ·p, v)  =  ((⟦θ⟧γ_Θ)·p, v)  =  (φ(ev θ)·p, v).    ∎
  ```

**Proposition 7.4 (uniqueness).** Every morphism `(F', φ') : 𝒮_T → 𝒮` equals
`(F, φ)`.

*Proof.*

1. *`F'Θ = FΘ` and `φ'(τ_Θ) = γ_Θ`, by induction on `Θ`.*
   - *Empty chain.* `F'[] = 1`, and the empty chain has the single point `N`.
   - *`Θ.a`.* By (ext) at the point `τ_Θ`:
     ```text
     F'(Θ.a)    = F'(Θ ⊲_{τ_Θ} a) = F'Θ ⊲_{φ'τ_Θ} a = FΘ ⊲_{γ_Θ} a = F(Θ.a)
     φ'(τ_{Θ.a}) = φ'(τ_Θ·p, v)     = (φ'(τ_Θ)·p, v)   = (γ_Θ·p, v)    = γ_{Θ.a}
     ```
2. *`φ' = φ`.* By naturality in `Δ` and Def. 6.5:
   ```text
   φ'(ev θ) = φ'(⟦θ⟧τ_Θ) = ⟦θ⟧(φ'τ_Θ) = ⟦θ⟧(γ_Θ) = φ(ev θ).
   ```
3. *`F'σ = Fσ`.* By naturality in `Θ` and step 2:
   ```text
   γ_Θ·F'σ = φ'(τ_Θ)·F'σ = φ'(τ_Θ·σ) = φ'(ev σ) = ⟦σ⟧(γ_{Θ'}).
   ```
   So `F'σ = Fσ` by Lemma 7.1. ∎

**Theorem 7.5 (main theorem).** For a positive theory `T`, `𝒮_T` is an initial
object of `Mod(T)`.

*Proof.* Props. 7.3 and 7.4. ∎

The two halves use different things.

- **Existence** uses (M4) in the target, and only at the generic points `γ_Θ`.
- **Uniqueness** is the Yoneda lemma: `φ'` is determined by its values at the
  tautological points `τ_Θ`, and (ext) forces those values.

---

## 8. Status

| item | status |
|---|---|
| HrS structures, `Ctx`, Theorem 1.3 | **Lean** (`Initiality/`) |
| Prop. 1.1 | **Lean** (`Ctx/Inversion.lean`) |
| `PSh(𝒞)` as an HrS structure, `J_𝒞` (§2.1) | **Lean** (`HrS/Presheaf/`) |
| Defs. 3.1–3.3, Lemma 3.4 (a)–(d) | **Lean** (`Theory/Basic.lean`, `Theory/Positive.lean`) |
| positivity of `Ξ_λ` (§3.3) | **Lean, open**: `Theory/Examples.lean`, `sorry`s standing |
| Lemma 2.3, Lemma 3.4 (e), Lemma 3.5, §§4–7, Appendix A | paper |

**What the main theorem uses:** Lemmas 2.3, 3.4 and 3.5; Def. 4.1; Defs. 5.1,
5.2, 5.4 and Thm. 5.5; §6; §7. It uses neither Prop. 5.3 nor Appendix A.

---

## Appendix A. Morphisms as logical relations

A morphism can also be defined as a pair `(F, r)`, where `r` is a witness that
`M` and `N` are related by the logical relation of a third HrS structure. For a
positive theory, the two definitions agree (Prop. A.7). Nothing outside this
appendix depends on it.

### A.1 The relational model

Fix a functor `F : 𝒞 → 𝒟`. For `I ∈ 𝒞`, write
`F_I : 𝒞/I → 𝒟/FI, (J, f) ↦ (FJ, Ff)`.

**Definition A.1 (the relational model `Rel F`).** The data are as follows.

- **Contexts** are triples `(Γ₁, Γ₂, Γᴿ)`, with `Γ₁ ∈ PSh(𝒞)` and
  `Γ₂ ∈ PSh(𝒟)`.
  - `Γᴿ` is a relation. It gives sets `Γᴿ(I, ξ₁, ξ₂)` of **witnesses** for
    `ξ₁ ∈ Γ₁(I)` and `ξ₂ ∈ Γ₂(FI)`.
  - Witnesses restrict: `Γᴿ(I, ξ₁, ξ₂) → Γᴿ(J, ξ₁·f, ξ₂·Ff)`.
  - Write `ρ : ξ₁ ~ ξ₂` for `ρ ∈ Γᴿ(I, ξ₁, ξ₂)`.
- **Types** are triples `(A₁, A₂, Aᴿ)`. `Aᴿ` gives sets of witnesses
  `Aᴿ(ρ, x₁, x₂)` for `ρ : ξ₁ ~ ξ₂`, `x₁ ∈ A₁(I, ξ₁)` and `x₂ ∈ A₂(FI, ξ₂)`,
  with restrictions.
- **Terms** are triples `(t₁, t₂, tᴿ)` with `tᴿ(ρ) ∈ Aᴿ(ρ, t₁ξ₁, t₂ξ₂)`, natural
  in `I`.
- **Extension.** `(ρ, α) : (ξ₁, x₁) ~ (ξ₂, x₂)` means that `ρ : ξ₁ ~ ξ₂` and
  `α ∈ Aᴿ(ρ, x₁, x₂)`.
- **Type formers.** On the first two components they are those of `PSh(𝒞)` and
  `PSh(𝒟)`. On witnesses:

```text
Uᴿ(ρ, S₁, S₂)              =  natural maps S₁ → S₂ ∘ F_I        (S₁ ∈ PSh(𝒞/I),  S₂ ∈ PSh(𝒟/FI))
(El S)ᴿ(ρ, x₁, x₂)         =  {★ | Sᴿ(ρ)(x₁) = x₂}               (the component of Sᴿ(ρ) at id_I)
Bind(A, C)ᴿ(ρ, b₁, b₂)     =  natural families
                                w(f, x₁, x₂, α)  ∈  Cᴿ((ρ·f, α), b₁(f, x₁), b₂(Ff, x₂))
                              over f : J → I  and  α ∈ Aᴿ(ρ·f, x₁, x₂)
IdSort(S, S')ᴿ(ρ, ★, ★)    =  {★ | Sᴿ(ρ) = S'ᴿ(ρ)}
IdElement(l, r)ᴿ(ρ, ★, ★)  =  {★}
```

In words:

- two sorts are related by a map from the first to the second;
- two elements are related when that map sends one to the other;
- two `Bind`-elements are related when they send related arguments to related
  results.

**Proposition A.2** **[routine]**. `Rel F` is an HrS structure, and the
projections `π₁ : Rel F → PSh(𝒞)` and `π₂ : Rel F → PSh(𝒟)` are morphisms.

The two equation types need care.

- **`IdSort`.** A term of `IdSort(S, S')` exists iff `S₁ = S'₁`, `S₂ = S'₂` and
  `Sᴿ = S'ᴿ`, that is, iff `S = S'`.
- **`IdElement`.** `(El S)ᴿ` is a proposition, so a term of `El S` is determined
  by its first two components. This is why the witnesses of `IdElement` can be
  trivial.

**Corollary A.3 (fundamental lemma).** Let `J_Rel : Ctx → Rel F` be the morphism
of Theorem 1.3. Then `π₁ ∘ J_Rel = J_𝒞` and `π₂ ∘ J_Rel = J_𝒟`, by uniqueness.
Hence `J_Rel` assigns the following.

- To every context `Γ`, a relation `⟦Γ⟧ᴿ` between `⟦Γ⟧_𝒞` and `⟦Γ⟧_𝒟`.
- To every type `a`, a relation `⟦a⟧ᴿ` between `⟦a⟧_𝒞` and `⟦a⟧_𝒟`, over
  `⟦Γ⟧ᴿ`.
- To every term `t` and every `ρ : ξ₁ ~ ξ₂`, a witness `⟦t⟧ᴿ(ρ) : ⟦t⟧ξ₁ ~ ⟦t⟧ξ₂`.
  Likewise for every map `σ`: `⟦σ⟧ᴿ(ρ) : ⟦σ⟧ξ₁ ~ ⟦σ⟧ξ₂`.

### A.2 Relational morphisms

Let `𝒮 = (𝒞, 1, M, ⊲)` and `𝒮' = (𝒟, 1, N, ⊲)` be models, and let
`F : 𝒞 → 𝒟` be a functor with `F1 = 1`. Then `F(!_I) = !_{FI}`. So a witness
`r : M ~ N` in `⟦Ξ⟧ᴿ` at stage `1` restricts to `r_I := r·!_I : M_I ~ N_{FI}`.

**Definition A.4 (related points).** Let `Δ` be a chain over `Ξ`. Points
`γ₁ ∈ ⟦Δ⟧_M(I)` and `γ₂ ∈ ⟦Δ⟧_N(FI)` are **related over `r`** by a witness
`ρ : γ₁ ~ γ₂` in `⟦Ξ ▷ Δ⟧ᴿ` whose `Ξ`-part is `r_I`. Explicitly,
`ρ = (r_I, α₁, …, α_k)` with `α_j` a witness for the `j`-th entries.

**Definition A.5 (relational morphism).** A **relational morphism**
`(F, r) : 𝒮 → 𝒮'` consists of the following.

- A functor `F : 𝒞 → 𝒟` with `F1 = 1`.
- A witness `r : M ~ N` in `⟦Ξ⟧ᴿ(1, M, N)`.
- **(ext)** A condition on chosen extensions. Let `Δ` be a positive chain over
  `Ξ`, let `ρ : γ₁ ~ γ₂` be related over `r` at `I`, and let `a ∈ Adm(⌜Δ⌝)`. Then
  ```text
  F(I ⊲_{γ₁} a) = FI ⊲_{γ₂} a,        F(p) = p,        v₁ ~ v₂ over ρ·p in ⟦a⟧ᴿ.
  ```

### A.3 Functionality

**Lemma A.6 (functionality).** Let `(F, r)` be a relational morphism and `Δ` a
positive chain over `Ξ`.

- **(a)** Every `γ ∈ ⟦Δ⟧_M(I)` is related over `r` to exactly one point
  `φγ ∈ ⟦Δ⟧_N(FI)`, by exactly one witness.
- **(b)** Let `a ∈ Pos(⌜Δ⌝)` and `x ∈ ⟦a⟧(I, γ)`. There is exactly one
  `φx ∈ ⟦a⟧(FI, φγ)` related to `x` over the witness of (a), by exactly one
  witness.
- **(c)** `φ(γ·f) = (φγ)·Ff` and `φ(x·f) = (φx)·Ff`.
- **(d)** Let `t ∈ Tm(Ξ ▷ Δ, a)` with `a` positive. Then `φ(⟦t⟧γ) = ⟦t⟧(φγ)`.
  For a slice map `σ : ⌜Δ'⌝ → ⌜Δ⌝` between positive chains,
  `φ(⟦σ⟧γ) = ⟦σ⟧(φγ)`.

With this notation, (ext) reads as follows: `F(I ⊲_γ a) = FI ⊲_{φγ} a`,
`F(p) = p`, and `φ(v) = v`.

*Proof.* First prove **(b')**: let `ρ : γ₁ ~ γ₂` relate points of a positive
chain `Δ` over `r`, let `a ∈ Pos(⌜Δ⌝)`, and let `x₁ ∈ ⟦a⟧(I, γ₁)`; then there is
exactly one pair `(x₂, α)` with `α ∈ ⟦a⟧ᴿ(ρ, x₁, x₂)`. The proof is by induction
on the derivation of `a ∈ Pos`, for all `Δ` and `ρ` at once.

*(P1) `a = El S`.* `⟦S⟧ᴿ(ρ)` is a map `⟦S⟧γ₁ → ⟦S⟧γ₂ ∘ F_I`, and `(El S)ᴿ` is its
graph. Take `x₂ := ⟦S⟧ᴿ(ρ)(x₁)` and `α := ★`.

*(P2) `a = IdElement(l, l')`.* `x₁ = ★` means `⟦l⟧γ₁ = ⟦l'⟧γ₁`. By Cor. A.3,
`⟦l⟧γ₂` and `⟦l'⟧γ₂` are both related to this element of `El S`. By (P1) they are
equal, so `★ ∈ ⟦a⟧(FI, γ₂)`. The witness `★` is the only one.

*(P3) `a = Bind(b, c)`, with `b ∈ Adm ∩ Pos` and `c ∈ Pos`.* Take the chosen
extension `(I ⊲_{γ₁} b, p, v₁)`. By (ext), `F(I ⊲_{γ₁} b) = FI ⊲_{γ₂} b`,
`F p = p`, and `α_v : v₁ ~ v₂` over `ρ·p`. So the generic points are related:

```text
(ρ·p, α_v) : (γ₁·p, v₁) ~ (γ₂·p, v₂)        (points of the positive chain Δ.b)
```

1. *`F` on pairing maps.* Let `f : J → I` and `z₁ ∈ ⟦b⟧(J, γ₁·f)`. By the
   induction hypothesis for `b`, there is a unique `ζ : z₁ ~ z₂` over `ρ·f`.
   - Restrict `α_v` along `⟨f, z₁⟩`. This gives
     `z₁ = v₁·⟨f, z₁⟩ ~ v₂·F⟨f, z₁⟩` over `ρ·f`, hence `v₂·F⟨f, z₁⟩ = z₂`.
   - Also `p ∘ F⟨f, z₁⟩ = F(p ∘ ⟨f, z₁⟩) = Ff`.
   - Therefore `F⟨f, z₁⟩ = ⟨Ff, z₂⟩`.
2. *Existence.* By the induction hypothesis for `c` at the generic points, there
   is a unique `ω : x₁(p, v₁) ~ y₂`.
   - By Lemma 2.3 in `𝒟`, `y₂ = x₂(p, v₂)` for a unique `x₂`.
   - Put `w(f, z₁, z₂, ζ) := ω·⟨f, z₁⟩`. By step 1, it relates
     `x₁(p, v₁)·⟨f, z₁⟩ = x₁(f, z₁)` to `y₂·F⟨f, z₁⟩ = x₂(Ff, z₂)`.
   - It lies over `(ρ·p, α_v)·⟨f, z₁⟩`, which equals `(ρ·f, ζ)` by uniqueness of
     `ζ`.
3. *Uniqueness.* Let `w' : x₁ ~ x₂'`. Its component at `(p, v₁, v₂, α_v)`
   relates `x₁(p, v₁)` to `x₂'(p, v₂)`.
   - By the induction hypothesis for `c`, `x₂'(p, v₂) = y₂`, so `x₂' = x₂` by
     Lemma 2.3.
   - Each component of `w'` is unique by the induction hypothesis for `c`, so
     `w' = w`.

Now the remaining parts.

- **(a)** follows from (b') by induction on the length of `Δ`. The empty chain
  has the single point `N_{FI}`, with the witness `r_I`.
- **(c)** holds because witnesses restrict, and by uniqueness.
- **(d)** holds because Cor. A.3 provides the witnesses `⟦t⟧ᴿ(ρ)` and
  `⟦σ⟧ᴿ(ρ)`; then apply uniqueness. The `Ξ`-part of `⟦σ⟧ᴿ(ρ)` is
  `⟦p ∘ σ⟧ᴿ(ρ) = ⟦p⟧ᴿ(ρ) = r_I`, because `σ` is a slice map. ∎

### A.4 Agreement

**Proposition A.7 (agreement).** Fix `F : 𝒞 → 𝒟` with `F1 = 1`. The assignment
`(F, r) ↦ (F, φ)` of Lemma A.6 is a bijection from relational morphisms
`𝒮 → 𝒮'` to morphisms `𝒮 → 𝒮'` (Def. 5.2).

*Proof.* `(F, φ)` is a morphism by Lemma A.6 (a), (c), (d) and (ext).

**Injective.** By Lemma A.6, related arguments are exactly the pairs `(β, φβ)`,
each with a unique witness. Look at the components of `r` slot by slot.

- *Sort slot `y`.* The component `r_y` is a natural family, over the pairs
  `(β, φβ)`, of witnesses in `Uᴿ`. Such a witness is a natural map
  `M_y(β·−) → N_y((φβ)·F−)`. By naturality in `I`, the family is determined by
  its components at identities, and these are the maps `φ_y` **[routine:
  Yoneda]**.
- *Every other slot.* The component is a witness of `El`, `IdSort` or
  `IdElement` under `Bind`s, and such a witness is unique when it exists.

**Surjective.** Given a morphism `(F, φ)`, define `r` slot by slot.

- `r_y` is the family whose components at identities are the maps `φ_y`.
- At every other slot, `r_x := ★`.

Along the slots, and by induction on positive types as in Lemma A.6, the
relatedness over `r` on positive chains is the graph of `φ`.

- *`El S`.* By Lemma 3.5 and Prop. 5.3 (a).
- *`IdElement`.* There is nothing to check.
- *`Bind(b, c)`.* By (ext), Lemma 2.3, and `φ(x(f, z)) = (φx)(Ff, φz)`. This is
  step 1 of the proof of Prop. 5.3 (a), applied to `x·f`.

The witnesses `★` exist by Prop. 5.3 (b): (op) at operation slots, (sort) at
sort-equation slots. Finally, (ext) for `(F, r)` is (ext) for `φ`. ∎

Without positivity, Lemma A.6 fails by the examples of Remark 5.6: related
elements need not exist, or need not be unique.
