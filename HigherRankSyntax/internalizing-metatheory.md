# Internalizing metatheory: external versus internal families

This note covers two families that are definable for every external numeral but not internally:

- semisimplicial types in 2LTT (§0);
- towers of exponentials on Church numerals in the simply typed λ-calculus (§1).

In both, an external numeral is a variable of a non-admissible sort and an internal numeral is a variable of an admissible sort.

# 0. Semisimplicial types, 2LTT, and "external but not internal"

## 0.1 Semisimplicial types

A semisimplicial type of level n is a tower of type families. Each level gives the fillers for the boundaries built from the levels below it.

```text
level 1     A₀ : U                                                      points
level 2     A₁ : A₀ → A₀ → U                                            edges
level 3     A₂ : Π (x y z : A₀). A₁ x y → A₁ y z → A₁ x z → U           triangles
level k+1   A_k : (boundary of a k-simplex in the data so far) → U
```

- **The boundary** of a k-simplex assigns to every proper face of {0, …, k} a cell of the right dimension, compatibly along shared faces.
- **`S_n`** is the type of level-n towers, an iterated Σ-type in `U₁`. For each fixed n it can be written out by hand.
- **The open problem** in plain HoTT is an internal `S : ℕ → U₁` with `S(n) ≃ S_n`. It can be solved in extensions:
  - 2LTT with ACKS's axioms (A1) or (A2);
  - plausibly also Kolomatskaia–Shulman's displayed type theory (2023; not checked).

## 0.2 2LTT as a theory in our framework

```text
inner (HoTT)     Ty₀, Tm₀, Π₀, Σ₀, Id₀, U₀ ⊂ U₁, ℕ₀, univalence
outer (strict)   Ty₁, Tm₁, Π₁, Σ₁, finite types, ℕ₁ with recursion, strict equality with reflection
conversion       c : [A : of Ty₀] of Ty₁,          Tm₁ (c A) ≡ Tm₀ A
```

Every slot has rank ≤ 3. There are two choices of admissible sorts:

```text
𝒫_all    :=  { Tm₀ A,  Tm₁ A }          both levels extend contexts
𝒫_inner  :=  { Tm₀ A }                  only the inner level does
```

**𝒫_all is ACKS's 2LTT.** Their models are "two categories with families which share a common category of contexts" (Def 2.9), and `c` preserves context extension. Their presheaf model over a model C of HoTT (Cor 2.14) works like this:

- **Contexts** are presheaves on C.
- **Outer types** over P ∈ Ĉ are presheaves on C/P. `P.A` is the presheaf of pairs. `ℕ₁` is "levelwise", i.e. the constant presheaf `Δℕ`.
- **Inner types** over P are maps `P → Ty_C`, and inner terms are lifts to `Tm_C`.

**𝒫_inner is the same model, presented over the base C.**

- Sorts are presheaves on C.
- `Tm₀ A` is representable, by comprehension in C.
- `Tm₁ ℕ₁ = Δℕ` is not representable, because `y(Γ) × Δℕ ≅ ∐ₖ y(Γ)`.

**What the choice changes, and what it doesn't:**

- **Judgments are written the same way.** `Ξ ⋈ [n : of Tm₁ ℕ₁] ⊢ e : of Tm₀ U₁` is a judgment under both choices. 𝒫 only says which bindings Θ must denote objects of the base.
- **Every judgment means the same.**
  - Over C, `Ξ ⋈ Θ ⊢ e : of T` means a natural transformation `⟦Θ⟧ ⇒ T`, where `⟦Θ⟧ ∈ Ĉ` is the presheaf of fillings.
  - Over Ĉ, `⟦Θ⟧` is itself a context. By the definitions above, an element of T at that context is the same data, up to isomorphism.
  - ACKS build their inner type formers over C in exactly this way. For (2.10), Π's codomain is given "naturally in (Δ, σ : Δ → Γ) ∈ C/Γ, [as] a map B_σ : Tm_C(Δ, A[σ]) → Ty_C(Δ)". This is reduced to `Ty(Γ.A)` "by the universal property of context extension in C". That is `Bind` and Lemma 2.3 of `positive-theories-and-initiality.md`.
- **Where non-representability shows up in ACKS.** It is not in comprehension, since every type has comprehension. It is in the Yoneda comparison `y : C → Ĉ`, which "acts bijectively on types and terms":
  - inner extension preserves representables: `y(Γ).A ≅ y(Γ.A)`;
  - outer extension does not: `y(Γ).ℕ₁ ≅ ∐ₖ y(Γ)`.

  Conservativity (Prop 2.18) rests on the first of these.
- **Which to use.**
  - Under 𝒫_all, the line between object level and metatheory is "the context is in the image of y". It is visible only in the presheaf model.
  - Under 𝒫_inner, the line is "admissible or not", and it is part of the theory.
  - For internalizing metatheory, 𝒫_inner is the better fit. The cost is that outer `Π₁` then binds non-admissible variables, so this version is not positive.

## 0.3 The two judgments

```text
external   Ξ ⋈ [n : of Tm₁ ℕ₁]  ⊢  SST n : of Tm₀ U₁          derivable (ACKS §4)
internal   Ξ ⋈ [n : of Tm₀ ℕ₀]  ⊢  S n   : of Tm₀ U₁          with S ⌜k⌝ ≃ S_k for all k:  open
```

- **External.**
  - **Meaning:** `Nat(Δℕ, Tm_C(−, U₁)) ≅ Tm_C(1, U₁)^ℕ`, i.e. one closed HoTT type for each k.
  - **Over Ĉ:** an inner term over the context `Δℕ ≅ ∐ₖ y(1)`, i.e. one over each summand.
  - **Computation:** substituting `n := s₁ᵏ z₁` computes away by outer recursion, and staging gives the HoTT type `S_k`.
  - **Strictly,** ACKS build an outer type of Reedy fibrant diagrams and prove it is inner up to outer isomorphism.
- **Internal.** `Tm₀ ℕ₀` is representable under both choices. By Yoneda, the judgment means one HoTT term `n : ℕ ⊢ S : U₁`.
- **How they relate.** Substituting `n := ⌜m⌝` turns an internal family into an external one. The open problem asks whether `k ↦ S_k` is in the image.

## 0.4 The high-level reason

`S_{k+1}` is built from `S_k` and its face maps. For the next boundary type to typecheck, the face maps must satisfy the simplicial identities `dᵢ dⱼ = d_{j−1} dᵢ` (for i < j) *judgmentally*.

- **For a concrete k**, the face maps are explicit composites of projections, so the identities hold by computation. The outer level is extensional, so it can carry them through a recursion on an outer n.
- **For a variable n**, they hold only up to paths. Using them needs coherences, then coherences between those, with no bound. A single HoTT term cannot carry this, and HoTT cannot add strictness because UIP contradicts univalence.

§1 has the same pattern, with a different missing principle: iterating one numeral at several types.

# 1. λ-calculus: towers of exponentials

In the simply typed λ-calculus, a Church numeral is iterated at a single type, and every exponentiation moves the exponent one type level up (§1.2). A tower of exponentials of height k therefore needs numerals at k different types (§1.3).

- An external numeral can choose these types by recursion on itself (§1.4–§1.6).
- No internal numeral can, whatever its type (§1.7–§1.8).
- System F internalizes the construction (§1.9).

## 1.1 Church numerals at every type

```text
N_A     :=  (A ⇒ A) ⇒ A ⇒ A  =  (A ⇒ A) ⇒ (A ⇒ A)           ⇒ associates to the right
N       :=  N_o
c_k^A   :=  λf. λx. f (f ( ⋯ (f x)))      :  N_A           k occurrences of f;  f : A ⇒ A,  x : A
gᵏ      :=  λx. g (g ( ⋯ (g x)))                           k occurrences of g;  g⁰ = λx. x
```

- **What `c` is.** `c` is a function in the metatheory, like `tw` in §1.3:

  ```text
  c  :  ℕ × Types  →  closed terms,          c_k^A  :  N_A
  ```

  Here `Types` is the set of simple types. The index k is a natural number of the metatheory, not an expression.
- **In the theory of §1.4,** `c_k^A` is the expression `lam ((f) lam ((x) app f ( ⋯ (app f x))))`.
  - For a closed type A, `Ξ ⊢ c_k^A : of Tm N_A`.
  - With A a bound variable, as in the filling `(A) c₁^A`, `Ξ ⋈ [A : of Ty] ⊢ c_k^A : of Tm N_A`.
- **No slot of the theory takes k.** The operation that takes an external numeral in place of k is `church` (§1.4), with `church (s₁ᵏ z₁) A =βη c_k^A`.
- `c_k^A g =β gᵏ` for every `g : A ⇒ A`: the numeral returns the k-fold composite of its argument.
- The untyped term `λf. λx. f (f ( ⋯ (f x)))` has type `N_A` for every A; the superscript records which typing is meant. Numerals at every type are standard, though the notation varies (Barendregt–Dekkers–Statman; Sørensen–Urzyczyn).
- Modulo βη, the closed terms of type `N` are exactly the `c_k^o`. So `Tm(ε, N) ≅ ℕ`.

## 1.2 Exponentiation raises the type of the exponent

**Lemma 1.1.** For all m, n ∈ ℕ and every type A,

```text
c_m^{A⇒A}  c_n^A   =βη   c_{nᵐ}^A
```

*Proof.* `c_n^A` has type `(A ⇒ A) ⇒ (A ⇒ A)`, so `c_m^{A⇒A}` iterates it:

```text
c_m^{A⇒A} c_n^A   →β   λg. c_n^A ( c_n^A ( ⋯ (c_n^A g)))           m occurrences of c_n^A,  g : A ⇒ A
```

By induction on j, applying `c_n^A` j times to g gives `g^{nʲ}` up to βη:

- for j = 0, `g =η g¹`;
- for the step, `c_n^A g^{nʲ} →β λx. g^{nʲ} ( ⋯ (g^{nʲ} x)) =β g^{nʲ·n}`.

So the right-hand side is βη-equal to `λg. g^{nᵐ}`, which is `c_{nᵐ}^A`. ∎

**Example.**

```text
c₂^{A⇒A} c₃^A   →β   λg. c₃^A (c₃^A g)   =β   λg. c₃^A g³   =β   λg. g⁹   =   c₉^A   =   c_{3²}^A
```

The base `c₃^A` iterates `g : A ⇒ A`. The exponent `c₂^{A⇒A}` iterates `c₃^A`, which is a function on functions, so it needs the higher type. Addition and multiplication keep both arguments at one type:

```text
add   :=  λm. λn. λf. λx. m f (n f x)     :  N_A ⇒ N_A ⇒ N_A           c_m, c_n  ↦  c_{m+n}
mult  :=  λm. λn. λf. m (n f)              :  N_A ⇒ N_A ⇒ N_A           c_m, c_n  ↦  c_{m·n}
exp   :=  λm. λn. m n                      :  N_{A⇒A} ⇒ N_A ⇒ N_A       c_m, c_n  ↦  c_{nᵐ}
```

## 1.3 The tower

**What is defined.** For every natural number k and every simple type A, a closed term

```text
tw(k, A)  :  N_A                 i.e.   tw : ℕ × Types → closed terms,    tw(k, A) ∈ Tm(ε, N_A)
```

- **What it is:** an application of Church numerals to one another, at types that depend on k.
- **What it computes:** the tower number 2↑↑k, as a Church numeral at type A: `tw(k, A) =βη c_{2↑↑k}^A` (Lemma 1.2).
- **How it is defined:** in the metatheory, by recursion on k. §1.4 expresses it in the framework.

**Tower numbers.** Exponentiation associates to the right: `2^2^2 = 2^(2^2)`.

```text
2↑↑k     :=  2^2^⋯^2           k twos  (2↑↑0 := 1)            1, 2, 4, 16, 65536, …
2_h(s)   :=  2^2^⋯^2^s         h twos, with s on top         2_0(s) = s,   2_1(s) = 2^s,   2_2(s) = 2^(2^s)
```

Recursively, `2↑↑(k+1) = 2^(2↑↑k)` and `2_{h+1}(s) = 2^(2_h(s))`. The tower number is the case s = 1: `2↑↑k = 2_k(1)`, for example `2↑↑3 = 2_3(1) = 2^(2^(2^1)) = 16`.

- **In `2↑↑k`, the height of the tower is k.**
- **In `2_h(s)`, the height h is fixed and only the top s varies.** §1.7 uses this to bound what a fixed term can compute, and §1.8 shows that each fixed height is internal.

**Definition.** By recursion on k, simultaneously for all types A:

```text
tw(0, A)     :=  c₁^A
tw(k+1, A)   :=  tw(k, A ⇒ A)  c₂^A
```

**Lemma 1.2.** `tw(k, A) =βη c_{2↑↑k}^A` for every k and every A.

*Proof.* By induction on k, for all A at once. For k = 0 both sides are `c₁^A`. For the step:

```text
tw(k+1, A)  =  tw(k, A ⇒ A) c₂^A  =βη  c_{2↑↑k}^{A⇒A} c₂^A  =βη  c_{2^(2↑↑k)}^A  =  c_{2↑↑(k+1)}^A
```

This uses the induction hypothesis at the type `A ⇒ A`, then Lemma 1.1 with m := 2↑↑k and n := 2. ∎

Unfolded, with `A₀ := o` and `A_{j+1} := A_j ⇒ A_j`:

```text
tw(k, o)  =  c₁^{A_k}  c₂^{A_{k−1}}  ⋯  c₂^{A₁}  c₂^{A₀}           applications nested to the left
```

For k = 3 there are three steps:

```text
c₁^{A₃} c₂^{A₂}  =βη  c₂^{A₂}
c₂^{A₂} c₂^{A₁}  =βη  c₄^{A₁}
c₄^{A₁} c₂^{A₀}  =βη  c₁₆^{A₀}
```

- **The recursion changes its type argument,** from A to A ⇒ A (polymorphic recursion). Correspondingly, the proof of Lemma 1.2 uses the induction hypothesis at a different type.
- **`tw(k, o)` contains numerals at the k + 1 types** `A_k, …, A₀`. §1.7 shows that no fixed type suffices.
- **The metatheory only writes this program;** βη-reduction computes 2↑↑k. These programs are the standard witness that β-normal forms can be non-elementarily larger than the terms they come from (cf. Statman 1979).

## 1.4 The theory

```text
-- inner: simply typed λ-calculus, one base type
Ty    : sort                                                          not admissible (no type variables)
Tm    : [A : of Ty] sort                                              [x : of Tm A] admissible
o     : of Ty
⇒     : [A B : of Ty] of Ty
lam   : [A B : of Ty,  b : [x : of Tm A] of Tm B]  of Tm (A ⇒ B)
app   : [A B : of Ty,  f : of Tm (A ⇒ B),  a : of Tm A]  of Tm B
β     : [A B,  b : [x : of Tm A] of Tm B,  a : of Tm A]  eq (app (lam b) a) (b a)
η     : [A B,  f : of Tm (A ⇒ B)]                        eq (lam ((x) app f x)) f

-- outer: numerals, iterated at families of terms indexed by types
N₁     : sort                                                         not admissible
z₁     : of N₁
s₁     : [m : of N₁] of N₁
iter   : [D : [X : of Ty] of Ty,
          a : [A : of Ty] of Tm (D A),
          t : [r : [B : of Ty] of Tm (D B),  A : of Ty] of Tm (D A),
          m : of N₁,
          A : of Ty]
         of Tm (D A)
iter-z : [D, a, t, A]       eq (iter D a t z₁ A)       (a A)
iter-s : [D, a, t, m, A]    eq (iter D a t (s₁ m) A)   (t ((B) iter D a t m B) A)
```

**Conventions.** `λx. M` stands for `lam ((x) M)` and juxtaposition for `app`. Type arguments are omitted. The numerals of §1.1 are closed expressions.

**Reading `iter`.** `iter` is the ordinary iterator `it : C → (C → C) → N₁ → C`, taken at `C := ∀A. Tm (D A)`: a choice of one term of type `D A` for every type A. Its equations are those of `it`, namely `it a t z₁ = a` and `it a t (s₁ m) = t (it a t m)`.

C is a binding over `Ty`, not a sort, so every occurrence of C is curried into a binding:

- the base `a`;
- the step's input `r`;
- the result, whose `∀A` becomes the trailing entry `A`.

In `iter-s`, the filling `(B) iter D a t m B` is `it a t m : C`.

**Definitions.** Three derived slots, given by their bindings and boundaries:

```text
succ    : [A : of Ty,  x : of Tm N_A]    of Tm N_A           successor of a numeral at type A
church  : [m : of N₁,  A : of Ty]        of Tm N_A           the external numeral m, as a numeral at type A
tw      : [m : of N₁,  A : of Ty]        of Tm N_A           the tower program of §1.3, at type A
```

For example, `Ξ ⋈ [m : of N₁, A : of Ty] ⊢ tw m A : of Tm N_A`. The type argument of `succ` is omitted below. They are defined by:

```text
succ x       :=  λf. λy. f (x f y)
church m A   :=  iter ((X) N_X) ((A) c₀^A) ((r A) succ (r A))         m A
tw m A       :=  iter ((X) N_X) ((A) c₁^A) ((r A) r (A ⇒ A) c₂^A)     m A
```

By `iter-z` and `iter-s`:

```text
church z₁ A  ≡  c₀^A                 church (s₁ m) A  ≡  succ (church m A)
tw z₁ A      ≡  c₁^A                 tw (s₁ m) A      ≡  tw m (A ⇒ A) c₂^A
```

So on closed numerals, `church (s₁ᵏ z₁) A =βη c_k^A`, and `tw (s₁ᵏ z₁) A ≡ tw(k, A)` is the program of §1.3.

**Shape.**

- **Rank.** In `iter`, `r` contributes 2, so `t` contributes 3. The binding of `iter` therefore has rank 3, and `iter` has rank 4.
- **Not positive, not a SOGAT.** The binders of `D`, `a`, `t` and `r` bind variables of sort `Ty`, which is not admissible. So the theory is not positive, and it is not a SOGAT, both because of its rank and because of what it binds.
- **Why the motive ranges over all types.** The recursive call of `tw` is at `A ⇒ A`, so a motive `Tm (D A)` for one fixed A would not do.
- **A lighter alternative.** Take `church` and `tw` as slots, with the four equations above as axioms. That theory has rank 3. Its only nested binder is that of `lam`, which binds an admissible sort, so it is positive and second-order. The external tower is the same.

**Relation to 2LTT.** This is a miniature of 2LTT under 𝒫_inner:

- the inner level is the simply typed λ-calculus;
- the outer level is N₁ with `iter`;
- `church` plays the role of `⌜−⌝`.

## 1.5 The intended model

```text
base 𝒞    contexts Γ of simple types;  maps: substitutions modulo βη;  ε terminal
Ty    ↦  ΔTypes, the constant presheaf of simple types
Tm A  ↦  Tm(−, A),   Tm(Γ, A) := terms of type A in Γ, modulo βη             Γ ⊲ A := Γ, x : A
N₁    ↦  Δℕ;     z₁ ↦ 0;     s₁ ↦ (k ↦ k + 1)
```

**How a slot is interpreted** (`positive-theories-and-initiality.md` §2.1 and Def 4.1). Let x be a slot with binding Θ and boundary `of T`.

- The fillings of Θ at a context Γ form a set `F_Θ(Γ)`, and these sets form a presheaf `F_Θ`.
- For each filling `φ ∈ F_Θ(Γ)`, `T` gives a set `T(Γ, φ)`.

The model's component at x is then one element, and its component at Γ is a dependent function on the fillings at Γ:

```text
⟦x⟧      ∈   ⟦Bind(Θ, T)⟧(ε)   ≅   Nat(F_Θ, T)
⟦x⟧_Γ    ∈   ∏_{φ ∈ F_Θ(Γ)} T(Γ, φ)                      with  ⟦x⟧_Γ(φ)[σ] = ⟦x⟧_Δ(φ·σ)  for σ : Δ → Γ
```

**The fillings of `iter`'s binding at Γ.** `F(Γ)` is the set of tuples `(D, a, t, k, A)` described in the table below; the possible `a` and `t` depend on `D`.

- `ΔTypes` is constant, so a binder over `Ty` becomes a product over all types.
- Naturality in Γ reduces each filling to its value at Γ, and nothing relates the components at different types.
- Below, `D`, `a` and `t` also name these values.

```text
entry   a filling at Γ is                                                amounting to
D       a type D(X) for every type X                                     a function  Types → Types
a       a term a_A ∈ Tm(Γ, D(A)) for every type A                        a family  a = (a_A)_A ∈ ∏_A Tm(Γ, D(A))
t       a term t(r, A) ∈ Tm(Γ, D(A)) for every family                    an operation on families,
        r ∈ ∏_B Tm(Γ, D(B)) and every type A                             t_Γ(r) := (t(r, A))_A
m       a number k                                                       k ∈ ℕ
A       a type                                                           A ∈ Types
```

Strictly, `t` also gives an operation at every `Δ → Γ`, and these commute with substitution. `iter` at Γ uses only `t_Γ`; the rest makes it commute with substitution.

**The interpretation of `iter`.** `⟦iter⟧` is one element of `Nat(F, T)`, where `T(Γ, (D, a, t, k, A)) := Tm(Γ, D(A))`. Its component at Γ is a dependent function

```text
⟦iter⟧_Γ   ∈   ∏_{(D, a, t, k, A) ∈ F(Γ)}  Tm(Γ, D(A))
```

It starts from the family a, applies the step k times, and takes the component at A:

```text
⟦iter⟧_Γ (D, a, t, k, A)   :=   (t_Γᵏ (a))_A
```

- **It commutes with substitution,** because t does.
- **`iter-z`:** for k = 0 the result is `a_A`, the meaning of `a A`.
- **`iter-s`:** for k + 1 the result is `(t_Γ(t_Γᵏ(a)))_A = t(t_Γᵏ(a), A)`. This is the meaning of `t ((B) iter D a t m B) A`, because the filling `(B) iter D a t m B` denotes the family `t_Γᵏ(a)`.

**`church` and `tw`.** Both take `D(X) = N_X`. They differ in the start and in the step:

```text
            start a_A       step (t_Γ(r))_A        result (t_Γᵏ(a))_A
church      c₀^A            succ (r_A)             c_k^A
tw          c₁^A            r_{A⇒A} c₂^A           tw(k, A)  =βη  c_{2↑↑k}^A        by Lemma 1.2
```

- **`church` works one type at a time:** its step uses only the component `r_A`.
- **`tw`'s step needs the whole family:** it builds the component at A from the component at `A ⇒ A`. This is the polymorphic recursion of §1.3. For k = 2:

  ```text
  (t_Γ(a))_A    =  a_{A⇒A} c₂^A                =  c₁^{A⇒A} c₂^A
  (t_Γ²(a))_A   =  (t_Γ(a))_{A⇒A} c₂^A         =  c₁^{(A⇒A)⇒(A⇒A)} c₂^{A⇒A} c₂^A   =  tw(2, A)
  ```

**The motive as a polymorphic numeral.** The motive `∏_A Tm(Γ, N_A)` is the external counterpart of a polymorphic numeral: an arbitrary choice of one numeral for each type. A System F numeral (§1.9) is a single, uniform such choice.

## 1.6 External and internal judgments

Set `N = N_o`.

```text
external             Ξ ⋈ [m : of N₁]       ⊢ e : of Tm N    ↦  ⟦e⟧ ∈ Nat(Δℕ, Tm(−, N))  ≅  Tm(ε, N)^ℕ  ≅  ℕ^ℕ
internal, input A    Ξ ⋈ [n : of Tm N_A]   ⊢ e' : of Tm N    ↦  ⟦e'⟧ ∈ Nat(Tm(−, N_A), Tm(−, N))     ≅  Tm(ε, N_A ⇒ N)
```

**Restriction, from internal to external.** Substituting the external numeral for the internal one turns an internal judgment into an external one:

```text
Ξ ⋈ [n : of Tm N_A] ⊢ e' : of Tm N       ⟼       Ξ ⋈ [m : of N₁] ⊢ e'[n := church m A] : of Tm N
```

On meanings, this is the map

```text
Tm(ε, N_A ⇒ N)  →  Tm(ε, N)^ℕ,            P  ↦  (k ↦ P c_k^A)
```

- **Precomposition.** It is precomposition with `⟦church − A⟧ : Δℕ → Tm(−, N_A)`, `k ↦ c_k^A`.
- **Why "restriction".** An internal family is defined on all terms of type `N_A`, open ones included. Restriction keeps only its values on the numerals `c_k^A`.
- **The equation.** `P := λn. ⟦e'⟧`, and `⟦e'[n := church m A]⟧` at k is `⟦e'⟧[n := c_k^A] =βη P c_k^A`.

- **External.** This follows from naturality, since `Δℕ` is constant, and from `Tm(ε, N) ≅ ℕ`.
- **Internal.** This follows from Yoneda, since `Tm(−, N_A) = y(n : N_A)`, followed by λ-abstraction. It holds whatever slots e uses: an expression with no free external variable means a single λ-term.
- **The external tower.** `Ξ ⋈ [m : of N₁] ⊢ tw m o : of Tm N` means `k ↦ c_{2↑↑k}`, that is, `k ↦ 2↑↑k`.
- **The question** is whether this family is in the image of restriction, for some input type A.
- **Why the input type is a parameter.** Raising the input type is what makes more functions internal (§1.8), so Theorem 1.3 quantifies over A to exclude every raise.
- **There is no way back.** By Yoneda, `Nat(Tm(−, N_A), Δℕ) ≅ ℕ`, so every outer expression of sort N₁ is constant in an inner numeral. The metatheory can produce internal numerals (`church`) but cannot read them.

## 1.7 No internal tower

**Theorem 1.3.** For no closed type expression A is there an e with

```text
Ξ ⋈ [n : of Tm N_A] ⊢ e : of Tm N        and        Ξ ⋈ [m : of N₁] ⊢ e[n := church m A] ≡ tw m o
```

Equivalently, there is no closed term `P : N_A ⇒ N` with `P c_k^A =βη c_{2↑↑k}` for every k.

The proof uses the equation only through its instances at the closed numerals, `m := s₁ᵏ z₁`. So the theorem also holds with the weaker hypothesis "`Ξ ⊢ e[n := church (s₁ᵏ z₁) A] ≡ tw (s₁ᵏ z₁) o` for every k". In the intended model the two hypotheses agree, because `Δℕ` is constant.

The proof uses the following notions:

```text
level(o) := 0,       level(B ⇒ E) := max(level(B) + 1, level(E))
|t|      := number of variable occurrences, abstractions and applications in t      (types not counted)
```

*Proof.*

1. **Reduce to a closed term.** By §1.6, e means a single term `n : N_A ⊢ ⟦e⟧ : N`. Put `P := λn. ⟦e⟧`. The equation holds in the intended model, as an equality of natural transformations out of `Δℕ`. At k its two sides are `⟦e⟧[n := c_k^A] =βη P c_k^A` and `c_{2↑↑k}`. So `P c_k^A =βη c_{2↑↑k}` for every k.
2. **The levels are bounded.** Let d be the largest level of a type occurring in P or in `N_A`.
   - Every type occurring in `P c_k^A` has level ≤ d.
   - β-reduction creates no new types: the types in `M[x := L]` occur in M or in L.
   - So every type occurring in a reduct of `P c_k^A` has level ≤ d, and d does not depend on k.
3. **Normalization bound** (Schwichtenberg 1982). If every type occurring in a term t has level ≤ d, then the β-normal form of t has size at most `2_d(K·|t|)`, for a constant K. The reason: contracting all redexes of the highest degree, innermost first, removes that degree and at most exponentiates the size.
4. **Apply the bound.** `|c_k^A| = 2k + 3`, so `|P c_k^A| = |P| + 2k + 4`. The β-normal form of `P c_k^A` therefore has size at most `2_d(K·(|P| + 2k + 4))`.
5. **Compare with the target.** For k ≥ 1, `c_{2↑↑k}` is βη-normal and contains 2↑↑k occurrences of f.
   - The β-normal form of `P c_k^A` is βη-equal to it.
   - βη-normal forms are unique.
   - η-reduction keeps a β-normal term β-normal while only shrinking it.

   So the β-normal form of `P c_k^A` has size at least 2↑↑k.
6. **Contradiction.** For k ≥ d, `2↑↑k = 2_d(2_{k−d}(1))`. Now `2_{k−d}(1)` eventually exceeds `K·(|P| + 2k + 4)`, and `2_d` is strictly increasing. So for large k, step 5 contradicts step 4. ∎

The same proof works with any closed output type `N_C` in place of `N`.

## 1.8 Each fixed height is internal

For h ≥ 1:

```text
P_h  :=  λn. n c₂^{A_{h−1}} ⋯ c₂^{A₁} c₂^{A₀}     :   N_{A_h} ⇒ N
P_h c_k^{A_h}   =βη   c_{2_h(k)}
```

*Proof.* Lemma 1.1 gives `c_j^{A_{i+1}} c₂^{A_i} =βη c_{2^j}^{A_i}`. Apply it for i = h−1, …, 0, starting from j = k. ∎

- **The type level of the input is the height of the tower.** The tower is the diagonal, where the height equals the input: `P_k c₁^{A_k} →β tw(k, o)`.
- **The external numeral chooses both the program `P_k` and the type `A_k` of its input.** Any fixed input type handles only a fixed height, which is why Theorem 1.3 quantifies over A. Fortune–Leivant–O'Donnell (1983) study which functions become definable when input and output numerals have different types.
- **Predecessor is a fixed-height case.**
  - It is not internal at `N ⇒ N`: by Schwichtenberg's theorem (1976), the functions definable on `N` are the extended polynomials, and predecessor is not one of them.
  - It is internal at `N_B ⇒ N`, with `B := (o ⇒ o) ⇒ o`:

    ```text
    λn. λf. λx. n (λg. λq. q (g f)) (λu. x) (λu. u)
    ```

  One raise of the input type suffices, so once the input type may vary, predecessor does not separate external from internal.

## 1.9 Internalizing the tower: System F

```text
-- additions: type variables, and quantification over them
[X : of Ty]  admissible
∀     : [D : [X : of Ty] of Ty]  of Ty
Λ     : [D,  b : [X : of Ty] of Tm (D X)]  of Tm (∀ D)
inst  : [D,  u : of Tm (∀ D),  B : of Ty]  of Tm (D B)
∀-β   : [D, b, B]    eq (inst (Λ b) B)         (b B)
∀-η   : [D, u]       eq (Λ ((X) inst u X))     u
```

Write `∀α. E` for `∀ ((α) E)`, `Λα. M` for `Λ ((α) M)`, and `u [B]` for `inst u B`.

- **The motive becomes a type.** Since Ty is now admissible, Lemma 2.3 of `positive-theories-and-initiality.md`, together with `Λ` and `inst`, gives

  ```text
  Bind([A : of Ty], Tm (D A))(Γ)  ≅  Tm(Γ ⊲ Ty, D X)  ≅  Tm(Γ, ∀ D)
  ```

  For `D := (X) N_X` this is the type of polymorphic numerals, `N_∀ := ∀α. N_α`, with `c_k^∀ := Λα. c_k^α`.
- **The iteration of `iter` becomes ordinary iteration at `N_∀`:**

  ```text
  tower  :=  λn. n [N_∀] (λr. Λα. r [α ⇒ α] c₂^α) c₁^∀        :   N_∀ ⇒ N_∀
  tower c_k^∀   =βη   c_{2↑↑k}^∀
  ```

  The step `λr. Λα. r [α ⇒ α] c₂^α` is the step `(r A) r (A ⇒ A) c₂^A` of `tw`, with the external binder over A turned into `Λα`.
- **Proof of the equation.**
  - `c_k^∀ [N_∀] ≡ c_k^{N_∀}`, so `tower c_k^∀ =βη stepᵏ c₁^∀`.
  - `step c_j^∀ =βη Λα. c_j^{α⇒α} c₂^α =βη c_{2^j}^∀`, by Lemma 1.1 at the type α.
- **So `Ξ ⋈ [n : of Tm N_∀] ⊢ tower n : of Tm N_∀` is an internal tower.** It is impredicative: n is instantiated at `N_∀` itself (Girard–Lafont–Taylor for System F).
- **Other inner theories with an internal tower:**
  - MLTT with a universe U, iterating at `Π (A : U). N_A`, which lives one universe up;
  - Gödel's System T, whose numbers have a recursor at every type and in which 2↑↑n is primitive recursive.

## 1.10 Comparison

| | inner theory | external family | the external numeral chooses | missing internally | internalized by |
|---|---|---|---|---|---|
| tower | simply typed λ-calculus | `k ↦ c_{2↑↑k}` | the types `A_k, …, A₀` of the program | iterating one numeral at several types | System F; a universe; System T |
| semisimplicial types | HoTT | `k ↦ S_k` | the boundary types of the k levels | judgmental face-map identities | open in plain HoTT; extra strictness ((A1)/(A2), displayed type theory) |

In both rows, the external numeral is eliminated with judgmental computation at each concrete k, and it produces the types the construction needs at each stage. An internal numeral is one term of one type, and can be eliminated only as far as the inner theory allows.

# References

- D. Annenkov, P. Capriotti, N. Kraus, C. Sattler. *Two-level type theory and applications.* Mathematical Structures in Computer Science, 2023. arXiv:1705.03307. (ACKS)
- H. Barendregt, W. Dekkers, R. Statman. *Lambda Calculus with Types.* Cambridge University Press, 2013.
- S. Fortune, D. Leivant, M. O'Donnell. *The expressiveness of simple and second-order type structures.* Journal of the ACM 30, 1983.
- J.-Y. Girard, Y. Lafont, P. Taylor. *Proofs and Types.* Cambridge University Press, 1989.
- A. Kolomatskaia, M. Shulman. *Displayed type theory and semi-simplicial types.* arXiv, 2023.
- H. Schwichtenberg. *Definierbare Funktionen im λ-Kalkül mit Typen.* Archiv für mathematische Logik und Grundlagenforschung 17, 1976.
- H. Schwichtenberg. *Complexity of normalization in the pure typed lambda-calculus.* In: The L. E. J. Brouwer Centenary Symposium, North-Holland, 1982.
- M. H. Sørensen, P. Urzyczyn. *Lectures on the Curry–Howard Isomorphism.* Elsevier, 2006.
- R. Statman. *The typed λ-calculus is not elementary recursive.* Theoretical Computer Science 9, 1979.
