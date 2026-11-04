# Well-typed syntax from raw syntax

Status: proposal, 2026-11-02, second version. Supersedes `judgements-b-system-plan.md`.

Starting point: the raw syntax 𝔼, a relative monad on the slot functor, so that Kl(𝔼) is the category
of arities and substitutions. Everything else is derived. Decisions: kinds `ty`/`tm` inside the sorts of
the raw syntax; equations as entries without a slot; judgement forms over conclusions.

Summary. §1: a relative monad on J_S is a natural model whose types are its sorts; a unit type is
adjoined to it. §2: raw types are a module M sorted over S ⊔ {⊤}; the raw natural model is the
pullback along the sorting, contextualised (the chapter's C(T, M), with the unit type). §3: a *typing* is a sub-natural-model with a conversion-closed
congruence; this is the general machinery: typings form a complete lattice, their quotients are
natural models, and the structural rules are the unwinding of the definition. §4: a type theory is a
module of raw types and a set of rules; its judgements are the least typing closed under the rules.
§5: ToS^ω is the type theory whose raw types are hypothetical conclusions and whose rules say that an
entry is a hypothetical judgement (Figure 5.1); Figure 5.2 is the complete rule set. §6: the
relationship between raw and well-typed syntax. §7: what remains to be proved.

Notation. For a J_S-relative monad T, Kl(T) has as objects the lists of sorts and
Kl(T)(Ξ, Ξ′) = Set^S(J_S Ξ, T Ξ′); g ⊙ f := g^♯ ∘ f. It has finite coproducts by concatenation
Ξ ⋈ Ξ′, with coprojections inl, inr; f ⋈ Φ := ⟨inl ⊙ f, inr⟩. C(T) := Kl(T)^op. Presheaves on C(T)
are functors on Kl(T); T is one. Γ.A denotes context extension; the chapter writes Γ ⋈ [A].

---

## 1. Relative monads as natural models

**Definition 1.1** (Awodey, MSCS 2018, Def. 3; Prop. 2: equivalent to CwFs). A *natural model* on a
category with a terminal object is a representable map of presheaves p : Tm → Ty: for Γ and
A ∈ Ty(Γ) there are Γ.A, p_A : Γ.A → Γ and ν_A ∈ Tm(Γ.A) over A[p_A] such that every σ : Δ → Γ and
t ∈ Tm(Δ) over A[σ] have a unique ⟨σ, t⟩ : Δ → Γ.A with p_A ∘ ⟨σ, t⟩ = σ and ν_A[⟨σ, t⟩] = t.
Tm(Γ, A) is the fibre over A. A natural model is *contextual* if every object is uniquely an iterated
extension of the terminal object. Every natural model has a *contextualisation*: objects the finite
sequences (A₁, …, Aₙ) with A_i ∈ Ty(pt.A₁…A_{i−1}), morphisms and presheaves inherited from pt.A⃗; it
is contextual, and the functor (A⃗) ↦ pt.A⃗ is a fully faithful morphism of natural models. (Contextual
natural models are the C-systems; ALN, to be cited precisely. The word "C-system" is not used below.)

**Proposition 1.2.** Let T be a J_S-relative monad. On C(T) let Ty := S (constant) and
Tm := ⊔_s T(−)_s, with p the sorting. Then p is a contextual natural model: the pullback of p along
s : y(Ξ) → S is represented by Ξ ⋈ [s], with p_s = inl and ν_s = inr ∈ Kl(T)([s], Ξ ⋈ [s]) = T(Ξ ⋈ [s])_s.

*Proof.* Kl(T)(Ξ ⋈ [s], Δ) ≅ Kl(T)(Ξ, Δ) × T(Δ)_s, naturally in Δ, by the coproduct. ∎

*Remark.* Conversely a contextual natural model with constant types S is a J_S-relative monad
(T(Ξ)_s := Tm(Ξ, s), η the generic terms, ♯ substitution); the two constructions are inverse. Not
needed below. ACU 2015 does not state this; it is ours.

**Definition 1.3** (unit type). The natural model of T *with a unit type* is
  p⁺ : Tm ⊔ 1 → S ⊔ {⊤}
on C(T), with 1 sorted to ⊤. It is representable: the pullback of p⁺ along ⊤ : y(Ξ) → S ⊔ {⊤} is
represented by Ξ itself, with p_⊤ = id_Ξ, ν_⊤ = ⋆ and ⟨σ, ⋆⟩ = σ; along s ∈ S it is as in 1.2.

A hypothesis of type ⊤ carries no data, and extending a context by it adds no variable. This is the
only addition to Kl(T), and §5 forces it: an equation is a hypothesis without data.

---

## 2. Raw types

**Definition 2.1.** A *module of raw types* over T is a presheaf M on C(T) with a map
|−| : M → S ⊔ {⊤} to the constant presheaf, i.e. an (S ⊔ {⊤})-sorted T-module. A type A ∈ M(Ξ)_s
has sort |A| := s; types of sort ⊤ are *silent*.

**Definition 2.2** (raw natural model). R(T, M) is the contextualisation of the pullback of the
natural model of T with a unit type (1.3) along the sorting |−| : M → S ⊔ {⊤}. The pullback is a
natural model by Awodey, Cor. 4 (representable maps are stable under pullback along any map into
the base), and the contextualisation of a natural model is one.

*Remark.* Read as a C-system, R(T, M) is C(T⁺, M) of `def:sorted-c-system`, for the relative monad
T⁺ on J_{S ⊔ {⊤}} with T⁺(Ξ)_⊤ := 1 and T⁺(Ξ)_s := T(Ξ⁻)_s, where Ξ⁻ deletes the ⊤-variables; so
`prop:sorted-c-system` is a corollary of 2.2. T⁺ is not used below.

**Unwinding.** Objects: raw contexts Γ = (A₁, …, Aₙ) with A_i ∈ M(Γ_{<i}^↓), where Γ^↓ ∈ Kl(T), the
underlying object, is the list of the sorts of the non-silent entries of Γ. Morphisms Δ → Γ:
Kl(T)(Γ^↓, Δ^↓). Types over Γ: M(Γ^↓). Terms of A over Γ: T(Γ^↓)_{|A|} if |A| ∈ S, and {⋆} if A is
silent. Γ.A appends A; p_A = inl, resp. id; ν_A = inr, resp. ⋆; ⟨σ, t⟩ is
copairing, resp. σ.

**Sort-degeneracy.** Let R₀ := R(T, 1), the raw natural model with one type per sort, and
ε : R → R₀ the morphism induced by M → 1. Then ε is bijective on every fibre Tm_R(Γ, A), and Ty_R(Γ)
depends only on ε(Γ): a raw term of A is a raw term of every type of the same sort, over every
context with the same sorts. This is the meaning of "raw", and the only property of R used in §3
besides contextuality.

---

## 3. Typings

Fix T and M; R := R(T, M); Γ, Δ range over raw contexts.

**Definition 3.1** (raw judgements). Γ ⊢ A (A ∈ Ty_R(Γ)); Γ ⊢ t : A (t ∈ Tm_R(Γ, A)); Γ ⊢ A ≡ A′
(A, A′ ∈ Ty_R(Γ), |A| = |A′|); Γ ⊢ t ≡ t′ : A (t, t′ ∈ Tm_R(Γ, A)). A *set of judgements* is a set J
of raw judgements.

**Definition 3.2** (derived forms; finite conjunctions of raw judgements, by recursion on length).
- ⊢ (); ⊢ Γ.A := ⊢ Γ and Γ ⊢ A.
- Δ ⊢ σ : Γ, for σ : Δ → Γ in R: Δ ⊢ () : () := ⊢ Δ; Δ ⊢ ⟨σ, t⟩ : Γ.A := Δ ⊢ σ : Γ, Γ ⊢ A, Δ ⊢ t : A[σ].
  (Every σ : Δ → Γ.A is uniquely ⟨p_A ∘ σ, ν_A[σ]⟩.)
- Γ ≡ Γ′: () ≡ (); Γ.A ≡ Γ′.A′ := Γ ≡ Γ′ and Γ ⊢ A ≡ A′. (Then Γ^↓ = Γ′^↓, so A′ ∈ Ty_R(Γ).)
- Δ ⊢ σ ≡ σ′ : Γ: () ≡ (); ⟨σ, t⟩ ≡ ⟨σ′, t′⟩ := Δ ⊢ σ ≡ σ′ : Γ and Δ ⊢ t ≡ t′ : A[σ].

**Definition 3.3** (typing). A set of judgements is a *typing* if:
- (T0) *presupposition*: Γ ⊢ A implies ⊢ Γ; Γ ⊢ t : A implies Γ ⊢ A;
- (T1) *substitution*: Δ ⊢ σ : Γ and Γ ⊢ A imply Δ ⊢ A[σ]; Δ ⊢ σ : Γ and Γ ⊢ t : A imply Δ ⊢ t[σ] : A[σ];
- (T2) *variables*: Γ ⊢ A implies Γ.A ⊢ p_A : Γ and Γ.A ⊢ ν_A : A[p_A];
- (E1) *equivalence*: ≡ on types over Γ and on terms of A over Γ is an equivalence relation on the
  well-formed ones, i.e. Γ ⊢ A ≡ A′ implies Γ ⊢ A and Γ ⊢ A′, Γ ⊢ A implies Γ ⊢ A ≡ A, symmetry,
  transitivity; likewise for terms;
- (E2) *congruence*: Γ ⊢ A ≡ A′ and Δ ⊢ σ ≡ σ′ : Γ imply Δ ⊢ A[σ] ≡ A′[σ′]; Γ ⊢ t ≡ t′ : A and
  Δ ⊢ σ ≡ σ′ : Γ imply Δ ⊢ t[σ] ≡ t′[σ′] : A[σ];
- (E3) *conversion*: Γ ⊢ t : A and Γ ⊢ A ≡ A′ imply Γ ⊢ t : A′; Γ ⊢ t ≡ t′ : A and Γ ⊢ A ≡ A′ imply
  Γ ⊢ t ≡ t′ : A′.

In natural-model terms, (T0)–(T2) say that the well-formed contexts, substitutions, types and terms
form a sub-natural-model W ⊆ R, determined by its types and terms because substitutions are
componentwise; (E1)–(E2) say that ≡, extended componentwise, is a congruence on W; (E3) says that it
is conversion-closed.

**Lemma 3.4.** In a typing: identities are well formed and well-formed substitutions compose
(componentwise, by T1, T2); if Γ ≡ Γ′ then id : Γ′ → Γ is well formed, hence every judgement over Γ
holds over Γ′ (induction on length, using E3 at the last entry, then T1); σ ≡ σ′ implies
A[σ] ≡ A[σ′] (E2 with E1); and if Δ ≡ Δ′ and Γ ≡ Γ′, then Δ ⊢ σ : Γ iff Δ′ ⊢ σ : Γ′, and
Δ ⊢ σ ≡ σ′ : Γ iff Δ′ ⊢ σ ≡ σ′ : Γ′ (the raw substitutions Δ → Γ and Δ′ → Γ′ are the same set).

**Proposition 3.5** (lattice). Each condition of 3.3 is a Horn clause in the raw judgements, so
typings are closed under arbitrary intersections, the set of all raw judgements is a typing, and for
every set X of Horn rules there is a least typing closed under X.

(E3) is a Horn clause only because of sort-degeneracy: t ∈ Tm_R(Γ, A′) is a raw judgement. In a
natural model that is not sort-degenerate it reads "some t′ ≡ t lies in Tm(Γ, A′)", Voevodsky's
lifting condition, which is existential.

**Proposition 3.6** (quotient). For a typing (W, ≡), let Ctx := W/≡ be given by
- objects: the classes [Γ] of well-formed contexts under Γ ≡ Γ′;
- morphisms: Ctx([Δ], [Γ]) := {σ | Δ ⊢ σ : Γ} / (Δ ⊢ σ ≡ σ′ : Γ), with [θ] ∘ [σ] := [θ ⊙ σ];
- types: Ty([Γ]) := {A | Γ ⊢ A} / (Γ ⊢ A ≡ A′), with [A][σ] := [A[σ]];
- terms: Tm([Γ], [A]) := {t | Γ ⊢ t : A} / (Γ ⊢ t ≡ t′ : A), with [t][σ] := [t[σ]];
- [Γ].[A] := [Γ.A], p_{[A]} := [p_A], ν_{[A]} := [ν_A].
Then Ctx is a contextual natural model, and [−] : W → Ctx is a surjective morphism of natural models
with kernel ≡.

*Proof.* The hom-sets, type sets and term sets do not depend on the representatives Δ, Γ, A, by
Lemma 3.4 and (E3). Composition and the actions are well defined by (E2), applied componentwise for
θ ⊙ σ; extension is well defined by the definition of ≡ on contexts. Representability: given
[σ] : [Δ] → [Γ] and [t] ∈ Tm([Δ], [A][σ]), choose representatives; by (E3) Δ ⊢ t : A[σ], so ⟨σ, t⟩ is
well formed, and its class is independent of the choices since ≡ on substitutions is componentwise.
Uniqueness: a τ with [p ∘ τ] = [σ] and [ν[τ]] = [t] equals ⟨p ∘ τ, ν[τ]⟩ in R, which is ≡ ⟨σ, t⟩
componentwise. Contextuality: [Γ.A] = [Γ′.A′] iff Γ ≡ Γ′ and A ≡ A′. ∎

**Proposition 3.7** (span). For a typing (W, ≡), R ↩ W ↠ Ctx: the first a monomorphism of contextual
natural models, the second surjective with kernel ≡. The composite relation R ⇀ Ctx is the typing
relation, defined exactly on well-formed data. In general there is no functor Ctx → R.

**Definition 3.8** (subquotients). A *subquotient* of R is a sub-natural-model W ⊆ R together with a
surjective morphism of contextual natural models q : W → Q (surjective on contexts, substitutions,
types and terms) with ker q ⊆ ker ε, i.e. q identifies only data of the same sort. (These are
Voevodsky's regular subquotients: regularity is the statement that q is a morphism.) For
q(Γ) = q(Γ′) and q(A) = q(A′), with A over Γ and A′ over Γ′, ε identifies Ty_R(Γ) with Ty_R(Γ′) and
Tm_R(Γ, A) with Tm_R(Γ′, A′). The subquotient is *saturated* if these identifications restrict to
bijections Ty_W(Γ) ≅ Ty_W(Γ′) and Tm_W(Γ, A) ≅ Tm_W(Γ′, A′) commuting with q.

**Proposition 3.9** (characterisation). (W, ≡) ↦ (W, [−] : W → W/≡) is a bijection between typings
on R and saturated subquotients of R up to isomorphism under W, with inverse (W, q) ↦ (W, ker q).

*Proof.* A typing gives a saturated subquotient by 3.6, (E3) and Lemma 3.4, with ker [−] = ≡.
Conversely, let (W, q) be saturated. ker q is componentwise on contexts and substitutions, since Q
is contextual and pairing in Q is unique. (W, ker q) satisfies (T0)–(T2) because W is a
sub-natural-model, (E1) because ker q is an equivalence relation on W, (E2) because q is a morphism,
and (E3) because of saturation. So it is a typing, and W/ker q → Q is a bijective morphism of
natural models, hence an isomorphism. The two constructions are inverse. ∎

*Remark.* Saturation is the conversion rule: a raw term has the same meaning at any two identified
types, and is well formed at one iff at the other. This is what "extrinsic" means. A subquotient
extends to a saturated one with the same quotient iff q is constant along the ε-identifications
between fibres of identified types; the saturation is then the largest W′ ⊇ W to which q extends.
Not every subquotient satisfies this: q may act on the fibre over A by a symmetry of the raw terms
relative to the fibre over A′ ≡ A, giving a quotient in which the same raw term has two meanings.
Such quotients are excluded by typings. Sort-degeneracy is what lets the conversion rule be stated
with the same raw term, which is what makes it Horn (3.5); this is all that remains of regularity.

**Remark 3.9** (monad form). Hom_W(Δ, Γ) is the dependent product of the Tm_W(Δ, A_i[σ_{<i}]), with
substitution as composition; so W is to the well-formed renamings what Kl(T) is to 𝔽↓S, and erasure
is a monad morphism to T.

---

## 4. Type theories

**Definition 4.1.** A *rule* over R is a Horn clause in the raw judgements of R: finitely many
premises and one conclusion, each a raw judgement or a derived form of 3.2 (a derived conclusion is
finitely many rules). A *type theory over T* is a module of raw types M together with a set X of
rules over R(T, M). Its *judgements* are the least typing on R(T, M) closed under X (Proposition 3.5),
and its *syntax* is the quotient Ctx (Proposition 3.6).

A type theory is specified by its raw types and its rules. Its structural rules are not specified:
they are (T0)–(E3), the conditions for the well-formed part to be a natural model and for the
quotient to be one. The judgements are inductively defined, so derivations are finite trees and
properties of judgements are proved by induction on derivations. If the structural rules of a system
are admissible rather than primitive, its judgement set is still a typing, and the system is a
*presentation* of the same type theory.

**Proposition 4.2** (morphisms out of the syntax). Let (M, X) be a type theory over T with
judgements J and syntax Ctx, and D a natural model.
1. If (W′, ≡′) is a typing on R closed under X and φ : W′ → D is a morphism of natural models with
   ≡′ ⊆ ker φ, then J ⊆ (W′, ≡′), and [x] ↦ φ(x) is a morphism Ctx → D.
2. If f, g : Ctx → D are morphisms of natural models and the judgements of J on which f and g agree
   are closed under X, then f = g.

*Proof.* (1) Leastness gives W ⊆ W′ and ≡ ⊆ ≡′ ⊆ ker φ, so the map is well defined, and it is a
morphism because φ is. (2) Let E be the judgements of J on which f and g agree: contexts and
substitutions componentwise, types with f[A] = g[A], terms with f[t] = g[t], equalities both of whose
sides lie in E. E is a typing: (T0)–(E3) hold because f and g preserve extension, p, ν and
substitution, and ≡ is inherited from J. E is closed under X by hypothesis and E ⊆ J, so E = J. ∎

So initiality of Ctx among models of a structure S reduces to: Ctx carries S; the structure used by
the rules of X is preserved by S-morphisms (then uniqueness is (2)); and, for every S-model D, a
typing closed under X mapping to D. The natural candidate is the *typing relation into D*: the raw
judgements validated by a partial interpretation ⟦−⟧_D of raw contexts, types and terms in D, with
≡_D := ker ⟦−⟧_D. For it, (E1)–(E3) hold because ≡_D is a kernel, (T2) and the extension structure
hold by the definition of ⟦−⟧_D, and closure under X is one check per rule; (T1) and (E2) are the
substitution lemma ⟦e[σ]⟧ = ⟦e⟧[⟦σ⟧]. That lemma is the whole syntactic content of initiality.

---

## 5. ToS^ω

### 5.1 Raw syntax, with kinds

K := {ty, tm} is the set of *kinds*: a slot of kind ty stands for a family, a slot of kind tm for an
element. This is the only syntactic distinction between the two, and it replaces the boundaries
sort and of(S) of the current chapter.

**Arities and sorts.** 𝔸 is the initial algebra of X ↦ List(X × K): an *arity* is a list of sorts,
and a *sort* is a pair (α, κ) of an arity and a kind. S := |𝔸| × K. The empty arity, concatenation
and rank are as in `def:arities`, with the kinds carried along. A *slot* of Γ of sort (α, κ) is a
position of Γ carrying (α, κ); Γ ∋ (α, κ) is the set of them; a *renaming* is a sort-preserving map
of positions. So 𝔸 with renamings is the category 𝔽↓S of the well-formed-syntax chapter, and the slot
functor Γ ↦ Γ ∋ − is J_S : 𝔸 → Set^S. The chapter's "for S = |𝔸| this is the slot functor" becomes
S = |𝔸| × K; nothing else in §§1–4 changes.

**Expressions.** Expr(Γ, κ) is defined inductively: for a slot x : Γ ∋ (α, κ) and arguments t with
t_i ∈ Expr(Γ ⋈ α_i, κ_i) for each sort (α_i, κ_i) of α, x(t) ∈ Expr(Γ, κ). The kind of an expression is
the kind of its head slot, and arguments respect the kinds of the slots they fill. 𝔼 : 𝔸 → Set^S,
𝔼(Γ)_{(α,κ)} := Expr(Γ ⋈ α, κ), is a J_S-relative monad with η_x the η-expansion and ♯ hereditary
substitution; both preserve kinds, and the proofs of the monad laws go through unchanged, since
kinds are inert. This is the list carrier over the result types K of the formalisation
(`Carrier.lean`). A morphism Γ → Δ of Kl(𝔼) is a substitution: one expression in Expr(Δ ⋈ α, κ) for
each slot of Γ of sort (α, κ). (Kl(𝔼)^op is the free cartesian closed category on the set K of
objects, in canonical form; cf. the commented remark in `raw-syntax.tex`. Not used.)

Two lemmas of the raw-syntax chapter are used:
- (B) *currying*: 𝔼(Ξ)_{(α,κ)} = 𝔼(Ξ ⋈ α)_{([],κ)}, and the action of f : Ξ → Ξ′ at sort (α, κ) is the
  action of f ⋈ α at sort ([], κ) (`lem:depth-derived`);
- (C) *instantiation*: η_x[⟨id, t⟩] = x(t) for x : Ξ ∋ (α, κ) and t : α ⇝ Ξ (`act_copair_eta`).

### 5.2 Raw types: hypothetical conclusions

A *conclusion* over an arity Ξ is one of
  type;   S ∈ Expr(Ξ, ty);   l ≡_c r, with c a conclusion of the first two forms and l, r ∈ Expr(Ξ, κ_c),
where κ_type := ty and κ_S := tm are the *kinds of the conclusions*. These are Cartmell's judgement forms: a family, an element of S, an
equation between families or between elements of S. The equation carries c because the judgement
Γ ⊢ l ≡ r : c does. For c non-equational, Expr(Ξ, c) := Expr(Ξ, κ_c).

By simultaneous recursion: an *entry* over Ξ is [Θ]c with Θ a telescope over Ξ of arity γ and c a
conclusion over Ξ ⋈ γ; its sort is (γ, κ_c) ∈ S for c non-equational and ⊤ for an equation. A
*telescope* over Ξ is a list of entries, each over Ξ extended by the sorts of the entries before it;
Θ^↓ is the arity of its slot entries. An entry is a hypothetical
judgement: the conclusion c under the hypotheses Θ. An equational entry binds no slot.

M(Ξ) := the entries over Ξ, sorted as above, with substitution at depth as the action
(`def:action-decorations`). M is the closure of the conclusions under hypothesising; it is
determined by the three conclusion forms.

### 5.3 The raw natural model

R := R(𝔼, M). Raw contexts are telescopes over the empty arity. Terms:
  Tm_R(Γ, [Θ]c) = Expr(Γ^↓ ⋈ Θ^↓, c) for c non-equational;   Tm_R(Γ, [Ψ](l ≡_c r)) = {⋆}.
By (B), on the nose, Tm_R(Γ, [Θ]c) = Tm_R(Γ.Θ, []c), where []c is the entry with the empty telescope
and Γ.Θ is Γ extended by Θ. Abbreviations at empty telescopes: Γ ⊢ S type for Γ ⊢ S : []type,
Γ ⊢ e : S for Γ ⊢ e : []S, Γ ⊢ l ≡ r : c for Γ ⊢ l ≡ r : []c, Γ ⊢ c ≡ c′ for Γ ⊢ []c ≡ []c′ (vacuous
for c = c′ = type). These are Martin-Löf's four forms; the entry-level forms are the same forms at a
telescope.

### 5.4 Rules

**Figure 5.1** (the rules of ToS^ω). Γ a raw context, Θ, Ψ telescopes, c, c′ non-equational
conclusions, S, S′ type expressions; ⊢ Γ.Θ and Θ ≡ Θ′ as in 3.2. A row with ⟺ is two rules.

```
Formation
  ⊢ Γ.Θ                                                  ⟹  Γ ⊢ [Θ]type
  Γ.Θ ⊢ S type                                           ⟹  Γ ⊢ [Θ]S
  Γ.Ψ ⊢ l : c,   Γ.Ψ ⊢ r : c                             ⟹  Γ ⊢ [Ψ](l ≡_c r)
Congruence
  Θ ≡ Θ′                                                 ⟹  Γ ⊢ [Θ]type ≡ [Θ′]type
  Θ ≡ Θ′,   Γ.Θ ⊢ S ≡ S′ type                            ⟹  Γ ⊢ [Θ]S ≡ [Θ′]S′
  Ψ ≡ Ψ′,   Γ.Ψ ⊢ c ≡ c′,   Γ.Ψ ⊢ l ≡ l′ : c,   Γ.Ψ ⊢ r ≡ r′ : c
                                                         ⟹  Γ ⊢ [Ψ](l ≡_c r) ≡ [Ψ′](l′ ≡_{c′} r′)
Binding
  Γ.Θ ⊢ e : c                                            ⟺  Γ ⊢ e : [Θ]c
  Γ.Θ ⊢ e ≡ e′ : c                                       ⟺  Γ ⊢ e ≡ e′ : [Θ]c
Equations
  Γ.Ψ ⊢ l ≡ r : c                                        ⟺  Γ ⊢ ⋆ : [Ψ](l ≡_c r)
```

Each rule is forced by the reading of an entry as a hypothetical judgement: an entry is well formed
iff its conclusion is well formed under its hypotheses; the entry formers are congruences; by (B) a
term of [Θ]c and a term of c over Γ.Θ are the same datum, so the judgements agree; ⋆ is evidence for
an equation iff the equation holds.

**Definition 5.1** (ToS^ω). The type theory over 𝔼 with raw types M and rules Figure 5.1. Its
judgements are the least typing on R closed under Figure 5.1; Ctx is its syntax.

**Proposition 5.2** (inversion). In the judgements of ToS^ω the converses of the formation and
congruence rules hold. Hence every row of Figure 5.1 is a biconditional: a judgement at [Θ]c over Γ
holds iff the corresponding judgements at []c over Γ.Θ and at the entries of Θ hold, so the judgements
are determined by their empty-telescope part.

*Proof.* Induction on derivations. An entry-level judgement is produced by a rule of Figure 5.1, where
the claim is immediate, or by (T0)–(E3): the substitution case is the substitution lemma for the
components, available because substitution is a condition; presupposition from an entry equality uses
the claim for equalities; conversion uses Lemma 3.4 for the components. Entry equalities are produced
only by the congruence rules and (E1)–(E3): reflection produces equalities between expressions. ∎

*Remark.* The converses that are rules are needed: Γ ⊢ e : [Θ]c ⟹ Γ.Θ ⊢ e : c makes slots usable
(below), and reflection Γ ⊢ ⋆ : [Ψ](l ≡_c r) ⟹ Γ.Ψ ⊢ l ≡ r : c is the only rule concluding an
equation between expressions from a non-equation. The converse of the second binding rule is
admissible.

**Derived rules.**
- *Use of a slot.* For an entry [Θ]c of Γ with variable x and Γ ⊢ t : Θ: (T2), (T1) give
  Γ ⊢ η_x : [Θ]c; binding gives Γ.Θ ⊢ η_x : c; (T1) along ⟨id, t⟩ gives Γ ⊢ η_x[⟨id, t⟩] : c[t], which
  by (C) is Γ ⊢ x(t) : c[t]. (Lean's `ap`.)
- *Hypotheses.* For an equational entry [Ψ](l ≡_c r) of Γ and Γ ⊢ t : Ψ: (T2), (T1), reflection and
  (T1) give Γ ⊢ l[t] ≡ r[t] : c[t]. (Lean's `hyp`.)
- *Refl*: Γ ⊢ l : c gives Γ ⊢ ⋆ : [](l ≡_c l), by (E1). *Irrelevance*: Tm_R(Γ, [Ψ](l ≡_c r)) = {⋆}.
- Weakening, substitution, conversion, functionality: (T1)–(E3).

### 5.5 The complete rule set

**Figure 5.2** (all rules of ToS^ω). The judgements of ToS^ω are the least set of raw judgements
closed under the following, where the derived forms are the abbreviations of 3.2 and the rules of
Figure 5.1 are included. In the instance, A[σ] and t[σ] are hereditary substitution at depth
(`def:action-decorations`), p_A is the renaming inl (the identity for an equational A), and ν_A is
the η-expansion of the last slot (⋆ for an equational A).

```
Derived forms (abbreviations)
  ⊢ ()                                 ⊢ Γ.A                  :=  ⊢ Γ,  Γ ⊢ A
  Δ ⊢ () : ()  :=  ⊢ Δ                 Δ ⊢ ⟨σ,t⟩ : Γ.A         :=  Δ ⊢ σ : Γ,  Γ ⊢ A,  Δ ⊢ t : A[σ]
  () ≡ ()                              Γ.A ≡ Γ′.A′            :=  Γ ≡ Γ′,  Γ ⊢ A ≡ A′
  Δ ⊢ () ≡ () : ()                     Δ ⊢ ⟨σ,t⟩ ≡ ⟨σ′,t′⟩ : Γ.A  :=  Δ ⊢ σ ≡ σ′ : Γ,  Δ ⊢ t ≡ t′ : A[σ]
  ⊢ Γ.Θ,  Γ ⊢ t : Θ,  Θ ≡ Θ′,  Γ ⊢ t ≡ t′ : Θ   the same, for telescopes

Structural rules (T0)–(E3)
  pre    Γ ⊢ A ⟹ ⊢ Γ                            Γ ⊢ t : A ⟹ Γ ⊢ A
  sub    Δ ⊢ σ : Γ,  Γ ⊢ A ⟹ Δ ⊢ A[σ]            Δ ⊢ σ : Γ,  Γ ⊢ t : A ⟹ Δ ⊢ t[σ] : A[σ]
  var    Γ ⊢ A ⟹ Γ.A ⊢ p_A : Γ                   Γ ⊢ A ⟹ Γ.A ⊢ ν_A : A[p_A]
  eq     Γ ⊢ A ≡ A′ ⟹ Γ ⊢ A,  Γ ⊢ A′             Γ ⊢ A ⟹ Γ ⊢ A ≡ A
         Γ ⊢ A ≡ A′ ⟹ Γ ⊢ A′ ≡ A                 Γ ⊢ A ≡ A′,  Γ ⊢ A′ ≡ A″ ⟹ Γ ⊢ A ≡ A″
         the same four for Γ ⊢ t ≡ t′ : A
  cong   Γ ⊢ A ≡ A′,  Δ ⊢ σ ≡ σ′ : Γ ⟹ Δ ⊢ A[σ] ≡ A′[σ′]
         Γ ⊢ t ≡ t′ : A,  Δ ⊢ σ ≡ σ′ : Γ ⟹ Δ ⊢ t[σ] ≡ t′[σ′] : A[σ]
  conv   Γ ⊢ t : A,  Γ ⊢ A ≡ A′ ⟹ Γ ⊢ t : A′     Γ ⊢ t ≡ t′ : A,  Γ ⊢ A ≡ A′ ⟹ Γ ⊢ t ≡ t′ : A′

Rules of ToS^ω: Figure 5.1
```

Eighteen structural schemes and twelve rules. Context conversion, weakening along any projection,
substitution of a single term, functionality, use of a slot and use of a hypothesis are derived.
The structural rules are those of `fig:structural-rules` with substitution along arbitrary
well-formed substitutions in place of W, S and δ, which generate them (every well-formed σ factors
through projections and single substitutions).

### 5.6 Locality and canonicity

**Locality.** Reflection is the only rule of Figure 5.2 whose conclusion is an equality between
expressions and whose premises contain none; its premise Γ ⊢ ⋆ : [Ψ](l ≡_c r) comes, by inspection
of the rules concluding such a judgement, from an equational entry of some context by var, sub, conv
and the equation rule. So ≡ is the congruence generated by the equational entries of the contexts,
instantiated along well-formed substitutions: over Γ, it is the theory that Γ presents.

**Conjecture 5.3** (canonicity). If Γ has no equational entry, then Γ ⊢ u ≡ u′ : c implies u = u′,
and Γ ⊢ A ≡ A′ implies A = A′; so over such Γ the quotient W → Ctx is injective.

The natural attempts fail: an induction on derivations of the strengthened statement "u[σ] = u′[σ]
for every well-formed σ into an equation-free context" meets, in the var case, a component
Γ′ ⊢ ⋆ : A[σ₀] of σ whose derivation is unrelated to the one being inducted on; and the relation
"equal after every instantiation into an equation-free context" is strictly coarser than ≡ (take
Γ = (A : type, B : type, a : A, b : A, h : [x : B](a ≡_A b)): a and b agree after every such
instantiation, since each one supplies a ≡ b under x : B, but a ≢ b over Γ, as B has no element), so
it cannot serve as a model. Nothing below depends on the conjecture.

### 5.7 The syntax

Ctx is a contextual natural model with:
- types the hypothetical conclusions: Ty(Γ) = ⊔_Θ Concl(Γ.Θ)/≡;
- strict Π over telescopes: Tm(Γ, [Θ]c) = Tm(Γ.Θ, []c), by the binding rules in both directions;
- a universe U := []type with El(S) := []S, both strict under substitution, with Tm(Γ, U) the
  well-formed families over Γ; U is not an element of U;
- extensional, proof-irrelevant equality: Tm(Γ, [Ψ](l ≡_c r)) = {⋆} if Γ.Ψ ⊢ l ≡ r : c and ∅ otherwise.

In a general natural model with U, El, Π over telescopes with strict currying, and Id at U and at
El S with reflection and irrelevance, [Θ]type is Π_Θ U, [Θ]S is Π_Θ El(S) and [Ψ](l ≡_c r) is
Π_Ψ Id_c(l, r). This is the structure the GAT HrS of the previous plan named.

**Initiality** (to prove for this design). Let HrS be the GAT of natural models with a Tarski
universe U, El, a Π with currying lam : Tm(Γ.A, B) ≅ Tm(Γ, Π A B) : unlam, and Id at U and at El S
with refl, reflection and irrelevance, all stable under substitution. Ctx is an HrS-model by the
above, with Π_Θ the iterated Π and lam, unlam identities. *Theorem (to prove):* Ctx is initial among
HrS-models. By Proposition 4.2 the proof consists of:
1. the partial interpretation ⟦−⟧_D of raw syntax in an HrS-model D. It is type-directed: for an
   expression e over a raw context Γ′, ⟦e⟧_{Γ′} ∈ Tm(⟦Γ′⟧, ⟦c⟧) with c synthesised, by recursion on
   𝔼: ⟦x(t)⟧_{Γ′} = unlam^k(ν_x)[⟨id, ⟦t⟧⟩], defined when ⟦t⟧ is and the types match in D; and
   ⟦type⟧ = U, ⟦S⟧ = El ⟦S⟧, ⟦l ≡_c r⟧ = Id_{⟦c⟧}(⟦l⟧, ⟦r⟧), ⟦[Θ]c⟧ = Π_{⟦Θ⟧} ⟦c⟧ (iterated Π),
   ⟦e at [Θ]c over Γ⟧ = lam_Θ ⟦e⟧_{Γ.Θ}, ⟦⋆⟧ = refl. Strictness of currying in Ctx is no obstacle:
   lam_D and unlam_D are inserted at each binding, and the binding rule holds by definition. The
   variable rule requires the η-lemma ⟦η_x⟧ = ν_x, by well-founded induction on rank using
   lam ∘ unlam = id (`Typing/Eta.lean` in the current design);
2. the substitution lemma ⟦e[σ]⟧ = ⟦e⟧[⟦σ⟧], by the well-founded recursion of hereditary
   substitution; this makes the typing relation into D a typing;
3. the twelve rules of Figure 5.1, one check each in D (binding is lam/unlam; the equation rule is
   refl and reflection; irrelevance makes ⟦⋆⟧ the only term);
4. uniqueness by 4.2(2), since HrS-morphisms preserve everything Figure 5.1 uses.
Item 2 is the only syntactic work and is what the Lean development proves for the current design
(`Initiality/Substitution.lean`); items 3 and 4 replace its soundness, descent and uniqueness
inductions. The term-model theorem for GATs gives a different presentation of the initial HrS-model,
with explicit substitutions and lam/unlam as constructors; identifying it with Ctx is the content of
this theorem, not a citation.

---

## 6. Raw and well-typed syntax

Kl(𝔼) is the category of free higher-rank structures: arities and substitutions. Ctx is the
category of finitely presented ones: a well-formed context is a presentation, with generators the
slot entries and relations the equational entries; a morphism Δ → Γ is an interpretation of the
presentation Γ in Δ; two interpretations are equal when they agree modulo the theory of Δ. Raw syntax
relates to well-typed syntax as free algebras relate to finitely presented algebras.

**Theorem 6.1** (span; 3.7). R ↩ W ↠ Ctx, a monomorphism and a surjection of contextual natural
models with kernel ≡; the typing relation R ⇀ Ctx is defined exactly on well-formed data; there is no
functor Ctx → R.

**Theorem 6.2** (locality; 5.6). Over Γ, ≡ is the congruence generated by the equational entries of
Γ: Ctx(Γ) = W(Γ)/Th(Γ). Conjecturally (5.3), over equation-free Γ it is syntactic identity.

**Theorem 6.3** (universality; 5.7, to prove). Ctx is the initial contextual natural model with
strict Π over telescopes, a universe, and extensional proof-irrelevant equality at U and El. So 6.1
and 6.2 describe the initial model: its elements are well-formed canonical forms, and its equality is
the word problem of each context.

---

## 7. What remains

1. Lemma 3.4, Propositions 3.6 and 3.9: routine, a page.
2. Proposition 5.2: the induction on derivations; the substitution case is the substitution lemma
   for components.
3. Conjecture 5.3: open. Either a measure for the induction, or a model.
4. Initiality (Theorem 6.3) for the new design, via Proposition 4.2: the partial interpretation and
   its substitution lemma (the Lean proof needs the kinds K as its result types and equations as entries
   without a slot; the recursion is otherwise the same), twelve rule checks, uniqueness by leastness.
5. Presentation theorem: the syntax-directed system for the new design is a typing closed under
   Figure 5.1 (weakening, substitution lemma, conversion), hence equal to ToS^ω.
6. Property (B) with kinds, and (C): check against the raw-syntax chapter; the chapter's arities,
   slots and expressions acquire the kind parameter (§5.1).
7. Equations between higher-rank slots are stated in η-long form [Ψ ⋈ Θ](F(x⃗) ≡ G(x⃗)); this is
   function extensionality and is the only form the design admits.
8. Terminology: "typing" (3.3), "type theory over T" (4.1), "conclusion", "entry", "equational entry".

## 8. Dictionary from the current chapter

| current | here |
|---|---|
| boundaries sort, of(S), eq(l,r); entries [Θ]β | conclusions type, S, l ≡_c r; entries [Θ]c, equations without a slot |
| def:sorted-c-system, prop:sorted-c-system | R(T, M): a unit type adjoined, pullback along the sorting, contextualised (1.3, 2.2) |
| B-frames, B-sets, f^†, π_f, W, S, δ, Props 4.3/5.4, AENR | nothing; typings (3.3) |
| regular congruence, componentwise subquotient | typings = saturated subquotients (3.8, 3.9) |
| structural rules figures | the unwinding of 3.3 (Figure 5.2) |
| GAT S, raw realisation ρ, S-closed, HrS | nothing; Figure 5.1 |
| reflection, refl, irrelevance; junk fillers; saturation | the equation rule; {⋆}; nothing |
| syntax-directed rules (Lean) | a presentation (7.5) |
| initiality (Lean) | to redo, same shape (7.4) |

## 9. Citations

Verified: Awodey, *Natural models of homotopy type theory*, MSCS 28 (2018) 241–286, Def. 3, Prop. 2,
Cor. 4. To cite precisely: ALN for contextual natural models as C-systems. Not to cite: ACU 2015 for
the remark after 1.2. Palmgren–Vickers (APAL 145, 2007, Thm 22) only if the term-model analogy is
mentioned.
