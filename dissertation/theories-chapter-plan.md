# Chapter 4, Theories: plan

Proposal, 2026-11-17. Design history: `theories-plan.md` (cited N). Paper proofs:
`HigherRankSyntax/positive-theories-and-initiality.md` (cited PT), to be re-based on the current
ToS^ω. Marks: [PT], [N] proved on paper there; [new] to prove; [cite] to verify.

**Thread.** A theory is a signature with a choice of contexts. If its operations bind over contexts
only, a model is a functor on a category of syntax, the syntax itself is the representable functor,
and initiality is the Yoneda lemma; such theories are the GATs. If its operations bind over
functions, models still exist, homomorphisms are logical relations, and they compose under a
variance condition; compact Hausdorff spaces arise this way, and no GAT has them as models.

**Input.** Chapter 3, as a black box: Syn is initial in Mod(ToS^ω); ⟦−⟧_D : Syn → D is the unique
morphism. Chapter 2: contextual natural models; inversion.

---

## 1. Signatures

*Written into `chapters/theories.tex` on 2026-11-17 (Definitions 4.1–4.10 in the scratch build).
Differences from the outline below: the syntax over Ξ is written Syn_{/Ξ}, since Syn_𝒯 already
denotes the syntax of a type theory; the proof of 1.2 goes through a lemma on contextual slices
𝒟_{/G} of a model and their base change g^*, with weakening = base change along Ξ → pt and the
generic model δ_Ξ = the diagonal; the classified morphism is written ⟦−⟧_M, with explicit formulas;
1.3 comes with a proof sketch and a definition of the points of a telescope.*

**1.1 Definition.** A *signature* is an object Ξ of Syn: a closed telescope of sort slots
`S : [Θ] type`, element slots `c : [Θ] B` and equations `[Θ](l = r)`. A *model of Ξ in* a model D of
ToS^ω is a global element of ⟦Ξ⟧_D.

**1.2 Proposition (classifying model)** [N 1.3, proved]. Let Syn_Ξ be the contextual slice of Syn
over Ξ: objects Ξ.Θ, morphisms over Ξ. It is a model of ToS^ω, the diagonal δ is a model of Ξ in
it, and evaluation at δ is a bijection

    Mod(ToS^ω)(Syn_Ξ, D)  ≅  { models of Ξ in D },        natural in D.

Write ⟦−⟧_M : Syn_Ξ → D for the morphism classified by M. So Syn_Ξ is Syn with a generic model of Ξ
adjoined. The proof is two lines from the black box; nothing else in the chapter uses Chapter 3.

**1.3 Lemma (presheaf models)** [cite Hofmann–Streicher; routine]. For a small category 𝒩 the
presheaves on 𝒩 form a model 𝐏(𝒩) of ToS^ω: types are families, sorts the small families, Π the
dependent product, Id the equaliser. 𝐒 := 𝐏(1) is the model in sets. For a model M of Ξ in 𝐏(𝒩)
and a telescope Θ over Ξ, the presheaf ⟦Θ⟧_M consists of the *points* of Θ: at I, the fillings of
Θ in M over I.

---

## 2. Theories and models

**2.1 Definition (theory).** A *theory* T = (Ξ, 𝒫) is a signature with a class 𝒫 of types of Syn_Ξ
closed under substitution, the *admissible* types. They are the types of the variables of T.

**2.2 Definition (contexts, positive chains).** An entry `[Φ]c` is *positive* if c is an element
`x : B` or an element equation `l =_B r`, and Φ is a telescope of positive admissible types. A
*context* of T is a telescope of admissible types, a *positive chain* a telescope of positive
entries. 𝒞_T and 𝒫os_T are the full subcategories of Syn_Ξ on them. Both are contextual natural
models, with the admissible types, resp. the positive entries, as types.

A context declares variables. A positive chain declares parameters, each an element or an equation
in a context: `A : ty, B : [x : tm(A)] ty`.

**2.3 Definition (model)** [PT 4.1, plus contextuality]. A *model* of T is a small category 𝒩 with
a terminal object ⊤, a model M of Ξ in 𝐏(𝒩), and a structure of contextual natural model on 𝒩
whose types and terms are the admissible types of M and their elements:

    Ty(I)          =  { [A, θ] :  Θ a positive chain,  A ∈ 𝒫(Θ),  θ ∈ ⟦Θ⟧_M(I) },   [A[σ], θ] = [A, ⟦σ⟧θ]
    Tm(I, [A, θ])  =  ⟦A⟧_M(I, θ)

So 𝒩 is the category of contexts of the model, and a variable of admissible type is interpreted by
context extension. Everything else is interpreted in presheaves: a binder over a non-admissible
entry ranges over all functions.

**2.4 Examples.** 𝒫 = ∅: 𝒩 = 1 and a model is a model of Ξ in sets. Untyped λ with `tm`
admissible: an abstract clone with `lam : Tm(n+1) → Tm(n)` and `app`. Type theory with `tm(A)`
admissible: a C-system with the type formers.

---

## 3. Positive theories

**3.1 Definition** [PT 3.3]. T is *positive* if the binder of every slot of Ξ is a positive chain
and every admissible type is positive. So T binds over contexts only: no function variables, no
sort variables, no sort equations as hypotheses. Then 𝒞_T ⊆ 𝒫os_T.

**3.2 Lemma (binding over a context)** [PT 2.3]. If A over y(I) is represented by I.A, then
Π(A, C)(I) ≅ C(I.A). Hence the points of a positive entry `[Φ]c` at I are the points of c at I.Φ.

**3.3 Lemma (expressions over positive chains)** [PT 3.5, from inversion]. Over a positive chain
every sort is S(t) for a sort slot S of Ξ, and every element is c(t) for an element slot c of Ξ or
a variable c.

**3.4 Definition (points, homomorphisms).** The *functor of points* of a model M is

    M(−) : 𝒫os_T → Set,        M(Θ) := ⟦Θ⟧_M(⊤).

It is a morphism of natural models 𝒫os_T → 𝔽am. A *homomorphism* M → M' is a natural
transformation M(−) ⇒ M'(−). Mod(T) is the resulting category, a full subcategory of [𝒫os_T, Set].

**3.5 Proposition (homomorphisms unfolded)** [PT 5.3; the converse is new]. A homomorphism is a
morphism F : 𝒩 → 𝒩' of natural models with functions S_M(θ) → S_{M'}(φθ) between the sorts in
every context, compatible with substitution, commuting with the operations and respecting the sort
equations. For type theory: a strict morphism of C-systems with the type formers.

**3.6 Theorem (the syntax is a model)** [PT 6.2–6.4]. There is a model 𝒮_T of T on 𝒩 = 𝒞_T whose
points are the substitutions:

    ⟦Δ⟧_{𝒮_T}(Θ)  ≅  Syn_Ξ(Θ, Δ),        natural in the context Θ and the positive chain Δ.

In particular 𝒮_T(−) ≅ 𝒫os_T(⊤, −).
*Proof.* Along the slots of Ξ: S(t) is interpreted by the set of its terms, c(t) by itself. The
bijection is proved by induction on positive entries, with 3.2 at binders and 3.3 at expressions.

**3.7 Theorem (initiality).** For T positive, 𝒮_T is initial in Mod(T). The unique homomorphism
𝒮_T → M is the interpretation σ ↦ ⟦σ⟧_M.
*Proof.* Mod(T)(𝒮_T, M) ≅ Nat(𝒫os_T(⊤, −), M(−)) ≅ M(⊤) = 1, by 3.6 and the Yoneda lemma. ∎

**3.8 Corollary (free models).** For a positive chain Θ, T[Θ] := (Ξ.Θ, 𝒫) is positive, and 𝒮_{T[Θ]},
as a model of T, has points 𝒫os_T(Θ, −). So Mod(T)(𝒮_{T[Θ]}, M) ≅ M(Θ): it is the model freely
generated by a point of Θ, and Θ ↦ 𝒮_{T[Θ]} is a full embedding 𝒫os_T^op → Mod(T).

**3.9 Corollary (completeness).** Two parallel morphisms of 𝒫os_T, in particular two terms over a
positive chain, are equal iff they are equal in every model. (Take M = 𝒮_{T[Θ]}.)

---

## 4. Positive theories and GATs

**4.1 Definition.** A *GAT* is a theory with no admissible types whose slots bind variables `x : B`
and equations only; equivalently, a positive theory with 𝒫 = ∅. (Cartmell's GATs with equational
premises; the theory of natural models of Chapter 2 is one.) Its models are its models in sets,
3.4 gives the usual homomorphisms, and 𝒫os_T is its syntactic category with equation types [cite
Cartmell].

**4.2 Theorem (functorial semantics)** [new; N 7.1]. Let T be positive. A functor 𝒫os_T → Set is
isomorphic to the functor of points of a model iff it preserves the terminal object and context
extension, i.e. finite limits. Hence

    Mod(T)  ≃  NM(𝒫os_T, 𝔽am)  ≃  Lex(𝒫os_T, Set).

*Proof plan.* ⇒: evaluation at ⊤ preserves limits. ⇐: for such a G, repeat the proof of 3.6 with
the fibres of G in place of the hom-sets of Syn_Ξ: the contexts of the model are the contexts of T
at the points of G, S(t) is interpreted by a fibre of G, and G is the functor of points. 3.6 is the
case G = 𝒫os_T(⊤, −). Alternative: unfold Mod(T) as an essentially algebraic theory [N 3.4, 6.2];
then G is a filtered colimit of representables, which are models by 3.8.

**4.3 Corollary (positive theories are GATs).**
(a) A GAT U is a positive theory, with the same models.
(b) A positive theory T has the models of the GAT 𝔾_T presented by the contextual category 𝒫os_T
[cite Cartmell]: its sorts are the positive entries of T, its terms the terms of T. A binder has
become a context.
(c) 𝔾 of a GAT is that GAT; (𝔾_T, ∅) has the models of T. The two translations are mutually
inverse up to equivalence of categories of models.
(d) Mod(T) is locally finitely presentable, with the 𝒮_{T[Θ]} as finitely presentable generators,
and 3.7 says that the initial lex functor is the representable one.

**4.4 Examples.** One admissible sort: abstract clones ≃ Lawvere theories. Untyped λ:
`Tm(n), var, sub, lam, app`. Type theory: 𝔾_T is the theory of B-systems with the type formers, and
4.2 is B-systems ≃ C-systems [Ahrens–Emmenegger–North–Rijke, verified].

**4.5 Remarks.** (i) 𝔾_T can have countably many sorts for finite T; the category of Lawvere
theories is not the category of models of a GAT with finitely many sorts [N 7.2]. (ii) SOGATs are
the positive theories of second order whose admissible types are sorts [N 4.1; cite Kaposi–Xie,
Uemura]. Positive theories add unbounded rank, admissible Π-types and equational hypotheses, and by
4.2 no new categories of models.

---

## 5. Beyond positivity: compact Hausdorff spaces

Theories with no admissible types; a model is a model of Ξ in sets. Binders range over functions.

**5.1 Definition (homomorphisms)** [PT A.1 at 𝒩 = 1; N 4.3]. Let 𝐅 be the model of ToS^ω in spans
of sets whose sorts are functions: contexts and types are spans Γ ← Γ^R → Γ', a sort is a pair of
sorts with a function between them, and its elements are related along the graph; Π and Id as in
presheaves. Both projections 𝐅 → 𝐒 are morphisms of models. A *homomorphism* M → M' is a model of Ξ
in 𝐅 over (M, M'). Unfolded: functions h_S between the sorts such that every operation of M is
related to that of M', where a ~ a' at S iff h_S(a) = a', and f ~ f' at `[Φ]c` iff f and f' send
related fillings of Φ to related values.

**5.2 Proposition.** (a) For a GAT these are the homomorphisms of 3.4 [PT A.7]. (b) Invertible ones
are the transports of structure. (c) They need not compose [N 4.3, checked]: for
`X : type, c : [f : [x:X]X] X` there are models on {0}, {0,1}, {0,1,2} whose inclusions are
homomorphisms while the composite inclusion is not.

**5.3 Definition (finite sort).** A sort `F : type` is *finite* if Ξ presents it as a finite
coproduct of units: constants `c_1, …, c_n : F` and `case : [B : type, b_1 … b_n : B, x : F] B`
with `case(B, b, c_i) = b_i` and `g(x) = case(B, g(c_1), …, g(c_n), x)` for `g : [x : F] B`.
*Lemma.* In every model F has exactly the n elements c_i, and every homomorphism is bijective on F.

**5.4 Definition (covariance).** An entry `[Φ]c`, with c an element or an element equation, is
- *covariant* if every entry of Φ is contravariant;
- *contravariant* if c is over a finite sort and every entry of Φ is covariant.

So inside a covariant entry only finite sorts occur at odd depth. T is *covariant* if, apart from
the structure of its finite sorts, its sort slots, element slots and sort equations bind covariant
entries only. Element equations are unrestricted.

**5.5 Theorem (covariant theories have categories of models)** [N 7.3; proved on paper with fixed
parameters in place of finite sorts, to redo]. Let T be covariant and h : M → M' a homomorphism.
(1) At a covariant entry A the relation is the graph of a function A(h) : A_M → A_{M'}, at a
contravariant one of a function A_{M'} → A_M: h_S at a sort, its inverse at a finite sort,
f ↦ c(h) ∘ f ∘ Φ(h) at `[Φ]c`. Covariant equations are preserved, contravariant ones reflected.
(2) So a homomorphism is a family of functions between the sorts with c_{M'}(Θ(h)θ) = h(c_M(θ)) for
every element slot `c : [Θ]B`.
(3) A(kh) = A(k)A(h). Hence homomorphisms compose, and Mod(T) is a category.
Every GAT is covariant, with Θ(h) = h componentwise. `c : [f : [x:X]X] X` is not.

**5.6 The theory T_K** [N 4.4]. With a ∧ b and ¬a defined by `if`:

    𝟚 : type,  tt ff : 𝟚,  if : [B : type, a b : B, x : 𝟚] B  with β and η        (a finite sort)
    X : type
    lim : [u : [p : [x:X]𝟚]𝟚,  u preserves ∧,  u preserves ¬] X
    lim([p] p(x)) = x
    lim([p] 𝔘([u] u(p))) = lim([p] 𝔘([u] p(lim u)))

It is covariant: p is contravariant, so u and its two premises are covariant.

**5.7 Theorem.** Mod(T_K) is the category of compact Hausdorff spaces and continuous maps.
*Proof.* A model is a set X with a map lim from its ultrafilters satisfying the laws of an algebra
for the ultrafilter monad, i.e. a compact Hausdorff space [Manes 1969, verified]. By 5.5, p(h) is
the preimage, u(h) the pushforward of ultrafilters, and a homomorphism is a function h with
h(lim u) = lim'(u(h)), i.e. a continuous map. ∎

**5.8 Corollary.** Mod(T_K) is not locally presentable: the ultrafilter monad has no rank [N 4.4].
So by 4.3 (d) no positive theory, hence no GAT and no SOGAT, has a category of models equivalent to
Mod(T_K).

**5.9 Remarks.** (i) Without the premises of lim: algebras of the double power set monad, a
category equivalent to Set^op [cite]. (ii) The separation concerns models in sets, where binders
range over all functions; compare second-order logic with full semantics. (iii) Isomorphism classes
of models cannot separate: natural numbers with a recursor have one model. (iv) Expected common
generalisation of 3.1 and 5.4: an entry of Φ may be admissible or contravariant [open].

---

## Proof obligations

1. 1.3: the presheaf model satisfies Def 3.1 strictly (Π and Id squares, universe).
2. 3.6: re-base PT 6.2–6.4 on the current ToS^ω (kinds, silent equations). The core of the chapter.
3. 3.5: the converse direction, for contextual models.
4. 4.2: the realisation of a lex functor. The only genuinely new theorem.
5. 5.5: redo the fourth-round proof with finite sorts; 5.3 lemma.
6. Citations to verify: Cartmell (GATs ≃ contextual categories, syntactic category), Kaposi–Xie,
   Uemura, Hofmann–Streicher, the double power set monad.

## Choices made here

- Models are contextual. GATs then get their usual models, and homomorphisms are determined by
  their action on points.
- Homomorphisms of positive theories are natural transformations of functors of points (3.4), not
  PT's pairs (F, φ). Initiality becomes one line; 3.5 says the two agree. Fallback: PT 5.2 as the
  definition and PT 7.3–7.4 as the proof.
- Not in the chapter: general (Henkin) models, morphisms of theories, non-contextual models,
  parameters.
