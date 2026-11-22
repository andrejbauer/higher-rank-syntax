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

## 0. Design of 2026-11-20 for Sections 4.3 onward (supersedes §§3–5 where they differ)

*Written after the user restated two desiderata: (1) a category of models for a class of theories
that contains the positive theories (GATs, SOGATs) and the compact Hausdorff theory, agreeing with
the straightforward homomorphisms on positive theories; (2) initiality "à la Voevodsky" for object
theories: what it means and whether it can be done. Status: paper arguments of the same day, in the
appendix "Proofs of 2026-11-20" at the end of this file (P1–P9). A first verification workflow died
on a usage limit with no result; a second, smaller one was started (results to be added below).*

**One tool.** For two models D, D' of ToS^ω and functors `i : ℬ → D`, `i' : ℬ → D'` from a category
of stages, the relational model `Rel(i, i')`: objects `(G, G', R)` with R a span of presheaves on ℬ
between the nerves `N G = D(i−, G)` and `N' G'`; types and terms are triples with witnesses; the
universe relates two sorts by the natural maps between their presheaves of elements ("functional
sorts"); Π relates two functions when related arguments go to related values; Id is equality of
witnesses. It is a model of ToS^ω with strict projections (P1). By `prop:classifying` a model of Ξ
in it relates the interpretations of every telescope and every term in the two models. Key lemma
(P2, relational binding): where the bound type has a generic related pair, witnesses at a product
are witnesses of the body at the extended stage.

**Use 1: homomorphisms, for every theory.** `(F, r) : (𝒞, M, R) → (𝒞', M', R')`: F preserves pt, r is
a model of Ξ in `Rel(よ, よF)` over `(M, M')`, and (ext) F preserves the chosen extensions and their
generic elements at related points. Equivalently: a model of T over the collage of F with
functional sorts (C3, not checked in detail). Unfolded: natural maps on the elements of every sort
slot at related points of its hypotheses, such that every element slot sends related points of its
hypotheses to related elements.

**The class.** Data sorts: finite sorts (constants and `case` with a uniqueness law); data types
`𝔻 ::= D | Π(𝔻, 𝔻)`. Forward and backward types over a telescope, the least families with
(F1) `A_y[σ]` for every sort slot y; (F2) `Id(l, r)` between elements; (F3) `Π(A_y[σ], C)`, y ∈ 𝒜,
C forward; (F4) `Π(P, C)`, P backward, C forward, where P must be a data type unless 𝒜 = ∅;
(B1) `A_D`, D a data sort; (B2) `Id(l, r)` between elements of a data sort; (B3) `Π(P, C)`,
P forward, C backward. Positive types: (F1)–(F3). T is *directed* if every entry of Ξ, other than
the slots presenting data sorts and the equations between elements, is `[Φ]C` with Φ a telescope of
forward and backward types and C = type, an instance `A_y[σ]`, or an equation between sorts, and
the hypotheses of admissible sorts are forward. T is *positive* if all those Φ consist of positive
types. Positive ⊂ directed; T_K is directed.

**Theorem A (P3, P4).** For a directed theory the CONTEXTUAL models and the homomorphisms form a
category Mod(T). At a forward type the relation is the graph of a function M → M', at a backward
type of a function M' → M; composition of homomorphisms is by the unique interpolation of related
points (forward entries pushed forward, backward ones pulled back). For positive theories all
models may be used. Contextuality cannot be dropped in general (P5: explicit counterexample over
the category with objects pt and K, Aut(K) = Z/2, for `c : [u : [p : [x:X]𝟚]𝟚] X`).

**Theorem B (C7; PT A.6–A.7 to re-base).** For a positive theory the homomorphisms are the pairs
`(F, φ)`.

**Theorem C.** Mod(T_K) = compact Hausdorff spaces and continuous maps (`p ↦ p∘h`, `u ↦ h_*u`,
`h(lim u) = lim'(h_*u)`). Not locally presentable, so not the models of any essentially algebraic
theory. Same class: filter monad (continuous lattices; citation to verify), double power set monad,
compact Hausdorff algebras, and with data binders countably infinitary algebra.

**Use 2: the term model of a positive theory (P6).** `𝒞_T` = admissible telescopes ⊂ `Syn//Ξ`. In
`Rel(i, よ)` between the syntax over Ξ and presheaves on `𝒞_T`, build by recursion along the slots of
Ξ the model `M_T` related to the generic model δ_Ξ with identity maps at sorts. Invariant, by the
same induction as for homomorphisms: on telescopes of positive types the relation is a bijection
`ev : Syn//Ξ(Γ, Θ) ≅ ⟦Θ⟧_{M_T}(Γ)`, natural in Γ and Θ. No term inversion. This replaces step R4.

**Theorem D (P7).** For positive T the term model `𝒮_T = (𝒞_T, M_T, R_T)` is initial in Mod(T) (and
among all models). Existence from `prop:classifying` and representability of `⟦Γ⟧_M`; uniqueness by
Yoneda at the tautological points.

**Voevodsky's form (P8, P9; to verify).** Raw syntax of T = the relative monad on finite sets of
expressions over the slots of Ξ and variables of arity ∅ (his RR), raw types `y(t)`, y ∈ 𝒜 (his LM),
judgements `Γ ⊢_T J :⟺ Ξ.Γ ⊢ J`, term model = the quotient syntax of this typing = regular
sub-quotient of C(RR, LM). It coincides with `𝒞_T` when admissible sort slots are injective, which
holds without equations between sorts (argument with a universe of codes, not written). Generation
(`Γ ⊢ x(t) : C` implies `Γ ⊢ t : Θ_x`) follows from Chapter 3's interpretation taken in Syn itself.
Optional adequacy: the judgements of T are the least typing closed under one rule per slot.

**The boundary (C13).** Beyond positive theories the term structure is not a model: T_K with a point
and a continuous endomap (or with N and a sequence) has initial model βℕ, uncountable;
`c : [f : [x:X]𝟚] X` is directed and has no initial model; T_K with a point and an arbitrary endomap
has none either (Lambek). So: all theories ⊋ directed (category of models) ⊋ positive (syntax =
initial model).

**Proposed sections.** 4.3 Relations between models (definition, P1, P2). 4.4 Homomorphisms and
directed theories (definition, Theorem A, Theorem B, examples). 4.5 The term model and initiality
(P6, Theorem D, Voevodsky's form). 4.6 Compact Hausdorff spaces and the limits of initiality
(Theorem C, the boundary).

**Decisions for the user.** (i) Mod(T) on contextual models (needed beyond positive theories).
(ii) Data sorts: finite sorts only, or inductively presented sorts (N). (iii) Whether to include
the adequacy statement (one rule per slot) and the injectivity lemma, i.e. how far to push the
Voevodsky packaging.

---

## 0b. Verification round 1 and the refined design (2026-11-20, evening)

*Round 1: four agents (R1 core, R2 computation, R3 literature, R4 Voevodsky), all returned.
Their full results are in the session transcript; the points that matter:*

- **Confirmed by a second reader (R1), carrying out the arguments:** P1 (the relational model is a
  strict model; nothing is required of the stage functors; `i(pt) = pt` only serves to read global
  elements), P2 (it is `lem:binding` applied in presheaves on the stages), P3 (F1)–(F3) for all
  models, C7 (homomorphisms of a positive theory = pairs (F, φ), φ a natural transformation on the
  full subcategory of positive telescopes; the passage back uses naturality along lifts,
  evaluation morphisms and `⟨σ, η(c)⟩`), P6 (term model, after the corrections below and with a
  five-line truncation lemma: `⟦_⟧_N ∘ π^* = ⟦_⟧_{N|Ξ}` for a prefix Ξ of Ξ'), P7 (initiality, also
  for non-contextual targets).
- **Corrections (R1).** E1: `𝒞_T` must be the contextualisation `Ctx(Syn//Ξ, ∐ よ(p_y))` (lists of
  pairs), not the full subcategory on admissible telescopes (counterexample: two admissible sorts
  with a sort equation). E2: "positive" must have no exemption for equations (counterexample:
  `Y, E, X : type; c, d : X; [g : [y:Y]E] c = d`: the term structure violates the equation and no
  initial model exists). E3: the conclusion forms (type; instance; equation between elements of
  an instance) belong to the definition; `prop:inversion` is not a generation lemma. The natural
  model of the term model is isomorphic to `𝒞_T` via ev, not equal.
- **Computation (R2).** P5 confirmed; a reduced, fully enumerated counterexample: X' the terminal
  presheaf on 𝒫, `X''(pt) = {x_0, x_1}`, `X''(K) = {z_0, z_3, z_4, z_5}`; 60 of 64 related pairs
  violate the composite; moreover NO homomorphism exists over the composite functor. Over sets:
  functionality, unique interpolation and composition hold on 27 directed shapes (lim with its
  premises, filters, mixed directions, dependent sort families, sort slots over mixed telescopes),
  exhaustively up to size 3 where feasible; all control shapes outside the class fail. Scripts
  were in the session scratchpad `wf2/R2-computation/`.
- **Voevodsky's form (R4).** Generation proved (Lemma G: if `Γ ⊢ x(t) : [Ψ]c'` then
  `Γ.Ψ ⊢ t : Θ` and `Γ.Ψ ⊢ c[t] ≡ c'`; by structural induction through Chapter 3's interpretation
  in Syn; no circularity; nothing for equality judgements). `n ↦ Expr(Ξ ⋈ n, tm)` is a J_f-relative
  monad, raw types `y(t)` a module, `Raw(RR_Ξ, LM_𝒜, ∅)` = Voevodsky's C(RR, LM); the slice
  `Γ ⊢_T J iff Ξ.Γ ⊢ J` is a typing; its quotient syntax Q_T is the image of `𝒞_T` in `Syn//Ξ`;
  `𝒞_T → Q_T` is an isomorphism iff the admissible sort slots are injective (fails with sort
  equations; holds without them by a term model with a universe of codes, outline only).
  WITHDRAWN: "the judgements of T are the least typing closed under one rule per slot" does not
  follow from generation plus initiality (leastness is completeness for equalities and needs a
  second term model on the per-slot calculus). Wording: "of the form of" the initiality
  conjecture, never "exactly". Verified quotation (arXiv 1602.00352, p. 2): "The term models for a
  class of type theories can be obtained by considering slices of the term model of the type
  theory called Logical Framework (LF), but unfortunately it is unclear how to extend this
  approach to type theories that have more substitutional (definitional) equalities than LF
  itself." Our slice construction is this route, with equational entries supplying the equalities.
- **Literature (R3).** Uemura's THESIS (ILLC DS-2021-09) starts from raw syntax of SOGATs (Ch. 4),
  proves the universal property of the syntactic category by a partial interpretation
  (Thm 4.8.18) and initiality in a (2,1)-category with weak morphisms (Thm 5.4.4); the arXiv paper
  only sketches Thm 5.17 and has bi-initiality (Thm 6.10). nLab "initiality conjecture" (2026):
  most are convinced by the thesis. Bezem–Coquand–Dybjer–Escardó (arXiv 2012.08370, Thm 1): strict
  initiality of a raw-syntax term model for finitely presented GATs, proof sketch, no binding.
  Kaposi–Xie: syntax = initial algebra of a translated GAT, "no meaningful notion of homomorphism
  of second-order models". No strict raw-syntax initiality for a general class WITH binding was
  found (absence of evidence). Manes Prop 5.5 (TAC reprint p. 86), Day 1975 Thms 3.3, 4.5 (all
  filters; morphisms preserve directed joins and arbitrary meets), AR Thms 1.64, 1.66, 3.36
  verified. KHaus not locally presentable: proved from AR 1.66 and a uniform ultrafilter. Scope
  for "no GAT": theories with a SET of operations of bounded arity (KHaus is varietal with a
  proper class of operations). Function-variable hypotheses such as `u : [p : [x:X]𝟚]𝟚` are not
  expressible in finitary or infinitary QII signatures. Unverified: Pospíšil in the original, RDP
  2015 quotation (do not print it).

### Refined design (supersedes §0 where they differ)

Supersedes CANDIDATE.md where they differ. Verified in round 1 (four agents): the relational model
is a strict model (P1), relational binding (P2), functionality on positive types, agreement with
the pairs (F, φ), the term model and initiality (P6, P7), generation (P8), the comparison with
Voevodsky's C(RR, LM) (P9), the counterexample over a non-terminal base (P5, by computation), and no
counterexample to functionality/composition over sets on 27 directed shapes. Corrections adopted:
- `𝒞_T := Ctx(Syn//Ξ, ∐_{y∈𝒜} よ(p_y))`, objects = lists of pairs `(y, σ)`; not a full subcategory.
- "positive" has NO exemptions: every entry of Ξ, equations included, has positive hypotheses.
- the conclusion forms are part of the definitions (below).
- the adequacy claim (one rule per slot generates the judgements) is withdrawn.
- positioning: Uemura's thesis proves initiality from raw syntax for SOGATs with weak morphisms.

#### A. Setting

Models are contextual throughout. A theory is `T = (Ξ, 𝒜)`; in this chapter Ξ has no equations
between sorts. An *instance* of a sort slot `S : [Φ_S] type` over a telescope Θ is a type
`S(t) := A_S[σ]`, `σ : Θ → Φ_S`. *Atomic types*: instances `S(t)` and equations `l =_{S(t)} r`
between elements of an instance. A sort slot S is *propositional* if Ξ contains the equation
`[Φ_S, a b : S] a = b`. An *axiom* is an entry of Ξ whose conclusion is an equation, or an instance
of a propositional sort. Every other entry is a sort slot or an *operation*.

#### B. Homomorphisms (unchanged)

`(F, r)`: F a functor of base categories preserving pt, r a model of Ξ in the relational model over
F lying over the two models, F preserving chosen extensions and generic elements at related
points. Unfolded: maps `h_S` on the elements of every sort slot S, at related points of its
hypotheses; every operation sends related points of its hypotheses to related elements. Axioms
impose no condition: for an equation because the relation at El is a graph; for a propositional
conclusion because two related elements of a subsingleton are equal.

#### C. The class

**Rigid sort.** A sort slot D of T is *rigid* if every homomorphism between models of T is bijective
on the elements of D (at all related points).
*Standard example.* `𝟚 : type; tt, ff : 𝟚` with the two axioms
    (D)  [B : type, a b : B, e : tt =_𝟚 ff]  a =_B b
    (E)  [B : type, g g' : [x : 𝟚] B, e₁ : g(tt) =_B g'(tt), e₂ : g(ff) =_B g'(ff), x : 𝟚]  g(x) =_B g'(x)
In every model in sets 𝟚 has exactly the two elements tt ≠ ff (apply (D), (E) with B a two-element
set; for (E), g the characteristic function of {tt, ff} and g' constant). So 𝟚 is rigid. No
eliminator is needed; Boolean operations are ordinary slots with truth tables, e.g.
`∧ : [a b : 𝟚] 𝟚` with four equations and `¬ : [a : 𝟚] 𝟚` with two.

**Positive types** (any 𝒜): `[x₁ : A₁, …, x_k : A_k] C` with the `A_i` instances of admissible sorts
and C atomic.

**Forward and backward types** (only when 𝒜 = ∅; then a contextual model is a model in sets): for
an entry `[Ψ]C` with C atomic,
    `[Ψ]C` is forward   if every entry of Ψ is backward;
    `[Ψ]C` is backward  if every entry of Ψ is forward and C is over a rigid sort.
(Ψ empty: every atomic type is forward; atomic types over rigid sorts are also backward.)
Action along a homomorphism h: forward `f ↦ C(h)∘f∘Ψ(h)` from M to M'; backward
`f' ↦ C(h)⁻¹∘f'∘Ψ(h)` from M' to M.

**Directed theory.** T is directed if the hypotheses of every entry of Ξ that is not an axiom are
(a) positive types, or (b) in case 𝒜 = ∅, forward or backward types.
**Positive theory.** The hypotheses of EVERY entry are positive types, and every conclusion is
`type` or atomic.

**Theorem A.** For a directed theory the (contextual) models and homomorphisms form a category.
**Theorem B.** For a positive theory the homomorphisms are the pairs (F, φ).
**Theorem D.** For a positive theory the term model on 𝒞_T is initial.

#### D. Examples to be verified (all with 𝒜 = ∅, models in sets, 𝟚 as above)

Abbreviations. `PX` := `[x : X] 𝟚` (a predicate; backward). An *ultrafilter* `u : βX` := the
telescope `u : [p : PX] 𝟚`, `[p q : PX] u({x} p(x) ∧ q(x)) =_𝟚 u(p) ∧ u(q)`,
`[p : PX] u({x} ¬p(x)) =_𝟚 ¬u(p)` (three forward entries). A *filter* : the same with the second
premise replaced by `u({x} tt) =_𝟚 tt`.

(1) T_K: `X : type`, `lim : [u : βX] X`, `[x : X] lim({p} p(x)) =_X x`,
    `[𝔘 : β(βX)] lim({p} 𝔘({u} u(p))) =_X lim({p} 𝔘({u} p(lim u)))`.
    Claim: Mod = compact Hausdorff spaces and continuous maps.
(2) T_DD: as (1) with `u : [p : PX] 𝟚` and no premises. Claim: Mod ≃ Set^op (algebras of the double
    power set monad = complete atomic Boolean algebras).
(3) T_Fil: as (1) with filters. Claim: Mod = continuous lattices with maps preserving directed joins
    and arbitrary meets (Day 1975).
(4) T_Top (Barr's relational algebras): `X : type`, `Conv : [u : βX, x : X] type`, propositional,
    `refl : [x : X] Conv({p} p(x), x)`,
    `trans : [𝔘 : β(βX), u : βX, x : X, v, y, m₁, m₂, c, w : Conv(u, x)] Conv({p} 𝔘({u} u(p)), x)`
    where the hypotheses `v, y, m₁, m₂, c` are Skolem witnesses of "𝔘 converges to u":
      `v : [𝒜 : [u : βX] 𝟚, B : PX, e₁ : 𝔘(𝒜) =_𝟚 tt, e₂ : u(B) =_𝟚 tt] βX`   (a βX-valued function,
          i.e. a function into 𝟚 with one more argument `p : PX`, plus the two premises),
      `y : [𝒜, B, e₁, e₂] X`,  `m₁ : [𝒜, B, e₁, e₂] 𝒜(v(𝒜, B)) =_𝟚 tt`,
      `m₂ : [𝒜, B, e₁, e₂] B(y(𝒜, B)) =_𝟚 tt`,  `c : [𝒜, B, e₁, e₂] Conv(v(𝒜, B), y(𝒜, B))`.
    Only `X` and `Conv` are not axioms; the hypotheses of `Conv` are forward. Claim: models = sets
    with a relation between ultrafilters and points that is reflexive and transitive in Barr's
    sense, i.e. topological spaces (Barr 1970); homomorphisms = maps preserving convergence =
    continuous maps. Without `trans`: pseudotopological spaces.
(5) T_Sup. A *subset* `A : Sub(X)` := the telescope
      `u : [p : PX] 𝟚`,  `w : [p : PX, e : u(p) =_𝟚 tt] X`,
      `[p, e] p(w(p, e)) =_𝟚 tt`,  `[p, e, q : PX, e' : q(w(p, e)) =_𝟚 tt] u(q) =_𝟚 tt`
    (four forward entries). In sets: u = "meets A" for A := the image of w, and every subset arises
    (choice). Along h: `A ↦ h(A)`, the direct image. Membership `a ∈ A` := the equational entry
    `[q : PX, e : q(a) =_𝟚 tt] u(q) =_𝟚 tt`.
    Signature: `X : type`, `∨ : [a b : X] X` with the semilattice laws, `sup : [A : Sub(X)] X`,
    `[A, a : X, m : a ∈ A] a ∨ sup(A) =_X sup(A)`,
    `[A, b : X, f : [a : X, m : a ∈ A] (a ∨ b =_X b)] sup(A) ∨ b =_X b`.
    Claim: Mod = complete lattices with maps preserving all joins. Variants: frames (add ∧, ⊤,
    distributivity), complete Boolean algebras (no free ones: Gaifman, Hales).
(6) T_DCPO: `X : type`, `Le : [a b : X] type` propositional with the axioms of a partial order;
    a *directed subset* := a subset with `u({x} tt) =_𝟚 tt` and
    `[p q : PX, [x y : X, l : Le(x, y), e : p(x) =_𝟚 tt] p(y) =_𝟚 tt, (the same for q)]
        u({x} p(x) ∧ q(x)) =_𝟚 u(p) ∧ u(q)`;
    `dsup : [A directed] X` with the two axioms of a least upper bound (conclusions in `Le`).
    Claim: Mod = dcpos and Scott-continuous maps.
(7) T_K with a group structure and continuity axioms: compact Hausdorff groups.

Claims about these categories: none is locally finitely presentable; KHaus, Set^op, Top, complete
lattices with join-preserving maps, frames, complete Boolean algebras, dcpos are not locally
presentable. So none is the category of models of a GAT.

#### E. Models with stages (to simplify the semantic sections)

For a model D of ToS^ω and a functor `i : ℬ → D`: the *points* of an object G at I are the morphisms
`iI → G`; the *elements* of a type A at a point g are the terms of `A[g]` over `iI`. In every
model: points of `G.A` are pairs; elements of `A[σ]` at g are elements of A at `σ∘g`; elements of
`Π(A, C)` at g are the terms of C over `iI.A[g]` (app), hence, if `iI.A[g] ≅ i(I')`, the elements of
C at the extended point; `Id(l, r)` has an element at g iff `l[g] = r[g]`. For presheaves with
`i = よ` these are the values of the presheaves (Yoneda). The explicit description of Π and of the
universe in presheaves is then never used: positive hypotheses bind admissible variables
(extension), and function variables occur only over the terminal base (sets and functions).


*Round 2 (two agents: X1 examples, X2 citations) was running when this was written; examples (4)–(6) above are hand-derived and unverified until it reports.*

---

## 0c. Round 2 results, the user's rejection of rigid sorts and stages, and Design 3 (2026-11-20, night)

*Round 2 (agents X1 examples, X2 citations), on the rigid-sort design of §0b.* All six example
theories typecheck and have the claimed models and homomorphisms, given Manes, Day and Barr (T_K,
double power set, filters, Barr's relational algebras for Top, the "subset with a witness
function" telescope, dcpos); brute force confirmed the subset telescope (1526 instances) and the
directedness premise (3671 instances). Findings that survive the redesign: (i) an entry whose
conclusion lies in a propositional sort imposes no condition on homomorphisms and passes through
composites and identities with arbitrary hypotheses (proved); (ii) the propositional SORT slot
itself needs well-behaved hypotheses: for `R : [f : [x:X]X] type` composition fails on 1, 2, 3
points (computed); (iii) the sort variable in the distinctness axiom of a two-element sort is
unavoidable (without sort variables the all-singletons structure is a model); (iv) Barr's
transitivity axiom has a Skolem-free form with an index sort variable,
`[I : type, W : βI, v : [i:I] βX, y : [i:I] X, c : [i] Conv(v i, y i), x, w : Conv(y_* W, x)] Conv(Σ_W v, x)`,
which is Barr's span definition (LNM 137, pp. 42, 44, 48–50, read). Citations verified by X2:
Barr 1970 Thm 3.1 and Prop 3.3; Seal 2005 Ex. 2.8 for the extension formula; Adámek–Rosický
Example 1.18(5): "The categories CPO, CSLat, and Top are not locally presentable"; Hales 1964;
Linton: "varietal categories are just categories tripleable over S" (complete Boolean algebras and
complete lattices with complete homomorphisms are NOT varietal: not cocomplete). No prior
presentation of compact Hausdorff or topological spaces by a finite signature with function
arguments was found (three searches; nearest: Arkor–McDermott Def 5.5).

*The user's reaction to §0b:* "The definition of rigid sorts and their inclusion in the definition
of directed theories seems contrived. The definition of models using stages is likewise ugly. Go
back to the drawing board and start from scratch". Then, mid-turn: "Compare proof of initiality
from Uemura's thesis with the one that we plan to carry out, and assess whether the're really
equivalent, or whether we're nonetheless doing something new", and "The guiding principle for your
thinking should be: We now have this LF, build from raw syntax and proven initial, that is higher
rank, which is a contrast to the work of Kaposi-Xie and Uemura --- from this, can we obtain any
interesting results about the semantics of object theories, that goes beyond their work?"

*Why the earlier designs needed fixed sorts, and how Design 3 avoids them.* With 𝟚-valued
predicates the relation at a predicate is strict (p = p'∘h), the power set is contravariant, and a
functional on predicates is covariant only if the truth values are fixed: every formulation
(parameters, declared rigid sorts, data sorts with eliminators, rigidity as a property) is the same
necessity. Design 3 uses the framework's own sorts as truth values: a predicate is a hypothesis of
conclusion `type`. Two sorts are related by a function, so predicates are related laxly
(`h(P) ⊆ P'`), everything is covariant (direct image), and no sort has to be fixed. The price:
predicates may be arguments of RELATIONS (propositional sorts, monotone), not of operations.

### Design 3 (supersedes §0 and §0b where they differ)

The author's verdicts on DESIGN2: "The definition of rigid sorts and their inclusion in the
definition of directed theories seems contrived. The definition of models using stages is likewise
ugly." Desiderata restated: (1) categories of models for a wide class of theories beyond SOGATs,
with interesting examples; (2) initiality à la Voevodsky for a class of theories; (3) a notion of
model as elegant as possible, with as little unfolding as possible in examples. Guiding principle
(their words): "We now have this LF, build from raw syntax and proven initial, that is higher rank,
which is a contrast to the work of Kaposi-Xie and Uemura --- from this, can we obtain any
interesting results about the semantics of object theories, that goes beyond their work?"

Everything below is a NEW proposal of the orchestrator, hand-derived, unverified. What is kept from
the verified rounds: the relational model Rel(i, i') is a strict model of ToS^ω (P1); relational
binding (P2); on positive theories the homomorphisms are the pairs (F, φ) (C7); the term model and
initiality (P6, P7) with `𝒞_T` the contextualisation; generation (P8); Voevodsky's form (P9).

#### 1. Models, without stages

A model of `T = (Ξ, 𝒜)` is a contextual natural model `(𝒞, ϖ)` together with a morphism of models
of ToS^ω `M : Syn//Ξ → 𝐏(𝒞)` (equivalently, by `prop:classifying`, a model of Ξ in presheaves on 𝒞)
such that `ϖ = ∐_{y ∈ 𝒜} M(p_y)`: the types and terms of 𝒞 are the admissible sorts and their
elements. The presheaf model is used only through:
 (R1) `M(Θ)` is a presheaf on 𝒞, the *points* of Θ; a point of `(Θ, x : E)` at I is a pair of a
      point θ of Θ and an element of E at θ;
 (R2) a sort slot S is a presheaf `M(S)` over the points of its hypotheses, and the elements of
      `S(t)` at θ are the elements of `M(S)` over `M(t)(θ)`;
 (R3) an equation `l = r` has an element at θ iff `M(l)(θ) = M(r)(θ)`;
 (R4) the elements of `[x : A]C` at θ, A an instance of an admissible sort, are the elements of C
      at `(θ·p, x)` in the extended context `I.A` (`prop:binding-model`);
 (R5) over the terminal category (𝒜 = ∅: models in sets) the elements of `[Ψ]C` at θ are the
      functions from the points of Ψ over θ to the elements of C, and an element of `type` is a set.
The Hofmann–Streicher universe and the explicit formula for presheaf products appear only in the
proof that 𝐏(𝒞) is a model.

#### 2. The class: operations are first-order, relations may take predicates

Setting: `T = (Ξ, 𝒜)`, no equations between sorts. *Instance* `S(t) := A_S[σ]` of a sort slot.
*Atomic type*: an instance or an equation between elements of an instance. A sort slot R is a
*relation* if Ξ contains `[Φ_R, a b : R] a = b`. An *axiom* is an entry whose conclusion is an
equation or an instance of a relation. Other entries are sort slots and *operations*.
*First-order type*: `[x₁ : A₁, …, x_k : A_k] C`, the `A_i` instances of admissible sorts, C atomic.
*Predicate*: a hypothesis `P : [Ψ] type`, Ψ a telescope of first-order types. *Member*: a
hypothesis `w : P(t)` for a predicate P bound earlier.

**Definition.** T is *relational* if
 (i) every operation and every sort slot that is not a relation has first-order hypotheses;
 (ii) the hypotheses of every relation are first-order types, predicates and members, and the
      relation is *monotone*: Ξ contains the axiom
      `[Φ, Φ̃, g : (for each predicate P of Φ a map [Ψ, p : P(ψ)] P̃(ψ), members sent to members), r : R(φ)] R(φ̃)`
      where Φ̃ differs from Φ only in its predicates and members;
 (iii) axioms are arbitrary entries.
T is *positive* if all hypotheses of all entries are first-order.

**Homomorphisms** are as before: a model of Ξ in the relational model over F, lying over the two
models, with F preserving chosen extensions. In the relational model two sorts are related by a
function. Hence two predicates P, P' are related (along h) by maps `P(ψ) → P'(h ψ)`: for
subsets, `h(P) ⊆ P'`. Unfolded for a relational theory: a homomorphism is a morphism `(F, φ)` of
the first-order part such that for every relation R: `R(P, x)` and `h(P) ⊆ P'` imply
`R'(P', h x)`; by monotonicity, iff `R(P, x)` implies `R'(h_! P, h x)`, `h_!` the direct image.

**Claim A (category).** For a relational theory, models and homomorphisms form a category.
Proof idea. Composition: a pair of points of the hypotheses of a relation, related along the
composite, has an interpolant: first-order entries are pushed forward along the first
homomorphism; a predicate is pulled back along the second (`P'(ψ') := P''(k ψ')`), members follow.
So `R(φ) ⟹ R'(φ') ⟹ R''(φ'')`. The maps between relations are unique because relations have at
most one element. Operations and other sorts are first-order (C7). Identities: the identity
relation at a predicate consists of all maps `P → P̃`, so the identity is a homomorphism iff every
relation is monotone. The same argument is claimed to work over arbitrary base categories (pull
back along (F', k) at all stages).
Known non-example (computed in round 2): a propositional sort `R : [f : [x:X]X] type`; there
composition fails. Function variables from a signature sort to a signature sort are excluded by
(ii).

**Examples (models in sets).**
 (a) Closure spaces: `X : type`, `Cl : [P : [y:X] type, x : X] type` (relation), monotone,
     `[P, x, p : P(x)] Cl(P, x)`, `[P, x, c : Cl({y} Cl(P, y), x)] Cl(P, x)`.
     Models: sets with a closure operator; homomorphisms: maps with `h(cl A) ⊆ cl h(A)`.
 (b) Topological spaces: (a) plus `cl ∅ = ∅` and `cl(A ∪ B) ⊆ cl A ∪ cl B`, written as equations
     with sort variables, e.g. "if x ∈ cl P then P is inhabited":
     `[P, x, c : Cl(P, x), B : type, a b : B, k : [y, p : P(y)] (a =_B b)] a =_B b`.
     A full subcategory of (a): Top with continuous maps.
 (c) Compact Hausdorff spaces: (b) plus two axioms. Continuous maps.
 (d) Complete lattices with join-preserving maps: `X`, `Le : [x y : X] type` (a partial order),
     `Below : [P : [y:X] type, x : X] type` ("x ≤ sup P") with: monotone; `P(x) ⟹ Below(P, x)`;
     down-closed; `Below(P, x)` and u an upper bound of P imply `x ≤ u`; a sup exists (an axiom
     with a sort variable expressing ∃).
 (e) Frames, complete Boolean algebras, dcpos, proximity spaces: the same pattern.
None of these categories is locally presentable (Top, complete lattices with join-preserving maps,
dcpos: Adámek–Rosický Example 1.18(5), verified in round 2).

#### 3. Initiality (verified core) and what follows from it

Positive theory: every hypothesis of every entry is first-order; conclusions `type` or atomic.
`𝒞_T := Ctx(Syn//Ξ, ∐_{y∈𝒜} よ(p_y))`. Term model `𝒮_T`; `ev : (Syn//Ξ)(Γ, Θ) ≅ M_T(Θ)(Γ)` for
telescopes Θ of first-order types; `𝒮_T` initial among models (strict homomorphisms).

**Claim D1 (free models).** For a telescope Θ of first-order types over Ξ, `T[Θ] := (Ξ.Θ, 𝒜)` is
positive; let F(Θ) be its term model, regarded as a model of T. Then
`Mod(T)(F(Θ), M) ≅ M(Θ)(pt)`, naturally in M.
**Claim D2 (definability).** For telescopes Θ', Θ of first-order types: every family of maps
`M(Θ')(pt) → M(Θ)(pt)` natural in `M ∈ Mod(T)` is induced by exactly one morphism `Θ' → Θ` of
`Syn//Ξ`. (Yoneda with D1 and ev.) Corollaries: completeness; Beth: if every model of T has
exactly one expansion to `T[Θ]`, the projection `Ξ.Θ → Ξ` is an isomorphism of signatures.
**Claim D3 (admissible and derivable rules).** For an entry `[Θ]C` with Θ first-order and C an
equation: it has a term over Ξ iff it holds in every model; `M_T([Θ]C)(pt)` is inhabited iff the
rule is admissible (holds for all substitution instances in all contexts of T).
**Claim D4 (beyond second order).** Let the admissible TYPES be the least class containing the
instances of admissible sorts and closed under `[x : A]B` for admissible A, B, and let contexts be
telescopes of admissible types (variables of any rank). With "first-order" replaced by "binds
variables of admissible types", the construction of the term model (P6) and initiality (P7) go
through unchanged: representability of an admissible type in the term model follows from the
invariant for that type. Examples of operators binding variables of rank ≥ 1: generalised
elimination rules discharging rules (Schroeder-Heister), binding of metavariables in contextual
modal type theory, quantification over predicate variables.

#### 4. Comparison with Uemura's thesis (to be checked against the text)

Both proofs have two steps: (1) a Streicher-style partial interpretation of the raw syntax of the
logical framework gives the universal property of the syntactic category over a signature (his
Thm 4.8.18, an equivalence of groupoids into categories with representable maps, using Hofmann's
splitting; ours: `thm:initiality` for the bare framework, then `prop:classifying` in two lines,
because a signature is a context, strict bijection into strict models); (2) a categorical argument
identifies the initial model of the object theory (his Thm 5.4.4, initial in a (2,1)-category,
morphisms preserving context extension up to isomorphism; ours: P6, P7, strict). Claimed
differences: strict versus weak statement; signatures as contexts (possible because the framework
has contexts of every rank); raw syntax as a relative monad with the term model as a subquotient;
scope of step (1) (every rank versus second order).


*Round 3 (agents Y1 comparison with Uemura's thesis, Y2 the relational class and the consequences of initiality, Y3 literature) was running when this was written.*

---

## 0d. Round 3 (2026-11-21): Uemura's thesis, literature, and Design 4 (relational theories)

*Supersedes §§0–0c where they differ. Agents: Y1 (comparison with Uemura's thesis, read from the
text), Y3 (literature) returned; Y2 (verification of Design 3) died on a usage limit, so Design 4
below is checked by my own proofs and two brute-force scripts only.*

### Uemura's thesis against our initiality proof (Y1, from the text; printed page numbers)

- **His statements.** Thm 4.8.18 (p. 128): "For any SOGAT T and any CwR C, the functor (−)^⋆ is an
  equivalence of groupoids Itpr(T, C) ≃ CwR(Cl(T), C)." Thm 5.4.4 (p. 152): "For any type theory T,
  the model I(T) is an initial object in the (2, 1)-category Mod(T)." Ex. 5.4.3: the base of I(Cl(T))
  is "the category of contexts and substitutions". Models (Def 3.2.4–3.2.5): CwR morphisms
  T → DFib_{M(base)}; morphisms preserve comprehension up to canonical isomorphism (Beck–Chevalley).
- **Strict versus weak is routine** (proved by Y1): for a contextual source and a target with chosen
  structure, the groupoid of weak morphisms is equivalent to the set of strict ones (induction on
  the length of contexts).
- **Not routine:** identifying the two syntaxes. His: three fixed levels (variables, metavariables,
  symbols), λ and application as object-level symbols with β, η axioms. Ours: canonical forms,
  λ-free, hereditary substitution. Deducing one theorem from the other needs an adequacy /
  canonical-forms theorem. ToS^ω is itself a finite SOGAT, so Thm 5.4.4 already gives a bi-initial
  model of it, in his presentation of the syntax.
- **Slices.** He has theories as objects with slices and the classifying property (Prop 5.3.2
  p. 149, Prop 5.4.5 p. 154, §5.4.2 p. 155; Ex 4.7.2: theories over DTT are Cartmell's GATs), but
  only symbols WITHOUT binding can be adjoined by slicing; operators with binding are constants of
  the pretheory (Defs 4.2.5, 4.3.5). Remark 4.1.1 (p. 51): "we are not allowed to write a
  higher-order operator like ((A → B) → C) ⇒ D in a SOGAT".
- **Proofs.** Step 2 (initiality of the term model) is the same Yoneda argument in both (his p. 153;
  our P7). Step 1 is genuinely different: he interprets the raw syntax of each SOGAT T separately,
  into the presheaf topos over a CwR, with Hofmann's splitting (p. 115), topos-internal partial
  maps and the impredicativity of the topos (Remark 4.1.3); Lemmas 4.8.10, 4.8.11 are proved as
  "Straightforward". We interpret the bare framework once, into strict models, without splitting,
  with uniqueness by minimality, and reach every signature by slicing. Our P6 (term model through
  Rel(i, よ)) is extra work he does not need, because his Yoneda embedding preserves pushforwards.
- **New in ours (Y1's list):** strict, raw-syntax, canonical-forms initiality (Voevodsky's form);
  one framework theorem plus slicing; signatures with binding operators as contexts; a notion of
  model of an LF signature AS AN OBJECT THEORY, which his thesis names as an obstacle (pp. 3–4):
  "One could define a model of a theory over a logical framework as a model of the logical
  framework equipped with additional structure to interpret the theory, but this does not coincide
  with the usual notion of a model of a type theory because the interpretation of the logical
  framework is not part of the usual notion of a model of a type theory" (our Def 4.14 fixes the
  framework model to presheaves over the base; `prop:binding-model` recovers the usual notion);
  sort equations (excluded from SOGATs, p. 106); all non-positive theories.
- **He has, we lack:** infinite signatures, Prop/prop judgement forms, the converse (every CwR is
  the syntactic CwR of a SOGAT, p. 135), compact generation of Mod(T) (Prop 5.2.1),
  Mod_dem(T) ≃ Th(T) (Thm 5.1.8), no adequacy obligation.
- **Not new for positive theories:** free models and definability (his S ⊣ L, Thm 5.1.8, §5.4.2,
  Lemma 5.4.7; for essentially algebraic theories Gabriel–Ulmer); higher-rank binders over
  admissible types are, semantically, first-order binding plus Π on representable sorts (his
  Remark 3.2.12, p. 45).
- **Verdict:** present initiality for positive theories as a new PROOF and PRESENTATION, by the route
  Voevodsky named (arXiv 1602.00352 p. 2, verified in round 1: "The term models for a class of type
  theories can be obtained by considering slices of the term model of the type theory called
  Logical Framework (LF), but unfortunately it is unclear how to extend this approach to type
  theories that have more substitutional (definitional) equalities than LF itself"); the
  equational entries of ToS^ω remove that obstacle.
- **Side finding about Chapter 3 (not yet told to the user before 2026-11-21):** `lem:tos-models`
  says a model of ToS^ω is "precisely" a model of `def:ttos`. But `def:model`(3) has one Id on the
  IMAGE At of ⟨U, El⟩, while `def:ttos` declares Id for U and for El(S) with S as a parameter; in a
  model of the GAT with El(S) = El(S') for S ≠ S', or U = El(S), the two Id types may differ. Fix:
  index Id in `def:model` by 1 ⊔ [U], or add compatibility axioms to `def:ttos`. Presheaf models and
  Syn are unaffected (El is injective there, U is not small).

### Literature (Y3; quotations read in the sources)

- Closure spaces in the sense extensive + monotone + idempotent, maps f(c A) ⊆ d(f A): Seal,
  "Canonical and op-canonical lax algebras", TAC 14 (2005) no. 10, §5.2 pp. 238–239; Prop 5.3:
  "The category Alg(P, 2) is isomorphic to Clos"; Prop 2.7: lax algebra categories are topological;
  p. 221: Alg(U, 2) ≅ Top (Barr; Clementino–Hofmann–Tholen); monotonicity "is a consequence of the
  reflexivity and transitivity". Also Janelidze–Sobral, Cahiers LXVI-1 (2025) §1 ("CLS").
  TERMINOLOGY CLASH: in Adámek–Herrlich–Strecker (Exercise 5N, p. 78) "Clos" is pretopological
  spaces; cite Seal and state the axioms.
- Rosický, abstract (7th Winter School 1979, p. 71): "A concrete category (A,U) is (absolutely)
  topological iff it is isomorphic to the category of models of a relational normal universal Horn
  theory T without equality of some type" (relation symbols of arbitrary cardinal arity; the JPAA
  1981 paper was not obtained).
- Closure spaces and Top are not locally presentable, not even accessible: proof by Y3 (no
  reference found for closure spaces): presentable objects are discrete, colimits of discrete
  spaces are discrete. Top also by Adámek–Rosický Example 1.18(5) (read in round 2). Sup-lattices
  and frames: monads without rank plus AR Thm 1.66 (round 2).
- Uemura's paper, §8 pp. 53–54: reconstruction of T from Mod_T is "Question 8.1" (open). Kaposi–Xie
  (intro): "SOGATs are not well-behaved algebraic theories, for example, there is no meaningful
  notion of homomorphism of second-order models" (about models with metatheoretic function spaces;
  they do have homomorphisms of first-order models after translating to a GAT). Neither framework
  has sort variables (Uemura arXiv §5 p. 22, Fig. 1; thesis Defs 4.2.2–4.2.10; Kaposi–Xie Defs
  13–15).
- Higher order elsewhere: Arkor–McDermott, "Higher-order algebraic theories" (preprint 2020;
  simply typed, every order, λ-free, initial term algebra, Thms 3.6, 4.4, Prop 5.16);
  Gratzer–Sterling arXiv 2012.10783 (LCCCs, "hypothetical judgments of arbitrary level", from
  sketches). Schroeder-Heister JSL 1984 is sentential; rules discharging rules start at level 4.
  No raw-syntax initiality for a dependently sorted framework of order above two was found
  (absence of evidence).

### Design 4: relational theories (mine, 2026-11-21)

Definitions, for T = (Ξ, 𝒜):
- *first-order type*: `[x₁ : A₁, …, x_k : A_k] C`, the A_i instances of admissible sorts, C an
  instance of a sort slot or an equation between its elements;
- *predicate*: a hypothesis `P : [Ψ] type` with Ψ a telescope of first-order types;
- *relation*: a sort slot R such that `[Φ_R, a b : R] a = b` is derivable;
- *axiom*: an entry whose conclusion is an equation or an instance of a relation;
- *monotone* relation: for each predicate argument, `[…, P, P̃, g : [ψ, p : P(ψ)] P̃(ψ), …, r : R(…P…)] R(…P̃…)` is derivable;
- T is *relational* if every hypothesis of every sort slot and every operation is a first-order
  type, except that relations may also take predicates, and then are monotone; axioms are
  arbitrary. Positive theories are the relational theories whose relations take no predicates.

**Theorem A (my proof, over ANY base category, all models, no contextuality needed).** Models and
homomorphisms of a relational theory form a category. A homomorphism is a pair (F, φ) on the
first-order part (C7) such that R(φ) implies R'(φ') for related points; at a predicate, P ~ P' iff
there is a natural map P → P'∘F; unfolded, R(…P…, x) ⟹ R'(…F_!P…, Fx), F_! the direct image (left
Kan extension). Proof: first-order entries as in C7; at a relation, interpolate a point related
along F'F by pulling the predicate back along the second functor, P' := P''∘F' (componentwise, at
all stages, so no image problem as in P5), and push first-order entries forward; the components at
relations are unique because relations are subsingletons; the identity is a homomorphism exactly
because relations are monotone; axioms impose no condition (round 2, X1).
**Examples.**
- Closure spaces: `X : type; Cl : [P : [y:X] type, x : X] type` (a relation),
  `refl : [P, x, p : P(x)] Cl(P, x)`, `trans : [P Q, x, c : Cl(P, x), d : [y, p : P(y)] Cl(Q, y)] Cl(Q, x)`.
  Monotonicity is derivable: `trans(P, Q, x, c, {y, p} refl(Q, y, g(y, p)))`. Models in sets: closure
  spaces in Seal's sense (Cl depends only on the support of P); homomorphisms: continuous maps.
- Topological spaces: closure spaces with cl ∅ = ∅ and cl(A ∪ B) ⊆ cl A ∪ cl B; full subcategory.
  The two axioms need "P is inhabited" and "or", written with a sort variable
  (`[…, B : type, a b : B, e : …] a =_B b`), valid in set models.
- Sup-lattices: closure spaces with T₀ (`[x y, e₁ : [P, c : Cl(P,x)] Cl(P,y), e₂ : …] x = y`) and
  principal closures (every cl A = cl{s}, one "exists"); full subcategory (Cl(P, x) ⟺ x ≤ ⋁P;
  continuous ⟺ join-preserving; checked by hand). Frames: add `∧`, `⊤` and the Horn axiom
  `[a, P, Q, k : [y, p : P y] Q(a ∧ y), x, c : Cl(P, x)] Cl(Q, a ∧ x)`.
- Sites: `Cov : [P : type] type` (a relation), `refl : [P : type, p : P] Cov(P)`,
  `trans : [P Q : type, c : Cov(P), d : [p : P] Cov(Q)] Cov(Q)`. No admissible sorts, so a model of
  Def 4.14 is a small category 𝒞 with terminal object and a model of Ξ in 𝐏(𝒞): Cov depends only on
  the support sieve of P, refl = maximal sieve covers, stability = naturality, trans = local
  character. Models ≅ Grothendieck topologies on 𝒞; homomorphisms = terminal-object-preserving
  cover-preserving functors. NEEDS NON-CONTEXTUAL MODELS (contextual ⇒ 𝒞 = 1).
- Compact Hausdorff spaces: Top plus two axioms quantifying over ultrafilters (with encodings);
  possible, not pretty. `lim` as an OPERATION is no longer in the class.
**Computations** (scripts in the session scratchpad `round3/scripts/`): `clos.py`: models of
refl+trans on ≤ 2 points (fibres of predicates 0..2) are exactly the 1, 2, 7 closure operators, all
support-determined and monotone; relational homomorphisms = continuous maps on all 3790 triples
(spaces up to 3 points, 61 closure operators on 3 points); 2255 composites, 0 failures; for an
extensive idempotent non-monotone operator the identity is not a homomorphism. `sites.py`: on the
terminal category and on the arrow category 0 → 1, models of the covering theory are exactly the
2 resp. 4 Grothendieck topologies, Cov is support-determined, and relational homomorphisms over the
four terminal-preserving functors are exactly the cover-preserving ones (48 cases).
**Why this class beyond SOGATs:** predicates are sort variables and bind over non-admissible sorts,
which SOGATs cannot write; Clos, Top, Sup, Frm are not locally presentable, so no GAT or SOGAT has
them as models. Precedents to cite: the Set-level presentations are Seal's lax algebras, Barr's
relational algebras, Rosický's relational Horn theories. What is new: one framework, homomorphisms
from the framework's relational model rather than by hand, the same definition giving (F, φ) on
positive theories, operations and dependent sorts alongside relations, arbitrary bases (sites).

### Results beyond Uemura and Kaposi–Xie (candidates, 2026-11-21)

1. Homomorphisms for every theory and Theorem A with the examples above.
2. Uniform adequacy (Y1's proposal P-a): for every finite SOGAT T with transcription Ξ_T, ToS^ω over
   Ξ_T derives exactly T's first-order judgements; in particular higher-rank reasoning in the
   framework is conservative over every SOGAT. Uemura, thesis p. 4: "it is hard to even state the
   general adequacy theorem asserting that any theory over the logical framework is adequate: for
   this statement to make sense, we need a general notion of a type theory outside the logical
   framework". Route: (⇒) his rules are admissible in ToS^ω (App, App-Eq, Hyp, Conv); (⇐) his
   syntactic model gives a model N of Ξ_T in presheaves on his contexts, `prop:classifying`
   interprets Syn//Ξ_T in it soundly, the interpretation of a first-order term is the class of its
   translation, and "interpretable ⟹ translation derivable" by structural induction as in the
   generation lemma. Unwritten: the model N slot by slot, and the admissibility check.
3. Interpretations for free: Syn(Ξ', Ξ) ≅ mod_{Syn//Ξ'}(Ξ) ≅ Mod(ToS^ω)(Syn//Ξ, Syn//Ξ'), so
   Ξ ↦ Syn//Ξ is fully faithful (Uemura, thesis p. 135, leaves morphisms of SOGATs and full
   faithfulness as future work). Modest: immediate from `prop:classifying` and
   `lem:signature-morphisms`.
4. Initiality for positive theories (new proof and presentation; adds sort equations).

### Proposed chapter (2026-11-21)

4.1 Signatures (as now). 4.2 Theories and models: Def 4.14 kept with all models (contextuality is
not needed by any result of Design 4, and sites need non-contextual models); `lem:presheaf-model`
reduced to an interface (types are presheaves on elements, terms are sections, sorts are the small
types, binding over a representable type is context extension), with the Hofmann–Streicher
universe and the product formula inside the proofs. 4.3 Relations between models (Rel(i, i'),
relational binding, homomorphisms for every theory). 4.4 Positive theories: (F, φ), the term model
via Rel(i, よ), initiality, Voevodsky's form, comparison with Uemura, optionally uniform adequacy.
4.5 Relational theories: Theorem A, examples, non-local-presentability, the boundary of initiality.

---

## 0e. Last search (2026-11-21): the user's verdict and my independent analysis

*The user, after Design 4: "This is not good enough. It's starting to look like the higher rank of
our framework doesn't really contribute much ... have one last go at trying to find something
genuinely new and interesting to claim and prove about our higher-rank framework. This would
ideally mean good semantics + possibly initiality for a wide class of theories, that genuinely
harness the fact that our framework is higher-rank ... I would like to construct a genuinely new
theory, not just this half-assed fiddling." A workflow (agents G1 unanchored generator, G2
evaluator of candidates C1–C9, G3 literature, J1 judge) was started; brief and candidates in the
session scratchpad `design/BRIEF2.md`, `design/CANDIDATES2.md`. Below: my own analysis, written
before the agents reported, unverified.*

**A structural reason why the hope fails in the form stated (my claim, proof sketch).** ToS^ω's own
theory of models is a positive theory T_ToS (ty; tm admissible; U, El, pi, lam, app with β, η; Id
at the two atoms with reflection and uniqueness). A model of a signature Ξ in a model of ToS^ω
("general" or Henkin semantics) is the same as a model of the positive theory T_ToS extended by the
deep transcription Ξ^♭ of Ξ (each slot [Θ]C becomes a constant of tm(code of Π_Θ C)). So with
general semantics every signature, of any rank, is a SOGAT-like positive theory: initiality holds
(prop:classifying), but nothing beyond "second order + Π + a universe" (Uemura, thesis Rem. 3.2.12).
With standard semantics (U all small presheaves, Π full) categories of models beyond lfp occur
(KHaus, Top, ...), but the term model is not a model beyond positive theories (O1). Positive
theories are where the two semantics agree on the term model. So "initiality + semantics beyond
SOGATs" is not available in either semantics; this dichotomy is itself a statement worth proving.

**Candidate results that are new and specific to this framework (my ranking before the agents).**
1. *Normalization by initiality (C2).* Syn (canonical forms, no λ, hereditary substitution) and the
   term model of T_ToS (explicit lam/app modulo β, η) are both initial in the same category, hence
   isomorphic: every explicit term is βη-equal, modulo the equational hypotheses, to a canonical
   form, and canonical forms are equal iff their explicit images are. Hereditary substitution is the
   unique homomorphism ("evaluation"); quotation is the other one. Slicing gives, for every
   signature Ξ of any rank, Syn//Ξ ≅ the term model of T_ToS[Ξ^♭]: higher-rank syntax = normal
   forms of second-order syntax with Π, as an isomorphism of initial models. Needs: Mod(T_ToS) =
   Mod(ToS^ω), which requires fixing the Id imprecision of lem:tos-models (index Id by codes).
2. *Uniform adequacy / conservativity (C1).* For every finite SOGAT T, ToS^ω over Ξ_T derives exactly
   T's first-order judgements; Voevodsky's slice route becomes a theorem for theories with
   definitional equalities. Proof: admissibility of the SOGAT rules, and soundness of ToS^ω in
   presheaves on T's syntactic contexts with "interpretation = translation".
3. *Strict initiality for positive theories* (new proof, Voevodsky's form).
4. *Standard semantics beyond lfp* with the boundary results (βℕ, no initial model).
The universe-internal structure 𝐏_ϖ(𝒞) (C6) is a model of ToS^ω and gives shallow presentations of
type theories (object types = framework sorts) with models = natural models with operations; it is
semantically the same as the deep (SOGAT) presentation, but much lighter to unfold.

---

## 0f. Verdict of the last search (2026-11-21; agents G1, G2, G3, judge J1; reports in the session scratchpad `round4/`)

**The strong hope is not achievable, and this is provable.** (1) Henkin collapse (C2, sketched,
needs the Id fix): for every signature Ξ of every rank, Syn//Ξ ≅ the term model of the finite SOGAT
T_ToS[Ξ♭]. (2) Standard semantics beyond positivity: definability fails at the first non-positive
type (G1-F3, proved: `[f:[x:X]X]X` has a natural family no term defines); incompleteness at rank 2
(G1-F4, proved modulo textbook facts: ℕ with a dependent eliminator into sort variables is
categorical in every 𝐏(𝒞), so its equations are Π⁰₁-complete; a variant without sort variables, with
a binder over the non-admissible ℕ, also works); homomorphisms need not compose (O2). Literature
agrees: Capriotti, PhD thesis 2016 (arXiv 1702.04912) §2.6 and §2.9; Bocquet, PhD thesis (ELTE,
2026) "Relative induction principles for second-order generalized algebraic theories", l.486:
"higher-order theories do not really have categories of algebras"; Kaposi–Xie.

**Credit owed (important).** Capriotti's thesis (Capriotti2016, already in references.bib, cited in
no chapter) has: a rule framework RF with Π over all types and a universe; a type former = a context
of the initial RF-category (Def 2.3.1); a Φ-structure = a global element of ⟦Φ⟧ in presheaves with
the "fibrant universe" of the CwF's types and terms (Def 2.3.2) — our 𝐏_ϖ(𝒞); morphisms by logical
relations in a span model R_F along an oplax morphism (Def 2.5.1–2.5.5, Lemma 2.7.1) — our
relational homomorphisms; the counterexample (U→U)→U on 1 ⊂ 2 ⊂ 3 (§2.6) — our O2; "flat" (morphisms
compose, Def 2.7.2) and "algebraic" (initial object, Def 2.7.5); and leaves open (§2.9): "if a type
former is written only using 'first-order' Π-types of non-small types, then it is automatically flat
... there should exist a notion of 'strict positivity' for type formers, and those type formers that
turn out to be strictly positive ought to be algebraic." Bocquet 2026: relative induction for SOGATs
(so displayed models / induction for positive theories is NOT new); Thm 6.6.2: 2LTT with any inner
SOGAT and outer MLTT (with W-types) is bijective on terms. Gratzer–Sterling arXiv 2012.10783 §5:
categorical conservativity of arbitrary-level LCCCs over a Uemura theory. Kovács ICFP 2022: strong
conservativity (staging) for one fixed object theory; l.1542 suggests the single-gluing proof.

**Ranking after adversarial checks (J1).**
1. Uniform adequacy (C1+, sketched, credible): for every finite Cartmell GAT (sort equations
   included) and every finite SOGAT without Prop/prop, ToS^ω over the transcription derives exactly
   the theory's judgements. The (⇐) direction needs a CODE-UNIVERSE model 𝐏_V(𝒞^T) (U := the
   theory's types modulo equality, El := its terms), not Hofmann–Streicher (two termless sorts would
   be identified, and type conversion could not be reflected); the same model discharges P9.
   Novelty moderate; answers Uemura's "hard to even state". 12–20 pages, 3–5 weeks. Scope caveat:
   equality assumptions in Uemura's environments (Def 4.3.4) unchecked.
2. Uniform staging (G1-F2, hard steps re-checked): outer sort-polymorphic inductive families (W,
   rank 3) over any positive inner theory are strongly conservative: every inner term over an inner
   context is judgementally the quotation of its stage, by ONE application of Ch. 3 initiality into
   the relational model with a RELATION-valued universe (checked to be a ToS^ω-model). Novelty
   reduced by Bocquet Thm 6.6.2 and Kovács; remaining: sort equations, the framework as the outer
   layer, the proof as an instance of all-rank initiality. 15–20 pages, 4–6 weeks.
3. Answer to Capriotti §2.9: fibrant-positive type formers (signatures read in 𝐏_ϖ(𝒞), binders only
   over El-variables) are flat and algebraic, with strict raw-syntax initial models. Content SOGAT-
   level; comparison with his OPLAX morphisms owed. 6–10 pages.
4. C2 (Henkin collapse as a theorem), 3–5 pages after the Id fix. Gives canonical representatives
   modulo βη and reflected hypotheses, NOT a normalization algorithm.
5. Boundary theorems F3, F4, O1, O2 (low novelty, sharp).
Demoted: displayed models / relative induction / parametricity translation (Bocquet, BKS); C4, C6
(tools/remarks); C7 refuted (`B, W : type, c : [f:[x:B]B] W`); C8 no route; F7 (Jung–Tiuryn-style
parametric definability at every rank) the only open route to new higher-rank semantics: high risk.

**Proposed narrative (J1):** "An initial higher-rank logical framework and the exact reach of its
algebraic semantics". Ch. 3 initiality (main theorem; no precedent found for strict raw-syntax
canonical-form initiality of a dependently sorted framework of unbounded rank with sort variables and
definitional equalities; as an abstract statement it is covered weakly by Uemura's Thm 5.4.4 for his
presentation). Ch. 4: classifying slices; relational homomorphisms credited to Capriotti; positive
theories with strict initiality by slices (Voevodsky's form), answering Capriotti §2.9; adequacy;
Henkin collapse. Ch. 5: the framework as metalanguage (fundamental theorem, weak conservativity,
staging). Ch. 6: boundary theorems. About 4–5 months of work. Housekeeping: index Id in def:model(3)
by 1 ⊔ [U] (needed by lem:tos-models, lem:mod-limits, C2); typo "Note that Only" in
well-formed-syntax.tex (line 1006).

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

*Third version, WRITTEN into `chapters/theories.tex` on 2026-11-18 after the user approved the
plan ("Ok, this looks good", then "make the change, go"), with their two amendments: natural
models throughout, no C-systems; the simply typed λ-calculus as a fourth running example. Numbers
of the scratch build: 4.11 theory `def:theory`; 4.12 four running theories `ex:theories`
(T_mon, T_λ, T_Π, T_→); 4.13 model `def:theory-model`; 4.14 points `def:points`; 4.15 points as
tuples `lem:points`; 4.16 points and substitution `lem:points-extension`; 4.17 extension
`def:extension`; 4.18 the natural model of a model `lem:model-natural`; 4.19 binding
`lem:binding`; paragraph on binding in a model; paragraph "a model unfolds slot by slot";
4.20 models unfolded `ex:models`; 4.21 literature `rem:model-literature`. The decisions D1–D3
below were accepted as proposed. History: the first version (types of a model as classes [A, θ]
over an intrinsic subpresheaf 𝒫) needed a quotient and too much preparation; the second (models
as a property: ⟦p_A⟧_M representable, contextual objects, democratic) could not carry a strict
theorem. The positive-types material is not in the chapter (the user deleted it); its statements
are recorded in §3 below. A sentence "the admissible sorts are the sorts of variables …" after
the definition of a theory was left out, because the user had deleted its predecessor.*

*`prop:binding-model` as ONE claim, WRITTEN 2026-11-19 (supersedes the two-item form of the next note; the user asked "can we drop point 1 from the statement? also, why is everything relative to the substitution sigma?", then "ok. make the change"). Statement: model (𝒞, M, R) of T = (Ξ, 𝒜), y ∈ 𝒜 with Φ_y and A_y of Def 4.12, σ : Θ → Φ_y in Syn//Ξ, C a type over Θ.A_y[σ]; for θ ∈ ⟦Θ⟧_M(I), τ := (y, ⟦σ⟧_M(θ)) ∈ Ty_M(I), extension p_τ, generic term ν_τ = (y, ⟦σ⟧_M(θ)·p_τ, v_τ). Then (θ·p_τ, v_τ) is a point of Θ.A_y[σ] at I.τ and evaluation b ↦ b(p_τ, v_τ) is a bijection ⟦Π(A_y[σ], C)⟧_M(I, θ) ≅ ⟦C⟧_M(I.τ, (θ·p_τ, v_τ)), natural in (I, θ): square with right vertical _·f^{+τ} and lower right corner ⟦C⟧_M(J.τ[f], (θ·f·p_{τ[f]}, v_{τ[f]})), where τ[f] = (y, ⟦σ⟧_M(θ·f)). The representation fact ((p_τ, v_τ) represents ⟦A_y[σ]⟧_M[θ], by the pasting diagram) is now the first half of the proof; Lemma 4.19(2) then gives the bijection and the square. GONE from the text: the right adjoint R_σ, its action on morphisms, and the isomorphism of presheaves ⟦Π(A_y[σ], C)⟧_M ≅ ⟦C⟧_M ∘ R_σ. For Section 4.3: the representation fact will probably be needed for contexts (generic points: g_{Γ.(y,σ)} := (g_Γ·p_τ, v_τ)); state it there as a lemma, citing the proof here. Why σ (explained to the user): a binding hypothesis is y applied to arguments, σ : Θ → Φ_y is the list of arguments; σ = id does not suffice (in `lam`, b : [x : tm(A)] tm(B(x)) lives over Θ = (A, B) and σ forgets B); the pair (y, σ) is data and cannot be recovered from the type A_y[σ], since injectivity of sort slots is not proved.*

*`prop:binding-model` reworked 2026-11-19 (the user: "you haven't said what y is, and the wording of the first point seems a bit clumsy. try to rewrite the prop as ellegantly as possible"). Setup: model (𝒞, M, R) of a theory T = (Ξ, 𝒜); y ∈ 𝒜 an admissible sort, with hypotheses Φ_y and generic type A_y (Def 4.12); σ : Θ → Φ_y in Syn//Ξ, so that A_y[σ] is a type over Θ; for θ ∈ ⟦Θ⟧_M(I), τ := (y, ⟦σ⟧_M(θ)) ∈ Ty_M(I) with extension p_τ and generic term ν_τ = (y, ⟦σ⟧_M(θ)·p_τ, v_τ). (1) The pair (p_τ, v_τ) represents the presheaf ⟦A_y[σ]⟧_M[θ] on 𝒞/I; hence a right adjoint R_σ of ∫⟦p_{A_y[σ]}⟧_M, with counit p_τ, is given by R_σ(I, θ) := (I.τ, (θ·p_τ, v_τ)), R_σ(f) := f^{+τ}, where τ[f] = (y, ⟦σ⟧_M(θ·f)). (2) For C over Θ.A_y[σ], evaluation b ↦ b(p_τ, v_τ) is a bijection ⟦Π(A_y[σ], C)⟧_M(I, θ) ≅ ⟦C⟧_M(R_σ(I, θ)), natural in (I, θ) (square kept), so ⟦Π(A_y[σ], C)⟧_M ≅ ⟦C⟧_M ∘ R_σ. Changes against the previous form: the slogan and the "in particular … we write" clause of (1) are gone; the right adjoint moved from the end of (2) to (1), with its action on morphisms; C is introduced only in (2); the lead-in names the admissible sort y. The proof has a new paragraph identifying R_σ(f) with the lift. Also on 2026-11-19 the user deleted Remark `rem:model-literature` from the end of Section 4.2; do not re-add it. The section now ends with Example 4.21.*

*Leaner version of Lemma 4.16 to Proposition 4.21, WRITTEN 2026-11-19 at the user's request ("could we shorten the developement from lemma 4.16 to prop 4.21, make it more elegant?", then "make the changes"). Lemma 4.16 `lem:points-extension` has two items: (1) for Θ = (A_1, …, A_k), with iterated pairs written as tuples, ⟦Θ⟧_M(I) = {(x_1, …, x_k) | x_j ∈ ⟦A_j⟧_M(I, (x_1, …, x_{j-1}))}, and ⟦p_{A_k}⟧_M forgets x_k; (2) ⟦A[σ]⟧_M(I, θ') = ⟦A⟧_M(I, ⟦σ⟧_M(θ')). Its proof displays ⟦Θ.A⟧_M = ⟦Θ⟧_M.⟦A⟧_M, ⟦p_A⟧_M = p_{⟦A⟧_M}, ⟦A[σ]⟧_M = ⟦A⟧_M[⟦σ⟧_M] and cites Lemma 4.10(1). Gone: the commuting square of sets of types, the equation of presheaves ⟦A[σ]⟧_M = ⟦A⟧_M ∘ ∫⟦σ⟧_M, the dependent-sum display, and `cor:points-telescope` (merged into item (1)). Lemma 4.17 `lem:representable-types` is one claim, the old item (1); the old item (2), p_A representable iff every A[γ] is, was never cited and is gone. Proposition 4.20 `prop:binding-model`: statement unchanged; (1) is proved by pasting pullbacks in one diagram, よ(I.τ) → ⟦Θ.A_y[σ]⟧_M → ⟦Φ_y.A_y⟧_M over よ(I) → ⟦Θ⟧_M → ⟦Φ_y⟧_M: the right square is the lift square of ⟦σ⟧_M and ⟦A_y⟧_M (a pullback by Lemma 3.16(3), as ⟦_⟧_M preserves lifts), the outer rectangle is the square that R gives at τ restricted to the summand ⟦p_y⟧_M, so the left square is a pullback and Lemma 4.17 applies. `prop:slots` and `lem:binding` are unchanged. Numbering now: 4.15 points, 4.16 pointwise interpretation, 4.17 representable types, 4.18 slots, 4.19 binding, 4.20 binding is context extension, 4.21 examples, 4.22 literature. Not used, worth remembering for Section 4.3: R_σ is also the right adjoint that Lemma 2.3 (`lem:pullback`) gives for the pullback of ϖ_M along θ ↦ (y, ⟦σ⟧_M(θ)), and the term model of R2 uses the same lemma.*

*(Superseded the same day: the user said it "doesn't merit a lemma"; the lemma, its proof, the induction sentence and the presheaf paragraph are now one short paragraph after `prop:slots`.) Lemma 4.20 `lem:components` added 2026-11-19 (the user found the sentence identifying the component with ⟦η(z)⟧_N obscure): for N ↔ (M, c) in `prop:slots` and E declaring z : [Φ_z]C_z ∈ Ξ.E, ⟦Φ_z⟧_N = ⟦Φ⟧_M, ⟦C_z⟧_N = ⟦C⟧_M and c = ⟦η(z)⟧_N; proof via N = ⟦δ_{Ξ.E}⟧_N, preservation of pairing and of app. `prop:slots` now uses Ξ, M (no primes) and lam_{⟦Φ⟧_𝒟[M]}; a drawn triangle was tried and rolled back at the user's order.*

*(Same day, later: the user could not read the purely categorical lemma, so `lem:binding` now has a two-sentence lead-in and three items: (1) b(f, a) = b(p, v)·⟨f, a⟩; (2) evaluation at (p, v) is a bijection Π(A, C)(I, γ) ≅ C(I', (γ·p, v)); (3) naturality, hence Π(A, C) ≅ C ∘ R for a right adjoint R of ∫p_A. The adjointness sentence after it is gone. `prop:binding-model` was then rewritten in the same three-item form: (1) (p_τ, v_τ) represents ⟦A_y[σ]⟧_M[θ]; (2) evaluation is a bijection ⟦Π(A_y[σ], C)⟧_M(I, θ) ≅ ⟦C⟧_M(I.τ, (θ·p_τ, v_τ)); (3) naturality via the lift f^{+τ}, hence R_σ and the isomorphism of presheaves; with a two-sentence lead-in.) `lem:binding` and `prop:binding-model` restated 2026-11-19 as isomorphisms of presheaves: for A over Γ with p_A representable and R a right adjoint of ∫p_A, Π(A, C) ≅ C ∘ R (evaluation at the representations; elementary proof kept, plus one sentence on adjointness: weakening = precomposition with ∫p_A, Π its right adjoint, ∫p_A ⊣ R); for a model, R_σ(I, θ) := (I.τ, (θ·p_τ, v_τ)), τ = (y, ⟦σ⟧_M(θ)), is a right adjoint of ∫⟦p_{A_y[σ]}⟧_M and ⟦Π(A_y[σ], C)⟧_M ≅ ⟦C⟧_M ∘ R_σ.*

*`prop:slots` restated 2026-11-19 at the user's request ("more precise, more categorical"): for a signature Ξ'.E with E = [Φ]C, pairing (M', c) ↦ ⟨M', lam_{Ψ_{M'}}(c)⟩, Ψ_{M'} := ⟦Φ⟧_𝒟[M'], is a bijection ∑_{M' ∈ mod_𝒟(Ξ')} Tm_𝒟(⟦Φ⟧_{M'}, ⟦C⟧_{M'}) ≅ mod_𝒟(Ξ'.E) over mod_𝒟(Ξ'). The paragraph after it defines the component at a slot z as c = ⟦η(z)⟧_M and treats an equation as the condition ⟦l⟧_{M'} = ⟦r⟧_{M'} (Def 3.1(3)).*

*Term model, for Section 4.3 (2026-11-19). The remark `rem:syntax-display-maps` was deleted from Section 4.2 at the user's request, once it was clear that it is the first half of the definition of the term model (R2) and claims no isomorphism. For 4.3: define ϖ_T := ∐ よ(p_y) on Syn//Ξ; state as a lemma that it is the pullback of ϖ along u(y, σ) := A_y[σ] (so representable by Lemma 2.3, extension Θ.A_y[σ], generic term (y, σ^{+A_y})), and that (id, u) is a morphism of natural models to Syn//Ξ, bijective on the terms of each type but not injective on types in general (equations between sorts); define the term model as the contextualisation, fully faithful over Syn//Ξ by Prop 2.16. It is only a natural model: the interpretation M_T (R4) and initiality (R5) need positivity. The deleted text was:*

```latex
\begin{remark}\label{rem:syntax-display-maps}
    The syntax of $T$ arises from the display maps in the same way, with the Yoneda embedding of $\Syn\dslash\Xi$ in place of the interpretation $\sem{\_}_M$. The natural transformation
    \[
        \varpi_T \coloneqq \coprod_{y \in \cat{A}} \yo(p_y) : \coprod_{y \in \cat{A}} \yo(\Phi_y.A_y) \to \coprod_{y \in \cat{A}} \yo(\Phi_y)
    \]
    of presheaves on $\Syn\dslash\Xi$ is representable. Its types over $\Theta$ are the pairs $(y, \sigma)$ of an admissible sort $y$ and a morphism $\sigma : \Theta \to \Phi_y$, the terms of $(y, \sigma)$ are the pairs $(y, \langle \sigma, t \rangle)$ with $t$ a term of $A_y[\sigma]$, and its extension is $p_{A_y[\sigma]} : \Theta.A_y[\sigma] \to \Theta$ with the generic term $(y, \sigma^{+A_y})$: the Yoneda embedding preserves the pullback of \cref{lem:iterated-pairing}(3), and coproducts of presheaves are disjoint and stable under pullback. The contextualisation of the natural model $(\Syn\dslash\Xi, \varpi_T)$ (\cref{def:contextual}) is the \emph{term model} of $T$.
\end{remark}
```

*End of 2026-11-19: Corollary `cor:model-nm` deleted at the user's request (Prop `prop:binding-model` names τ, p_τ, ν_τ = (y, ⟦σ⟧θ·p_τ, v_τ) itself and cites `lem:representable-types`(1) with the coproduct fact); natural-model types are bare pairs (y, θ). Remark `rem:syntax-display-maps` now follows Def 4.14 directly (Remark 4.15): ϖ_T := ∐ よ(p_y) on Syn//Ξ is representable, types (y, σ), terms (y, ⟨σ, t⟩), extension Θ.A_y[σ] with generic term (y, σ^{+A_y}), since よ preserves the pullback of Lemma 3.16(3); its contextualisation is the term model of T. Current order after Def 4.14: Remark 4.15, points 4.16, pointwise interpretation 4.17, tuples 4.18, representable types 4.19, slots 4.20, binding 4.21, binding is context extension 4.22, examples 4.23, literature 4.24.*

*Later on 2026-11-19: Lemma 4.18 split into Lemma 4.10(5) (sorts are small types, S(I, γ) = El(S)[γ]) and Lemma 4.18 `lem:representable-types` (for any type A: the square for p_A at γ is a pullback iff (p, v) represents A[γ], spelled out via Yoneda; p_A representable iff all A[γ] are). Prop 4.19 is now Corollary 4.19 `cor:model-nm` (label renamed): its proof asserts that a coproduct of natural transformations is representable iff each summand is, then cites Lemmas 4.16(3) and 4.18.*

*Representations instead of extensions, WRITTEN 2026-11-19. `def:extension` is gone (the user asked why it was needed). Lemma 4.18(2): the pullback square for p_{El(S)} at γ (drawn) iff (p, v) represents S(I, γ) on 𝒞/I. Prop 4.19(3): (p_{y(θ)}, v_{y(θ)}) represents ⟦η(y)⟧_M(I, θ). Lemma 4.22 (binding) is stated for a sort S and a representation (p, v) of S(I, γ), with ⟨f, a⟩ the unique h : f → p, v·h = a. Prop 4.23 transfers the representation along ⟦η(y)[σ]⟧_M(I, θ) = ⟦η(y)⟧_M(I, ⟦σ⟧_M(θ)) (Lemma 4.10(1)). Lemma 4.16 now has three items (square; presheaf equation ⟦A[σ]⟧_M = ⟦A⟧_M ∘ ∫⟦σ⟧_M; points of Θ.A as a dependent sum), followed by Cor 4.17 (points of a telescope are tuples).*

*Generic sorts via η, WRITTEN 2026-11-19 (amends the next note). Def 4.12 now reads: for y : [Φ_y] type ∈ Ξ (weakening as in §2.4.3), Ξ.Φ_y ⊢ η(y) : type by Prop 2.74, so η(y) is the generic sort, A_y := El(η(y)) the generic type, p_y := p_{A_y} : Φ_y.A_y → Φ_y the display map. Prop 2.74 (well-formed-syntax.tex) now states Γ.Θ ⊢ η(x) : c for x : [Θ]c ∈ Γ (user's request). The ν/app construction and z̄ are gone; components are ⟦η(z)⟧_M; examples use named forms (A_tm = tm(A), ⟦mul(x, y)⟧_M). Eq. (4.1) [Φ]C = Π_Φ(C) stays after Def 4.11 (user's request); its only use is the proof of Prop 4.21.*

*Framing of models, WRITTEN 2026-11-19 (supersedes the notation revision below). The user asked for a "totally rigorous definition" of the projections and agreed to: Def 4.12 `def:display-map`: for a slot z declared by [Φ]C = Π_Φ(C), with prefixes Ξ_{<z}, Ξ_{≤z} and projections π_z, π'_z: Φ_z := Φ[π_z], C_z := C[π_z^{+Φ}], z̄ := app_{Φ_z}(ν_{Π_Φ(C)}[π'_z]) ∈ Tm(Ξ.Φ_z, C_z); for a sort slot y: generic sort ȳ, generic type A_y := El(ȳ), display map p_y := p_{A_y} : Φ_y.A_y → Φ_y; in Syn all represented by η(z). Def 4.14 `def:theory-model`: (𝒞, M, R) with R a right adjoint of ∫ϖ_M, ϖ_M := ∐_{y∈𝒜} ⟦p_y⟧_M : Tm_M → Ty_M, so (𝒞, ϖ_M) is a natural model by definition (= R3 without contextuality). Lemma 4.18 `lem:presheaf-sorts` (sorts in 𝐏(𝒞) = small types; extension = representation of S(I, γ) on 𝒞/I; p_{El(S)} representable iff all S(I, γ) are). Prop 4.19 `prop:model-nm` now only describes types y(θ), terms, extensions (= representations of ⟦ȳ⟧_M(I, θ)), plus the converse. Remark 4.20 `rem:syntax-display-maps`: ϖ_T := ∐ よ(p_y) on Syn//Ξ is the pullback of ϖ along (y, σ) ↦ A_y[σ], representable by Lemma 2.3; its contextualisation is the term model of T (R2). Components are ⟦z̄⟧_M. The duplicate Π(Φ, C)/app_Φ paragraph is gone; Prop 4.21 uses Π_Φ, app_Φ of Def 3.14.*

*Notation revision, WRITTEN 2026-11-19 after the user called y(x⃗), Φ_y.y(x⃗) and p_{y(x⃗)} "confusing and imprecise": a sort slot y : [Φ_y] type ∈ Ξ (weakening as in §2.4.3) is, by Π-Tm, a sort over Φ_y in Syn//Ξ; El(y) is the type of its elements; p_y := p_{El(y)} : Φ_y.El(y) → Φ_y. A morphism σ : Θ → Φ_y is a tuple of arguments, y(σ) := y[σ] is y applied to them (App), El(y(σ)) = El(y)[σ] is a type of sort y over Θ, and its projection is the pullback of p_y along σ (drawn square, lem:iterated-pairing(3)); so p_y is to y what ϖ is to a natural model. Downstream: Def 4.13 ⟦p_y⟧_M : ⟦Φ_y.El(y)⟧_M → ⟦Φ_y⟧_M; Prop 4.17 Tm_M = ∐ ⟦Φ_y.El(y)⟧_M, terms = elements of ⟦El(y)⟧_M(I, θ); components ⟦z⟧_M (slot as a term of C_z over Φ_z); in 𝐏(𝒞) the small types ⟦El(y)⟧_M = El(⟦y⟧_M); Prop 4.20 with A := El(y(σ)); examples p_tm, ⟦El(m)⟧_M, ⟦mul⟧_M, ⟦El(tm)⟧_M; remark F(p_y).*

*Fifth version, WRITTEN 2026-11-18 after the user found the fourth "kinda fiddly", the notation
M_y confusing, and asked: define models by requiring certain projections to be representable;
make the natural model visible; examples monoids, natural models with Π, and a third. Numbers of
the scratch build: 4.11 theory `def:theory`; paragraph: for a sort slot y, the type y(x⃗) over its
hypotheses Φ_y, the projection p_{y(x⃗)} : Φ_y.y(x⃗) → Φ_y, and y(σ) := y(x⃗)[σ]; 4.12 three theories
`ex:theories` (T_mon; T_dep = (ty, tm), Uemura's Σ_DTT; T_Π extending Ξ_dep); 4.13 model
`def:theory-model` = (𝒞, M, R) with R_y a choice of pullback squares making ⟦p_{y(x⃗)}⟧_M
representable (NO contextuality any more: matches Def 3.1 and Awodey; initiality does not need it;
contextual models of T_mon are the monoids); 4.14 points; 4.15 points lemma (square + pairs);
4.16 extension; 4.17 the natural model of a model `prop:model-nm` (Ty_M, Tm_M, ϖ_M as coproducts;
types y(θ), terms, extensions I.y(θ)); 4.18 models slot by slot `prop:slots` + components
⟦z(x⃗)⟧_M + U = small types; 4.19 binding in presheaves `lem:binding`; 4.20 binding is context
extension `prop:binding-model` (⟦Π(y(σ), C)⟧_M(I, θ) ≅ ⟦C⟧_M(I.τ, (θ·p_τ, v_τ)),
τ = y(⟦σ⟧θ)); summary paragraph; 4.21 examples (presheaves of monoids, monoids on a terminal
category; T_dep = natural models with small presheaves; T_Π = natural models with dependent
products via P_ϖ); 4.22 remark (the classifying form F : Syn//Ξ → 𝐏(𝒞) with F(p) representable
is the form of Uemura Def 4.5 and KX Def 18; T_dep = Σ_DTT, Ex 5.7; Prop 4.18 ↔ Thm 5.19).
Lemma 4.10 (presheaf model) stays: the definition of a model interprets Ξ in 𝐏(𝒞).*

*Fourth version, WRITTEN 2026-11-18 at the user's request ("keep just the monoid and type theory
with pi types example and drop the others"; "Can we have a general result which characterizes
models of an arbitrary theory as natural models with extra structure?"; "Rephrase ... using a more
concise language and a more concise notation"). Numbers of the scratch build: 4.11 theory
`def:theory` (one line: Ξ with a set 𝒜 of sort slots); 4.12 two examples `ex:theories`
(T_mon, T_Π); 4.13 points `def:points`; 4.14 points and substitution `lem:points-extension`, then
a sentence that points of a telescope are tuples (the old tuple lemma is gone); notation
Π(Φ, C) and app_Φ for iterated products over a tuple of types; 4.15 models slot by slot
`prop:slots` (any model 𝒟 of ToS^ω: models of Ξ'.E over a fixed M' ↔ Tm(⟦Φ⟧_{M'}, ⟦C⟧_{M'}) via
pairing and app_Ψ), then the components M_z, ⟦z(x⃗)⟧_M = M_z, and in 𝐏(𝒞) terms of U = small
types (decoding, also written M_y); 4.16 model `def:theory-model` ((𝒞, M, R),
ϖ_M := ∐_{y∈𝒜} p_{M_y}); 4.17 extension `def:extension`; 4.18 models as natural models with
structure `thm:theory-models` (model of T = model of Ξ given by components + for every admissible
y, I, θ an extension of I by M_y at θ, such that every object is uniquely an iterated extension);
paragraph: admissible sorts form the natural model, the other components are structure on it;
4.19 binding `lem:binding`; binding in a model (M_y[σ]); 4.20 examples `ex:models` (monoids over a
terminal category; T_Π = contextual natural models with dependent products, via P_ϖ(Ty) and
P_ϖ(Tm)); 4.21 `rem:model-literature` (strict form of Uemura Def 4.5 and KX Def 18; Thm 4.18 is
the counterpart of Uemura Thm 5.19). Removed: A_y, admissible types, lem:points (tuples),
lem:model-natural, the slot-by-slot paragraph, T_λ and T_→, the CCC discussion. The previous
paragraphs of this note describe the third version and are superseded where they differ.*

*As written, beyond the outline below. 4.12(4): Ξ_→ = ty, tm, arr, lam, app, β, η, and
T_→ = (Ξ_→, {tm}). 4.20(2): the model of T_λ is described as before and then as a reflexive
object: ρ_I(t) := app(t·p, v) satisfies ρ ∘ lam = id, so the presheaf 𝒞(− × V, V), the
exponential of 𝒞(−, V) by itself, is a retract of 𝒞(−, V). 4.20(4): a model of T_→ is a
contextual natural model with function types; if the restriction maps of M_ty are bijections it
amounts to a contextual simply typed category with families with ⇒-structure
(Castellan–Clairambault–Dybjer Defs 9, 22), and with unit and product types these are equivalent
to cartesian closed categories (their Thm 5, re-read from the saved text). 4.21 calls the
definition a strict form of Uemura's and Kaposi–Xie's and mentions democratic models once.*

*Proposed 2026-11-18, after the user asked for CCCs as models ("the canonical example"), not yet
written. Problem: a sort without hypotheses (ty) is a presheaf on contexts, so models of T_→ have
context-dependent types (Kaposi–Xie FSCD 2024 §2, after Def 6, note the same: "a by hand
optimisation step is needed to replace Ty : Con → Set by Ty : Set"); also T_→ as written has no
closed types, so its term model is trivial. Fix: add unit, products (pair, fst, snd, β, β, η) and
str : [A : ty, B : [x : tm(A)] ty] ty with [A, C : ty] str(A, {x} C) = C and
[A, B, x : tm(A)] B(x) = str(A, B). In every model, restriction of M_ty along a projection p_τ is
then a bijection with inverse str (generic point plus naturality); by contextuality all
restrictions of M_ty are bijective. So models ↔ contextual scwfs with N1, ×, ⇒ (CCD Defs 9, 11,
12, 22), ↔ CCCs (CCD Thm 5); on objects up to isomorphism now, an equivalence of categories once
homomorphisms exist (to check). str is positive (same shape as pi). With base types o : ty,
initiality should give the Lambek–Scott theorem (term model = free CCC) as a corollary; expected,
not proved. Trivial alternative: the GAT of CCCs with 𝒜 = ∅ has CCCs as models on the nose.*

*Revised the same day after the user objected that the extended theory "is not at all how stlc is
usually presented". Recommendation now: keep the usual presentation (ty, tm, base types o : ty,
unit, prod, arr with their term formers, β and η; no str). Its models are contextual natural
models with unit, product and function types whose types may depend on the context (the same
phenomenon Kaposi–Xie remark on). Those whose presheaf of types has bijective restriction maps
are, up to isomorphism, the contextual scwfs with N1, ×, ⇒, hence correspond to CCCs (CCD Thm 5);
with homomorphisms they should form a full subcategory equivalent to CCCs (to check). The term
model lies in that subcategory: over a context of T every term of ty is the weakening of a closed
one (no slot produces ty from a tm argument; uses the term-inversion fact needed for R4), and
weakening is injective (interpret in the model in sets with ty the closed type expressions and
every tm(A) a singleton). So initiality in 4.3 still gives "the term model of STLC is the free
CCC on its base types", the Lambek–Scott correspondence. Rejected: str (non-standard), declared
rigid sorts (rejected by the user earlier), one sort per type (needs infinite signatures; ours
are finite telescopes).*

**Decisions (accepted).**
- (D1) The admissible data of a theory is a set 𝒜 of sort slots of Ξ, not a subpresheaf 𝒫 and
  not general schemas.
- (D2) One notion of model, the strict one: a contextual natural model with an interpretation of
  the signature. No C-systems in the text; mention them at most once, where the initiality
  theorem is related to Voevodsky's formulation.
- (D3) Notation: 𝒜 for the admissible sorts, Φ_y and A_y for the hypotheses and the type of a sort
  slot y; 𝒫 is retired.

**2.1 Definition (theory).** T = (Ξ, 𝒜): a signature with a set 𝒜 of its sort slots, the
*admissible sorts*. For a sort slot y of Ξ with entry `[Φ] type`:

    Φ_y  :=  Φ weakened to Ξ                      an object of Syn//Ξ (Def 4.6)
    A_y  :=  El(y(ν))  ∈  Ty_Syn(Ξ.Φ_y)           the sort y at the variables of Φ_y

where y is the slot as a closed term of its entry in Syn//Ξ (sentence after Def 4.6) and y(ν) its
iterated `app` (Def 3.1). An *admissible type* over a telescope Θ is an instance A_y[σ], for
y ∈ 𝒜 and σ : Θ → Φ_y in Syn//Ξ; with named slots it is written y(σ), e.g. `tm(a)`.

**2.2 Example (running theories).** T_mon = (Ξ_mon, ∅); T_λ = (Ξ_λ, {tm}), Φ_tm = ();
T_Π = (Ξ_Π, {tm}), Φ_tm = (A : ty), A_tm = tm(A). The existing example text, last sentences
changed.

**2.3 Definition (model).** For a small category 𝒞 with a terminal object and M ∈ mod_{𝐏(𝒞)}(Ξ),

    ϖ_M  :=  ∐_{y ∈ 𝒜} ⟦p_{A_y}⟧_M  :  ∐_{y ∈ 𝒜} ⟦Φ_y.A_y⟧_M  →  ∐_{y ∈ 𝒜} ⟦Φ_y⟧_M

a natural transformation of presheaves on 𝒞. A *model* of T is a triple (𝒞, M, R) with R a right
adjoint of ∫ϖ_M such that the natural model (𝒞, ϖ_M) is contextual (Def 2.4, Def 2.15). So a model
is a contextual natural model with an interpretation of the signature whose admissible sorts are
its types. Needs before it: Section 4.1 only.

**2.4 Points.** Definition (points) and Lemma (points as tuples): the existing 4.15, 4.16.
Lemma (points and substitution): for σ : Θ' → Θ and a type A over Θ,
⟦A[σ]⟧_M(I, θ') = ⟦A⟧_M(I, ⟦σ⟧_M(θ')) with the same restrictions, ⟦Θ.A⟧_M(I) = pairs (θ, x), and
⟦p_A⟧_M is the first projection. (The first equation was trimmed from 4.17; it is needed again in
2.6 and in §3.)

**2.5 Definition (extension)**: the existing 4.18. **Lemma (binding)**: the existing 4.19.

**2.6 Lemma (the natural model of a model).** In a model (𝒞, M, R): a type over I is a pair (y, θ)
with y ∈ 𝒜 and θ ∈ ⟦Φ_y⟧_M(I); its terms are the elements of ⟦A_y⟧_M(I, θ); R is a choice, for
all I, y, θ, of an extension (I.(y, θ), p, v) of I by ⟦A_y⟧_M at θ; every object is
pt.(y_1, θ_1).….(y_n, θ_n) for a unique sequence. For an admissible type A_y[σ] over Θ, a type C
over Θ.A_y[σ] and θ ∈ ⟦Θ⟧_M(I): ⟦Π(A_y[σ], C)⟧_M(I, θ) ≅ ⟦C⟧_M(I.(y, ⟦σ⟧_M θ), (θ·p, v)).
[Lemma 2.2, 2.4, 2.5.]

**2.7 Paragraph (a model unfolds slot by slot)**: the existing paragraph.

**2.8 Example (models unfolded), now exact.** (a) 𝒜 = ∅: Ty_M = ∅, 𝒞 is the terminal category,
models are the models of Ξ in sets; T_mon: monoids. (b) T_λ: one type over every object; the
objects are pt.tmⁿ, one for each n, the powers of V := pt.tm; 𝒞(I, pt.tmⁿ) ≅ M_tm(I)ⁿ and
M_tm ≅ 𝒞(−, V); app_I, lam_I : M_tm(I.tm) → M_tm(I), natural in I; β. Say what this is: with
ρ_I(t) := app(t·p, v), β gives ρ ∘ lam = id, so the presheaf 𝒞(− × V, V) = (yV)^(yV) is a retract
of yV: yV is a reflexive object of the cartesian closed category of presheaves on 𝒞, the classical
notion of a model of the untyped λ-calculus; conversely a reflexive object U of a cartesian closed
category gives the model with contexts Uⁿ and terms Hom(Uⁿ, U). The user asked whether one should
expect cartesian closed categories: those are the models of the simply typed calculus (possible
fourth example: ty, tm(A), unit, products, arrows, β, η, plus an operation that makes types
independent of the context; contextual models = cartesian closed categories with chosen structure
by Castellan–Clairambault–Dybjer Thm 5, verified 2026-11-16; the claim about the extra operation
is from the second design round and unproved). (c) T_Π: Ty_M = M_ty and ϖ_M = (M_tm → M_ty); a
model is a contextual natural model with dependent products in the sense of Def 3.1(2). No caveat
about injectivity of tm.

**2.9 Remark (literature).** Forgetting R and the uniqueness in contextuality leaves "ϖ_M is
representable": Uemura's models (Def 4.5) and, with chosen extensions, Kaposi–Xie's naive models
(Def 18, Problem 17); democratic models (Uemura Def 6.1) are those generated by the admissible
sorts. Remaining difference: entries of ToS^ω have hypotheses of arbitrary rank, over sorts that
need not be admissible, interpreted by products of presheaves.

**Removed from the text.** The subpresheaf 𝒫 and schemas in 4.11; the property-style definition
4.13 with contextual objects and democratic models (now the remark); Lemma 4.14.

**Order of writing.** (i) 2.1–2.3, (ii) 2.4–2.7, mostly existing text, (iii) 2.8–2.9.

## 3. Positive theories

*What comes after Section 4.2 (recommendation given to the user on 2026-11-19, awaiting their decision). The user asked whether to define positive theories next or first the category of models "for as wide a class as possible". Recommendation: Section 4.3 = positive types and chains (defined for every theory, they depend only on 𝒜), positive theories, the points of positive chains by iterated context extension (Prop 4.20, with the representation fact that was dropped from its statement), then homomorphisms (F, φ) and Mod(T), then the three examples; Section 4.4 = term model, syntactic model, initiality (R2, R4, R5). Reason for the order: a homomorphism must act on the points of the hypotheses of every slot; over a binder of an admissible sort the points are elements over an extended context (Prop 4.20) and F preserves extensions, over any other binder they are functions and a map on elements does not transport them (example: lam : [b : [x : tm] tm] tm with tm not admissible). So positivity is exactly what makes (F, φ) definable. For all theories the only uniform notion is that of functional logical relations (span model, §5), which do not compose in general: X = {0}, {0,1}, {0,1,2} with c : [f : [x : X] X] X, c_2(f) = 0 if f(0) = 0, c_3(f) = c_2(f|) if f preserves {0,1} and c_3(f) = 2 if f(0) = 0, f(1) = 2 (re-checked 2026-11-19). Section 4.2 itself needs nothing more; the comparison with Uemura and Kaposi–Xie has no home since the user deleted `rem:model-literature`, and fits best after initiality. Open obligation unchanged: term inversion over positive chains, needed for R4 only.*

*Positioning, 2026-11-18 (verified from the saved text of Uemura's paper). For the theories his
logical framework expresses, Uemura already has the results planned in §§3–4: Thm 6.10 (every type
theory has a bi-initial model I(T); for T = R(Σ) its base is the contexts of representable types
and its elements are the morphisms of R(Σ), cf. 3.6–3.7 below), Def 7.1 and 7.4 (T-theories =
cartesian functors T → Set; internal language L_T S(A) = A^S(1), cf. the functor of points in 3.4),
Thm 7.20 and Thm 7.31 (democratic models ≃ T-theories, cf. 4.2, which is therefore NOT new),
Ex 7.3 (finite theories, cf. 3.8). Dictionary: R(Σ) ↔ 𝒫os_T, base of I(R(Σ)) ↔ 𝒞_T. What remains
ours: the comparison (𝒫os_T is a representable map category and our models are his; unproved),
the reduction to the single initiality theorem of Chapter 3 for the higher-rank syntax, theories
that are not positive, positivity as the boundary, and §5. Decide with the user whether to prove
the comparison and cite, or to give a direct proof and present it as a new proof of a known
result.*

*Comparison theorem, proposed to the user 2026-11-18 (they called this route "the most efficient
and honest"). Positive theory, for this purpose: (a) every entry of Ξ is `[Φ]C` with Φ a positive
chain and C = `type`, a type expression, or an equation between elements (no sort equations as
axioms: they could only be realised up to isomorphism); (b) 𝒫 is generated by positive types over
positive chains. Let 𝕋 := (𝒫os_T, ℛ_T), ℛ_T the arrows isomorphic to composites of projections of
admissible types.*
*(1) 𝕋 is a representable map category (Uemura Def 4.1–4.2): finite limits from the terminal
object, extensions and equality telescopes (Id at elements; for Π(A, C) the telescope
Π(A, Eq_C(app l, app r))); ℛ_T is stable under pullback because 𝒫 is a subpresheaf; pushforward
along p_A is the Π of a positive telescope, positive by (P3). Argued inside the natural model
𝒫os_T, no raw syntax. Uses only 𝒫 ⊆ Pos.*
*(2) For a model (𝒞, M) of T with 𝒞 having a terminal object, ⟦−⟧_M restricted to 𝒫os_T is a
representable map functor to presheaves on 𝒞, i.e. a model of 𝕋 (Def 4.5). Uses Prop 4.7 (strict
preservation of extension, Id, Π) and the definition of a model.*
*(3) Realisation: every model of 𝕋 on 𝒞 is isomorphic to one from (2). Read M off the values of G
at the slots by recursion along Ξ, then show G ≅ ⟦−⟧_M by induction on positive chains, every
expression being a slot applied to arguments. Needs (a). This is our counterpart of his Thm 5.17
and the only part with real work; the syntactic model (PT 6.2–6.4) is the instance G = Yoneda.*
*Derived. From (1), (2), Thm 6.10: a bi-initial model with base ≃ 𝒞_T and elements = substitutions
(Def 6.7), mapping essentially uniquely to every model of T. With (3): that model is a model of T,
Mod(T) ≃ Mod_𝕋, and by Thm 7.20/7.31 democratic models of T ≃ Lex(𝒫os_T, Set); hence locally
finitely presentable, free models on positive chains (Ex 7.3), completeness, the GAT comparison,
and the separation of compact Hausdorff spaces. NOT derived: strict initiality among C-systems
with strict homomorphisms (so not Voevodsky's form), and the slot-by-slot description of
homomorphisms. Chapter 3 alone is an instance of Voevodsky's conjecture, for the one theory
ToS^ω.*

*Voevodsky's form for object theories (answer of 2026-11-18). Obtainable for positive theories
presented by schemas, by the strict theorem PT 7.5 rather than through Uemura: (1) T as a type
theory 𝔗_T in the sense of Definition 2.x (`def:type-theory`): raw syntax = expressions over the
arity of Ξ, one rule per slot; (2) its syntax Syn_{𝔗_T}, a subquotient, with contexts = lists of
schema instances; (3) strict models: chosen extensions, types = schema instances at points,
contexts uniquely lists of types; slot by slot these are C-systems with operations; strict
morphisms; (4) initiality by PT 7.3–7.4 with PT 6.2 as the core. Open: re-basing PT 6.2 and §7,
conservativity of ToS^ω over the slot rules, adequacy for less annotated presentations. PT 6.2 is
also part (3) of the comparison theorem at the Yoneda functor, so the two routes share their
core.*

*The route in six steps, as explained to the user on 2026-11-18 (schemas as data, strict models
on top of Definition 4.13).*
*(R1) Positive theory presented by schemas (Θ_i, A_i): every entry of Ξ has a positive chain of
hypotheses, every Θ_i is a positive chain, every A_i is positive. Positive types and chains must
return to the text.*
*(R2) Term model 𝒞_T: contexts are lists of schema instances; a type over Γ is a pair (i, σ) with
σ : Γ → Θ_i in Syn//Ξ, its terms are the terms of A_i[σ], Γ.(i, σ) := Γ.A_i[σ]. Formally the
contextualisation of Syn//Ξ with ϖ pulled back along (i, σ) ↦ A_i[σ] (Lemma 2.3, Def 2.15). For
T_Π the types over Γ are the terms of ty.*
*(R3) Strict model (𝒞, M, R): Ty_M := ∐_i ⟦Θ_i⟧_M, ϖ_M := ∐_i ⟦p_{A_i}⟧_M, R a right adjoint making
(𝒞, ϖ_M) a contextual natural model. Strict morphism (F, φ): F preserves pt, φ natural on points
of positive chains at all stages, F(I.(i, θ)) = FI.(i, φθ), F(p) = p, φ(θ·p, v) = (φθ·p, v).*
*(R4) Syntactic model, the core [PT 6.2–6.4]: M_T ∈ mod_{𝐏(𝒞_T)}(Ξ) with
ev : (Syn//Ξ)(Γ, Δ) ≅ ⟦Δ⟧_{M_T}(Γ), natural in the context Γ and the positive chain Δ; a sort slot
is interpreted by the sets of terms of that sort, an element slot by itself; induction on
positive chains, positive types and expressions, binding lemma at products. Needs from the
syntax: unique decomposition of a type into hypotheses and conclusion (inversion; `type` ≠ B can
be shown by the model in sets with singleton sorts), and that over a positive chain every sort is
a sort slot of Ξ applied to arguments and every element is a slot of Ξ or an entry of the chain
applied to well-formed arguments (term inversion, to be proved). Bookkeeping along prefixes of Ξ.
A shortcut through the classifying property fails: the nerve Γ ↦ Syn//Ξ(Γ, −) is not a morphism
of models of ToS^ω (it fails at U and at products over non-admissible types).*
*(R5) Initiality [PT 7.1–7.4]: F() := pt, F(Γ.(i, σ)) := FΓ.(i, ⟦σ⟧_N γ_Γ),
γ_{Γ.(i, σ)} := (γ_Γ·p, v), φ(ev θ) := ⟦θ⟧_N(γ_Γ); FΓ represents the points of Γ; uniqueness by
Yoneda at the tautological points ev(id). Short. With schemas no stability axiom is needed.*
*(R6) Packaging: 𝒞_T as a subquotient of the raw natural model of T (from Chapter 2); strict
models unfolded slot by slot as C-systems with operations, strict morphisms as homomorphisms
[PT 5.3; converse unproved]. No separate rule set is generated: the rules of T are those of ToS^ω
with the slots of Ξ as constants (the user rejected general rule generation on 2026-11-01).*

*Revised outline of Section 4.3, Positive theories and initiality (2026-11-18; supersedes 3.1–3.9
below where they differ).*
*3.1 Positive types, for T = (Ξ, 𝒜): the least family Pos(Θ) ⊆ Ty_Syn(Ξ.Θ) with (P1) El(S) for
every sort S; (P2) Id(l, r) for terms l, r of some El(S); (P3) Π(A, C) for every admissible type A
over Θ and every C ∈ Pos(Θ.A). In entry form: `[A_1, …, A_k] C` with C = B or C = (l =_B r) and
every A_j admissible (uses only Π(A, [Φ]C) = [A ⋈ Φ]C from Lemma 3.8). 3.2 Lemma: Pos is stable
under substitution. 3.3 Positive chains: telescopes with positive entries; they form a contextual
sub-natural-model 𝒫os_T of Syn//Ξ (Lemma 2.17). T is positive if every entry of Ξ has a positive
chain of hypotheses; then every Φ_y is a positive chain. 3.4 Homomorphisms = strict morphisms
(F, φ) (R3). 3.5 The term model 𝒞_T (R2). 3.6 The syntactic model (R4). 3.7 Initiality (R5).
3.8 Packaging (R6). 3.9 Remarks: the functor of points Δ ↦ ⟦Δ⟧_M(pt) is a morphism of natural
models 𝒫os_T → 𝐒, representable for the syntactic model; Uemura's Thm 6.10 and 7.31; our own
functorial semantics is not proved (advice given to the user: not worth it; local presentability,
if wanted for §5, comes more cheaply from the essentially algebraic description in R6).*


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

*UNIFIED DESIGN (2026-11-20, after the user rejected the separation: "the construction of the relation model and the corresponding category should be done on a class of theories that encompassess both the positive theories and Haus, and the definition of the category of models should agree with the more straightforward construction for positive theories"). This supersedes the next note where they differ: the base-category obstruction restricts ONE clause, it does not split the class. (1) One construction for all theories: Rel F for every F : 𝒞 → 𝒟 with F(pt) = pt (PT A.1); a morphism of models is (F, r), r a model of Ξ in Rel F over (M, M'), with (ext): F preserves the chosen extensions at related points (PT A.5). (2) Mod(T) := CONTEXTUAL models with these morphisms. Needed for the Hausdorff theory (its contextual models are the models in sets); for positive theories it is the full subcategory of the (F, φ)-category on contextual models. Def 4.14 does not require contextuality, so this is a decision for the user. (3) Directed theories, now for arbitrary 𝒜. Forward F ::= S(t) | l =_S r | [Ψ]C with C a sort or element equation and every entry of Ψ an admissible type, or built from data sorts only, or backward, the last ONLY IF 𝒜 = ∅. Backward B ::= D(t) | l =_D r | [Ψ]C with C over a data sort and every entry of Ψ forward. T is directed if every hypothesis of a sort slot, element slot or sort-equation slot is forward or backward and the hypotheses of every admissible sort are forward (so that F is determined on extensions). Positive theories are directed (every hypothesis is [A_1..A_k]C with A_i admissible); T_K is directed (𝒜 = ∅). (4) Statements. (A) For directed T, Mod(T) is a category. (B) For positive T, the relational morphisms are the pairs (F, φ) (PT A.6, A.7, on paper, old framework). (C) Mod(T_K) = KHaus (N Thm 4.4, on paper). (5) Why the clause 'only if 𝒜 = ∅': an element of a function entry has components at all stages over FI, a morphism tests only those in the image of F; a bound variable of admissible sort has its generic element at an image stage ((ext)), a bound variable over data is a pointwise product, a bound function variable has neither; a contextual model without admissible sorts has one stage. Backward entries are functional over every F: b is recovered from b' at all of its own components, and admissible hypotheses inside them go through the binding lemma (checked by hand 2026-11-20). (6) Pieces of (A) and their status: positive binders = PT A.6; backward entries over F = checked by hand; function binders over base 1 = by hand and brute force; data sorts are constant presheaves with bijective homomorphisms = standard, not written; the combined induction and Rel F for the current ToS^ω are not written.*

*Syntactic criterion: directed theories (proposed to the user on 2026-11-20 after "I'd prefer a syntactic criterion, even if it's … only sufficient - but I'd like it to be as general as possible"; proof in outline only, rules checked by brute force on small sets; supersedes 5.3–5.5 below where they differ). Setting: 𝒜 = ∅, models in sets (= contextual models). Data sort: a sort presented inductively (constructors with data or recursive arguments, an iterator into every sort, computation and uniqueness laws); finite sorts with case, N. Homomorphisms are bijective on data sorts and the iterator is related along every family of maps (both sides are algebra maps out of an initial algebra). Variance of occurrences: in a hypothesis, its conclusion is covariant, the conclusions of its own hypotheses are contravariant, alternating with each level of binding; an element equation counts as an occurrence of its sort. DIRECTED: in every hypothesis of every sort slot, element slot and sort-equation slot, the occurrences of non-data sorts are all covariant or all contravariant, and no hypothesis at any depth has conclusion `type` or is an equation between sorts; element-equation slots are unrestricted. Equivalent to the recursive rules: S(t) forward (both ways if S is data); l =_S r forward (both if S is data); [Ψ]C forward iff Ψ backward and C forward, backward iff Ψ forward and C backward. Actions: f ↦ C(h) f Ψ(h), resp. f' ↦ C(h)^{-1} f' Ψ(h). Claim: for a directed theory the models in sets and the relational homomorphisms form a category; a homomorphism is a family of functions on the non-data sorts with h(c φ) = c'(φ') for related fillings. Proof plan: induction along Ξ and on entries, showing that the relation is the graph of the action, E(id) = id, E(kh) = E(k)E(h) resp. E(h)E(k); hence unique interpolation at every slot, and the exact condition (E)/(S)/(I) above applies. Hypotheses of one slot may point in different directions and may depend on each other. T_K is directed (u and its two premises are covariant). Also covered: all first-order theories; sup : [s : [n:N]X] X (maps preserving countable sups). Sharpness, checked: [x:X]Y fails; [q:[b:2]X]X fails; mixed variance inside one hypothesis fails, e.g. [x:X, p:[y:X]2]2 with |X| = 3, 2, 1, h = (0,0,1): the pair is kh-related and f has no h-related partner at all. Brute force also confirmed unique interpolation for [b:2, p:[x:X]2]X and [s:[b:2]X, x:X]2. Warning: small sizes can hide failures ([f:[x:X]X]2 passes at size ≤ 2). Extensions, same argument, not written: codata sorts (corecursor with uniqueness) and sorts in definable bijection with an entry over data sorts are bijective too; a sort variable may be bound in an element slot, composition then still holds but id is a homomorphism only on models where that operation is natural. CORRECTION of 5.9 (iv): over a base other than 1 and F not surjective on slices, a covariant function entry with a non-admissible, non-data hypothesis is NOT functional: Π(P, C)(FI) has components at all g : K → FI, the relation tests only those of the form Ff. Example: 𝒞 = 1, 𝒟 with objects pt and K, Aut(K) = Z/2, X'(pt) = ∅, X'(K) = Z/2; two different u' over the same u for u : [p:[x:X]2]2. So the 'common generalisation' is false as stated, and for a directed theory that is not positive Mod(T) must consist of the contextual models. Over arbitrary bases only these survive: hypotheses of hypotheses that are admissible (binding lemma) or over data sorts (pointwise products), and contravariant entries (all their components are tested). Not proved.*

*Exact condition for composition, and precedents (worked out for the user on 2026-11-20; the argument is mine and elementary, the checks are brute force on small sets, nothing is in the text). Setting: Ξ has a category of models, one slot is added without equations, Φ(h) is the relation between fillings of its hypotheses along h. (E) Element slot c : [Φ]B, B a closed sort with two elements that kh separates: 'c ~_h c' and c' ~_k c'' imply c ~_{kh} c''' for all c, c', c'' iff every pair in Φ(kh) is joined by a zigzag of Φ(h)- and Φ(k)-pairs. Sufficiency: v := kh∘c on M-fillings, k∘c' on M'-fillings, c'' on M''-fillings is constant along edges. Necessity: let K be the zigzag component of φ; put c, c', c'' := b_0, h b_0, kh b_0 on K and b_1, h b_1, kh b_1 elsewhere. (S) Sort slot S : [Φ] type: the composite component is determined iff every pair in Φ(kh) has exactly one interpolant φ' with φ ~_h φ' ~_k φ''. (I) id is a homomorphism iff Φ(id) lies in equality (Reynolds' identity extension; fails at bound sort variables). Lax/oplax calculus: T(h);T(k) ⊆ T(kh) for T = [A]B needs the reverse inclusion (interpolation) at A and the lax one at B; interpolation at [A]B is what forward/backward gives. Equations can only help (if, rec are related along everything). Brute force (sets of size ≤ 3, all h, k; scripts were in the session scratchpad): interpolation, with unique interpolant, holds for X, [x:X]2, [b:2]X, [x:X,y:X]2, [p:[x:X]2]2, [p:[x:X]2]X, [q:[b:2]X]2 and fails, zigzags included, for [x:X]X, [x:X]Y, [q:[b:2]X]X (first failure at sizes 0, 1, 2); criterion (E) agrees with exhaustive enumeration of c, c', c'' on sets of size ≤ 2. Dependent B, and a syntactic converse beyond hypotheses of the shape [x:X]Y, are open. Alternative that always composes: pre-logical relations; in our terms presumably maps natural on the points of positive chains, i.e. commuting with all definable first-order operations. For T_K this seems to forget lim (definable ultrafilters are principal), so it is no substitute there. Precedents, all read in the papers: Kaposi–Kovács–Altenkirch POPL 2019 §5 (U^M := T_0 → T_1, El := graph, 'no higher-order functions because Π is strictly positive'; category only in §7); Kaposi–Kovács LMCS 16(1) 2020 §7 and §9; Kovács' thesis arXiv:2302.08837 §2.2.2 ('every morphism is a functional logical relation', 'such relations do not generally compose', 'polarity issues'); Kaposi–Xie FSCD 2024 intro and Def 3 ('no meaningful notion of homomorphism of second-order models'); Honsell–Sannella, Pre-logical relations, CSL 1999 (Ex. 5.4 'missing link in B is not a function', Prop. 5.5, Cor. 6.2); Angiuli–Cavallo–Mörtberg–Zeuner POPL 2021 Def 5.6, 5.11, Thm 5.12 ('reverse transitivity' = interpolation, S_1 → S_2 suitable when S_1 positive); Coquand–Danielsson 2013 (Is-isomorphism' as a logical relation, the groupoid case). See the memory note relational-homomorphisms-literature.*

*Generality of the span-model morphisms (answer given to the user on 2026-11-19; sources: PT Appendix A, N 4.3, 4.4, 7.3; all on paper for the older framework, nothing re-based yet). (1) The definition needs nothing from the theory: Rel F exists for every F : 𝒞 → 𝒟 with F1 = 1 (PT A.1, A.2 marked routine), a relational morphism is (F, r) with (ext) (PT A.5). With bijections as sort relations one gets a groupoid for every signature (N 4.3 (b), not written). (2) A category is a property: composition can fail (c : [f : [x:X]X]X), identities can fail when an operation binds a sort variable and is not parametric (N 4.3 (c)). (3) Sufficient conditions. Positive theories: relational morphisms = (F, φ), PT A.6 and A.7, for ALL positive theories and not only GATs (5.2 (a) below understates this; I had repeated the understatement to the user and corrected it). Binders with a direction (N 7.3): sorts and element equations are forward; [Φ]c is forward if Φ is backward and c forward, backward if Φ is forward and c backward; a sort is backward iff every homomorphism is bijective on it, a property and not data; if every binder entry of every slot is forward or backward, homomorphisms compose (proved without bound sort variables, bijective case to recheck). Without bijective sorts this class is the first-order theories. The four non-dependent cases of [A]B were re-derived on 2026-11-19: backward/forward gives f' = B(h) f A(h), forward/backward gives f = B(h) f' A(h), forward/forward and backward/backward give a commuting-square condition with no direction. (4) Open: the common generalisation (hypotheses admissible or with a direction, 5.9 (iv)); any converse. Operations fixed by a uniqueness law (if, a recursor) are preserved whatever their binders are, so the criterion is only sufficient. (5) Composing is not being the expected maps: for sup : [p : [x:X]𝟚]X the morphisms compose and are not the sup-preserving maps (N 4.4 (iii)).*

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

---

## Appendix. Proofs of 2026-11-20 (paper arguments for §0; claim numbers C1–C15 refer to the candidate design summarised in §0)

Notation as in `dissertation/chapters/theories.tex`. Everything here is a paper argument by the
orchestrator; nothing is in the dissertation text. Claims are numbered as in CANDIDATE.md.

### P1. The relational model `Rel(i, i')` (claim C1)

Data: models D, D' of ToS^ω; a small category ℬ with terminal object; functors `i : ℬ → D`,
`i' : ℬ → D'` with `i(pt) = pt`, `i'(pt) = pt`. Nerve: `N G(I) := D(iI, G)`,
`N A(I, g) := Tm_D(iI, A[g])`, restriction `a·f := a[i f]`. Likewise N' for i'.

Category 𝓡. Objects `(G, G', R)`: R a presheaf on ℬ with a map to `N G × N' G'`. Morphisms: triples
`(n, n', n^R)` commuting with the maps. Terminal object `(pt, pt, 1)`.
Types over `(G, G', R)`: triples `(A, A', A^R)` with `A ∈ Ty_D(G)`, `A' ∈ Ty_{D'}(G')`, and sets
`A^R(ρ; a, a')` for `ρ ∈ R(I)` over `(g, g')`, `a ∈ Tm(iI, A[g])`, `a' ∈ Tm(i'I, A'[g'])`, with
restriction maps `A^R(ρ; a, a') → A^R(ρ·f; a[i f], a'[i' f])`, functorial.
Terms of `(A, A', A^R)`: triples `(t, t', t^R)`, `t^R(ρ) ∈ A^R(ρ; t[g], t'[g'])`, natural in ρ.
Reindexing along `(n, n', n^R)`: `(A[n], A'[n'], (σ; a, a') ↦ A^R(n^R σ; a, a'))`; strictly functorial.
Extension: `(G.A, G'.A', R.A^R)` with `R.A^R(I) := {(ρ, a, a', α)}`, mapping to `(⟨g, a⟩, ⟨g', a'⟩)`.
Morphisms into it are pairs (morphism, term) uniquely, so 𝓡 is a natural model with chosen
extensions, and both projections are morphisms of natural models (they preserve pt, extension,
projections, generic terms on the nose).

Universe. `Ū := (U, U', U^R)` over the terminal object, `U^R(ρ; S, S')` := the set of natural
transformations `h : N(El S) → N'(El S')` of presheaves on ℬ/I, i.e. families
`h_f : Tm(iJ, El(S[i f])) → Tm(i'J, El(S'[i' f]))` for `f : J → I` with `h_f(a)[i' k] = h_{fk}(a[i k])`.
Decoding of a term `(S, S', S^R)` of Ū over `(G, G', R)`:
`El(S, S', S^R) := (El S, El S', (ρ; a, a') ↦ {⋆ | S^R(ρ)_id(a) = a'})`. Stable under reindexing.

Products. For `Ā` over Ḡ and `C̄` over `Ḡ.Ā`, and `b ∈ Tm(iI, Π(A,C)[g])`, write
`b(f, a) := app(b)[⟨i f, a⟩] ∈ Tm(iJ, C[⟨g∘i f, a⟩])` for `f : J → I`, `a ∈ Tm(iJ, A[g∘i f])`.
`Π(Ā, C̄) := (Π(A,C), Π(A',C'), Π^R)`,
`Π^R(ρ; b, b')` := families `w(f, a, a', α) ∈ C^R((ρ·f, α); b(f, a), b'(f, a'))` over `f : J → I`,
`α ∈ A^R(ρ·f; a, a')`, with `w(f, a, a', α)·k = w(fk, a[ik], a'[i'k], α·k)`; restriction
`(w·f)(k, …) := w(fk, …)`. `lam(u, u', u^R) := (lam u, lam u', ρ ↦ ((f, a, a', α) ↦ u^R(ρ·f, a, a', α)))`.
It is well typed because `(lam u)[g](f, a) = u[⟨g∘i f, a⟩]`. Inverse:
`app(b, b', w) := (app b, app b', (ρ, a, a', α) ↦ w_ρ(id, a, a', α))`; `lam∘app = id` by the
naturality of w in ρ. So the square of `def:model`(2) is a pullback. Stability under reindexing is
strict because it is strict in D and D' and `n^R` is natural.

Equations. At Ū: `Id((S,S',S^R), (T,T',T^R)) := (Id(S,T), Id(S',T'), (ρ; ⋆, ⋆) ↦ {⋆ | S^R(ρ) = T^R(ρ)})`.
A term exists iff `S = T`, `S' = T'` and `S^R = T^R`, and then it is unique. At `El(S̄)`:
`Id(ā, b̄) := (Id(a,b), Id(a',b'), (ρ; ⋆, ⋆) ↦ {⋆})`; a term exists iff `a = b` and `a' = b'`, which is
`ā = b̄` because the witness sets of `El(S̄)` are subsingletons. So the square of `def:model`(3) is a
pullback. (If a type is both Ū and some El(S̄), the two definitions agree, for the same reason.)

Hence 𝓡 is a model of ToS^ω and the projections are morphisms of models. By `prop:classifying`,
for `m ∈ mod_𝓡(Ξ)` with projections M, M': `π∘⟦_⟧_m = ⟦_⟧_M`, `π'∘⟦_⟧_m = ⟦_⟧_{M'}`. A global element
of `⟦Ξ⟧_𝓡` over `(M, M')` is an element of the apex of the span at the terminal stage (this is
where `i(pt) = pt` is used).

Instance `Rel(よ, よ∘F)` for `F : 𝒞 → 𝒞'`, `F(pt) = pt`: `N = id`, `N'Γ' = Γ'∘F`. This is the model of
PT Def. A.1. It is the presheaf model on the collage 𝒢_F (objects `I_0, I_R` for I ∈ 𝒞 and K for
K ∈ 𝒞'; `hom(J_0, I_R) = 𝒞(J, I) = hom(J_R, I_R)`, `hom(K, I_R) = 𝒞'(K, FI)`, the ends full, nothing
out of the R-copy) with the sub-universe of those small presheaves on `𝒢_F/I_R` whose R-part
projects bijectively onto the 𝒞-part. Slices at the end objects are `𝒞/I` and `𝒞'/K`, so the two
restrictions preserve Π and U strictly.

### P2. Relational binding (claim C2)

Let `ρ : g ~ g'` at I and `(p : I⁺ → I, v, v', α_v)` with `α_v ∈ A^R(ρ·p; v, v')`, generic: for all
`(f : J → I, a, a', α ∈ A^R(ρ·f; a, a'))` there is exactly one `k : J → I⁺` with `pk = f`,
`v[ik] = a`, `v'[i'k] = a'`, `α_v·k = α`. Then for fixed b, b',
`Π^R(ρ; b, b') → C^R((ρ·p, α_v); b(p, v), b'(p, v'))`, `w ↦ w(p, v, v', α_v)`, is a bijection, with
inverse `ω ↦ ((f, a, a', α) ↦ ω·k)`. Indeed `b(p, v)[ik] = app(b)[⟨ip, v⟩∘ik] = app(b)[⟨if, a⟩] = b(f, a)`,
and naturality of w gives `w(f, a, a', α) = w(p, v, v', α_v)·k`.

### P3. Functionality for forward and backward types (claim C5)

Setting: a homomorphism `(F, r)` between models `(𝒞, M, R)`, `(𝒞', M', R')` of a directed theory;
𝓡 := Rel(よ, よF). Statement S(E), for a type E over a directed telescope Θ and every witness
`ρ : θ ~ θ'` at I:
 forward E: for every `e ∈ ⟦E⟧_M(I, θ)` there is exactly one pair `(e', ε)` with
   `ε ∈ ⟦E⟧^R(ρ; e, e')`; write `e' = E(ρ)(e)`;
 backward E: for every `e' ∈ ⟦E⟧_{M'}(FI, θ')` exactly one pair `(e, ε)`; write `e = E(ρ)(e')`.
Induction on the generation, for all Θ, ρ at once.
 (F1) `A_y[σ]`: the relation is the graph of `h_y(⟦σ⟧^R ρ)_id`.
 (F2) `Id(l, r)` at `A_y[σ]`: `⟦l⟧`, `⟦r⟧` preserve witnesses, so `l(θ) = r(θ)` gives
   `l'(θ') = h(l θ) = h(r θ) = r'(θ')`.
 (F3) `Π(A, C)`, `A = A_y[σ]`, y ∈ 𝒜. Let `τ = (y, ⟦σ⟧_M θ)`, `τ' = (y, ⟦σ⟧_{M'} θ')`. By (ext),
   `F(I.τ) = FI.τ'`, `F(p_τ) = p_{τ'}` and `(v_τ, v_{τ'})` is related over `ρ·p_τ`. This tuple is a
   generic related pair: for `(f, a, a', α)`, `k := ⟨f, a⟩` is the only morphism over f with
   `v_τ·k = a`, and then `v_{τ'}·Fk` is related to `a` over `ρ·f`, hence equals `a'` by (F1); so
   `Fk = ⟨Ff, a'⟩`. By P2 and `lem:binding` on both sides, S(C) at `(ρ·p_τ, ⋆)` gives S(Π(A, C)) at ρ.
 (F4) `Π(P, C)`, P a data type: `⟦P⟧` is a constant presheaf in both models and its relation is the
   graph of the canonical bijection, with unique witnesses; elements of the product at `(I, θ)` are
   families indexed by the elements d of P, and witnesses are families of witnesses; apply S(C)
   componentwise.
 (F5) `Π(P, C)`, P backward, C forward, 𝒞 = 𝒞' = 1: `Π^R(ρ; b, b')` is the set of families of
   witnesses `w(p, p', π) ∈ C^R((ρ, π); b(p), b'(p'))`. By S(P) every p' has exactly one `(p, π)`.
   So `b'(p') := C(ρ, π)(b(P(ρ)p'))` is the only possibility, and it works.
 (B1), (B2) data: bijection; injectivity of `h_D` reflects equations.
 (B3) `Π(P, C)`, P forward, C backward: given b', the only possibility is
   `b(f, p) := C(ρ·f, π)(b'(Ff, P(ρ·f)p))`, where π is the witness of `p ~ P(ρ·f)p`. It is natural
   in f because witnesses restrict and are unique. Only stages of the form Ff are evaluated, so
   this holds over every F.
Corollary: over a directed telescope, a pair of points has at most one witness, and Θ(ρ) acts
entrywise.

### P4. Composition and identities (claim C6)

Let `(F, r) : 𝒮 → 𝒮'`, `(F', r') : 𝒮' → 𝒮''`. Build `r'' ∈ mod_{Rel(よ, よF'F)}(Ξ)` over `(M, M'')` along
the slots of Ξ, with the invariant
 (Comp) on directed telescopes over the prefix: `θ ~'' θ''` iff there is θ' with `θ ~ θ' ~' θ''`;
        θ' is then unique.
Uniqueness of θ' is entrywise: at a forward entry `θ'_j = E(ρ)(θ_j)`, at a backward one
`θ'_j = E(ρ')(θ''_j)`.
 Sort slot `y : [Φ] type`: for `φ ~'' φ''` with interpolant φ', `h''_y := h'_y(ρ')∘h_y(ρ)` (whiskered
   with F); natural in the stage.
 Element slot `c : [Φ] A_y[σ]`: `h''(c_M φ) = h'(h(c_M φ)) = h'(c_{M'} φ') = c_{M''} φ''`; the middle
   steps use that `⟦σ⟧` preserves witnesses, so the interpolant of `(σφ, σφ'')` is `σφ'`.
 Equation between sorts: both sides have the same composite maps, by the same argument.
 Equation between elements: nothing to check (the witness sets of El are subsingletons).
 Slots presenting a data sort: related along everything (C4).
 (Comp) for the longer prefix: show by induction on forward/backward types that `e ~ e' ~' e''`
   implies `e ~'' e''` ((F1) by the definition of h''; (F3) through the generic pair; (F4)
   componentwise; (F5), (B3): for a witness `p ~'' p''` take the interpolant p' given by (Comp) for
   P, then `b(p) ~ b'(p') ~' b''(p'')` and the hypothesis for C). Together with P3 for r'' this gives
   `E(ρ'') = E(ρ')∘E(ρ)` for forward E and `E(ρ)∘E(ρ')` for backward E, hence (Comp).
 (ext) for `(F'F, r'')` follows from (ext) for the two.
Identity: `F = id`, identity maps at the sort slots; the invariant is "over directed telescopes the
relation is equality". Unit and associativity laws: those of functions and functors.

### P5. Why contextual models (claim C14): a counterexample by hand

Theory: `𝟚` a finite sort, `X : type`, `c : [u : [p : [x:X]𝟚]𝟚] X`. No admissible sorts. Over the
terminal category its models are sets with a map `2^(2^X) → X` and Mod is a category by P4.
Let 𝒫 be the category with objects pt, K; `End(K) = {1, a}`, `a² = 1`; one morphism `g : K → pt`
(so `g a = g`); pt terminal. Consider models over the bases `1 --F--> 𝒫 --id--> 𝒫` (F picks pt).
For a presheaf Y on 𝒫: `Π(Y, 𝟚)(K) = 2^{Y(K)}` (a predicate q with `q(a, y) = q(1, y·a)`), and
`Π(Y, 𝟚)(pt)` = the a-invariant predicates on `Y(K)` (the value on `Y(pt)` is determined by
restriction). An element `u ∈ ΠΠ(Y)(pt)` has a component `u(id, _)` on invariant predicates and a
component `u(g, _)` on all predicates of `Y(K)`, invariant under the action of a on predicates,
with `u(g, q) = u(id, q)` for invariant q.
 Models. `X = {*}`. `X'(pt) = {x'}`, `X'(K) = {y_0, y_1, y_2}`, `x'|K = y_0`, a swaps y_1, y_2.
 `X''(pt) = {x''_0, x''_1}`, `X''(K) = {z_0, …, z_5}`, `x''_0|K = z_0`, `x''_1|K = z_5`, a swaps
 `z_1, z_2` and `z_3, z_4`. `h(*) = x'`. `k(x') = x''_0`, `k(y_j) = z_j`. `c` is the unique map;
 `c'` is constant `x'` (at K: `y_0`); `c''_K(w) := z_0` if w has a k-related partner in
 `ΠΠ(X')(K)`, `z_5` otherwise; `c''_pt(u) := x''_0` if `u·g` has a k-related partner, `x''_1`
 otherwise. These are natural, and `(F, h)`, `(id, k)` are homomorphisms.
 Failure. Let `u := ev_*` and `u''(id, q) := q(z_0)`, `u''(g, q) := q(z_0) xor [q(z_3) ≠ q(z_4)]`.
 Then u and u'' are related along `(F, kh)`, because that relation only sees the component at id.
 But `u''·g` has no k-related partner w': it would need `w'(1, k^*q) = u''(g, q)` for all q, and
 `k^* 1_{z_3} = k^* 0 = 0` while `u''(g, 1_{z_3}) = 1 ≠ 0 = u''(g, 0)`. So `c''(u'') = x''_1`, while
 `kh(c u) = x''_0`. The composite is not a homomorphism.
So non-contextual models must be excluded as soon as a forward entry binds a backward function
entry. For a theory WITH admissible sorts the same phenomenon is expected over contextual models
whenever 𝒞' has types that are not in the image of F (stages `FI.τ'` not of the form `Ff`); not
written out.

### P6. The term model of a positive theory (claim C8)

T positive; `𝒞_T` the admissible telescopes; `i : 𝒞_T → Syn//Ξ` the inclusion; 𝓠 := Rel(i, よ)
(the right-hand model is `𝐏(𝒞_T)`, where N' is the identity by Yoneda). Recursion on the prefixes
`Ξ_{<k}`: models `m_{<k} ∈ mod_𝓠(Ξ_{<k})` whose first projection is the truncation of the generic model
`δ_Ξ` and whose maps at sort slots are identities. Write `M_{<k}` for the second projection and
`W_k : Syn//Ξ_{<k} → Syn//Ξ` for the weakening, which is `π∘⟦_⟧_{m_{<k}}` by `prop:classifying`.
 Invariant: for a telescope Θ of positive types over `Ξ_{<k}`, both legs of the span `⟦Θ⟧_{m_{<k}}`
 are bijections; so it is the graph of a bijection `ev : (Syn//Ξ)(Γ, W_kΘ) ≅ ⟦Θ⟧_{M_{<k}}(Γ)`.
 Proof, by induction on the generation of positive types, for a witness `ρ : σ ~ θ` at Γ:
  (F1) `A_y[τ]`: by construction at the slot y, the witness in U^R is the identity of the presheaf
     `f ↦ Tm(Δ, A_y[τσf])`; the relation is the diagonal.
  (F2) `Id(l, r)`: `⟦l⟧_M(θ) = l[σ]` and `⟦r⟧_M(θ) = r[σ]` by (F1), so the two conditions coincide.
  (F3) `Π(A, C)`, `A = A_y[τ]`, y ∈ 𝒜: `Γ⁺ := Γ.A[σ]` is an object of `𝒞_T`; `(p, ν, ν, ⋆)` is a
     generic related pair, with `k = ⟨f, a⟩`. On the left `b ↦ app(b)` is bijective. On the right
     `(p, ν)` represents `⟦A⟧_M[θ]` by (F1), so `lem:binding` applies. Conclude by P2 and the
     hypothesis for C at `(ρ·p, ⋆)`.
 Step: the entry `[Φ]C` of Ξ at position k, with first component `c_1` (from δ_Ξ). By `prop:slots`
 in 𝓠 one needs a term of `⟦C⟧` over `⟦Φ⟧_{m_{<k}}` above `c_1`. With `σ_θ := ev⁻¹θ`:
  C = type:      `c_2(Γ, θ) :=` the presheaf `f ↦ Tm(Δ, El(c_1[σ_θ f]))`, witness the identity;
  C = `A_y[τ]`:  `c_2(Γ, θ) := c_1[σ_θ]`;
  C = `Id(l, r)` (elements): `l = r` over `W_kΦ` in `Syn//Ξ`, so `⟦l⟧_M θ = l[σ_θ] = r[σ_θ] = ⟦r⟧_M θ`;
  C = `Id(S, S')` (sorts, slot instances): the two presheaves of terms coincide, the witnesses are
     identities.
 Naturality of `c_2` in Γ: `σ_{θ·g} = σ_θ∘g`. In each case the component is forced.
Result: `M_T ∈ mod_{𝐏(𝒞_T)}(Ξ)` and `m` over `(δ_Ξ, M_T)`; `ev` natural in Γ, and in Θ for all
morphisms of `Syn//Ξ` between telescopes of positive types (because `⟦t⟧_m` is a morphism of 𝓠 over
`(t, ⟦t⟧_{M_T})`). `R_T(Γ, (y, θ)) := Γ.A_y[σ_θ]` makes `(𝒞_T, M_T, R_T)` a model of T; its natural
model is `𝒞_T` up to the bijection ev on types; it is contextual.
No term inversion is used. To apply the construction to a concrete signature one exhibits every
conclusion `B` as an instance `A_y[σ]`, which is what its well-formedness derivation by App does.

### P7. Initiality (claim C9)

Let `(𝒞, M, R)` be a model of T. Existence. For Γ ∈ 𝒞_T, `⟦Γ⟧_M` is represented by an object FΓ with
generic point `γ_Γ`: `F() := pt`, `F(Γ.(y, σ)) := FΓ.(y, ⟦σ⟧_M γ_Γ)`, `γ_{Γ.(y,σ)} := (γ_Γ·p, v)`
(`prop:binding-model`'s representation). For `g : Δ → Γ` let Fg be the morphism with
`γ_Γ·Fg = ⟦g⟧_M(γ_Δ)`. `φ(ev σ) := ⟦σ⟧_M(γ_Γ)`. It is natural in Θ (functoriality of `⟦_⟧_M`) and in
Γ (definition of Fg), and it satisfies (ext). By C7 it is a homomorphism. Uniqueness. For a
homomorphism `(F', φ')`: (ext) gives `φ'(ev id_Γ) = γ'_Γ`, the generic point of `F'Γ`, by induction
on Γ; then `φ'(ev σ) = φ'(⟦σ⟧_{M_T} ev id) = ⟦σ⟧_M(γ'_Γ)`; and F' on objects and morphisms is
determined in the same way. So `(F', φ') = (F, φ)`.

### P8. Generation from Chapter 3 (claim C11)

In `def:interpretation`, `⟦x(t)⟧_ρ := app(v_x)[⟨id, ⟦t⟧^{τ_x}_ρ⟩]` is defined only if every argument
`t_y` is interpretable at the entry of its slot instantiated at the preceding arguments
(`⟦t_y⟧_{ρ, e}` "defined when `⟦u⟧_{ρ.τ}` is defined and is a term of `b°`"), and an equational
premise is interpreted only if the equation holds in the model. Take the model `Syn`. Claim, by
structural induction on raw expressions e over a well-formed Γ, at the generic environment of Γ:
if `⟦e⟧` is defined then e is well typed and `⟦e⟧ = [e]`. For `e = x(t)`: by induction the
arguments are well typed at `Φ_y[t_{<y}]`, and their types are the declared ones because types of
`Syn` are classes modulo judgemental equality (conversion); equational premises hold in `Syn`,
i.e. are derivable; so `Γ ⊢ t : Θ_x`, and App gives `Γ ⊢ x(t) : c_x[t]` with `[x(t)] = ⟦x(t)⟧`.
Since every derivable judgement is interpretable (`prop:typing-relation`), `Γ ⊢ x(t) : C` implies
`Γ ⊢ t : Θ_x` and `Γ ⊢ C ≡ c_x[t]`.

### P9. Voevodsky's form (claim C10)

Raw syntax of T: `𝔼_Ξ(n)` := expressions of kind tm and arity ∅ over the slots of Ξ and n variables
of arity ∅; a relative monad on finite sets (substitution of arity-∅ variables). Raw types
`LM_𝒜(n)` := expressions `y(t)` of kind ty with head y ∈ 𝒜; a module. `Raw(𝔼_Ξ, LM_𝒜)`: contexts are
lists of raw types; this is Voevodsky's C(RR, LM). Judgements of T: `Γ ⊢_T J` iff `Ξ.Γ ⊢ J` in
ToS^ω. They form a typing (the slice of a typing). Its syntax `W/≡` has as types over Γ the classes
of raw types. The map from the types `(y, σ)` of `𝒞_T` to these classes is surjective by P8 and
injective iff the admissible sort slots are injective (`A_y[σ] = A_{y'}[σ']` implies `y = y'`,
`σ = σ'`). Injectivity holds if Ξ has no equations between sorts: run P6 with the universe of
codes `V(Γ) := ∐_y (Syn//Ξ)(Γ, Φ_y)`, decoded to the presheaves of terms, in place of the
Hofmann–Streicher universe; the sort slot y is interpreted by the code `(y, σ)`; the result is a
model of ToS^ω and of Ξ, and equal sorts have equal codes. (Tagging the elements does not work:
empty sorts.) NOT written out.
