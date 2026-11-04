# Plan: §Judgements of the well-formed syntax chapter, via B-systems

Status: proposal, 2026-10-31. It replaces the commented-out *Rules* subsection and the
current *Judgement forms* subsection of `chapters/well-formed-syntax.tex`.

Style of the write-up: terse. Only definitions and propositions, with as much commentary as
is needed to follow the development. Motivation will be reworked later. No `\cref` to labels
that do not exist yet. The comments marked **Why** in this file justify the structure. They are
not text for the chapter.

---

## 0. The idea in one paragraph

The term C-system `Ctx` is **defined** as the least regular subquotient of the raw syntax
C-system `Ctxr = C(𝔼, Ent)` to which the operations of a GAT S, *realised* on raw syntax by a
raw realization ρ, descend as an S-structure. Here S is the GAT of models of ToS^ω, and
"least" refers to inclusion of judgement sets.

In terms of judgements this splits in two.
1. *Being a regular subquotient.* By Voevodsky (Module Props. 4.1, 6.2, 6.11), a regular
   subquotient of C(T, M) is the same as four sets of judgements closed under his
   *structural rules*. This is the condition of being a regular subquotient at all, not an
   extra condition. On its own it is trivial: the least such set contains only the empty
   context.
2. *ρ descends as an S-structure.* This is closure under rules read off mechanically from S
   and ρ:
   - formation: the C-subsystem is closed under ρ;
   - congruence: ρ respects the congruence;
   - equations: the quotient satisfies the equations of S.

   All of the content is here.

So `Ctx` is given by the least set of judgements closed under both kinds of rules. The
syntax-directed rules of `Typing/Rules.lean` (the old figures) then become a **theorem**: a
presentation of the same judgements, proved later in the chapter from the metatheory.

### Design decisions (agreed 2026-10-31)

**D1. The judgement forms are Martin-Löf's four, read as the B-sets of `Ctxr`.**
The forms are ⊢ Γ, Γ ⊢ e : E, Γ ⊢ E ≡ E′ and Γ ⊢ e ≡ e′ : E. The seven syntax-directed
forms move to the later presentation section.

- *Why.* The definition of the term C-system is phrased on Voevodsky's B-sets Ob and Õb
  (Subsystems Props. 4.3, 5.4), together with their equality counterparts. The judgement
  forms that *define* `Ctx` must therefore be those four sets. They are exactly Voevodsky's
  "sentences of the four Martin-Löf kinds", B, B̃, B_eq and B̃_eq (RDP 2015 notes, slides
  15–16), and the four sets (C, C̃, C_eq, C̃_eq) of the Module paper (§§4, 6).
- The seven forms are artefacts of one particular *presentation*:
  - judgements on telescopes are primitive there because `ap` takes a whole telescope of
    arguments;
  - boundaries have their own judgements because expressions synthesise their boundary.

  Putting them next to the syntax-directed rules separates what is definitional from what is
  presentational.
- Telescope judgements (Γ ⊢ Θ, Γ ⊢ t : Θ, Γ ⊢ t ≡ t′ : Θ) become derived forms, as in
  MLTT.

**D2. The development is general: any raw syntax C-system C(T, M), any GAT S over
C-systems, any raw realization ρ. ToS^ω is the instance.**

- *Why.*
  - The structural rules and the subquotient construction depend only on (T, M).
    `prop:sorted-c-system` is already stated for arbitrary T and M.
  - The construction has the property we need (a least closed subquotient exists) exactly
    because the C-system has the form C(T, M). In a general C-system, conditions (3) and (4)
    of Subsystems Prop. 5.4 are existential, so intersections of regular subquotients need
    not be regular. In C(T, M) the witnesses are explicit.
  - The general definition C_{S,ρ} is also what the Initiality chapter needs to state the
    initiality conjecture precisely, for a triple (S, C(T, M), ρ). Stating it once here avoids
    duplication.
  - The instance for ToS^ω then costs one table and one proposition.

**D3. The definition stays canonical.** There is no rule that is not read off from S and ρ.
Lean's convention of accepting any raw expression as the filler of an equation slot appears
only in the presentation theorem, as a *saturation*.

- *Why.*
  - The point of the B-system route is that the rules are not chosen. A saturation rule
    would be the only rule not coming from S.
  - The quotient C-systems are isomorphic anyway. The isomorphism follows from initiality and
    the uniqueness proposition (J.3, item 15).

---

## 1. Changes to the existing text

| lines | current content | action |
|---|---|---|
| 344–346 | `\section{Judgements}` + opening paragraph | keep; adjust its last clause later |
| 348–377 | *Judgement forms*: paragraph 350–353, `tab:judgement-forms`, MLTT paragraph 377 | replace with J.1; move the paragraph, table and MLTT paragraph to the later section *Syntax-directed presentation* |
| 379–529 | commented-out *Rules*: notation paragraph, `fig:rules-wf`, `fig:rules-eq`, commentary 501–508, `deceq`, `rem:adams-judgements` | delete here; in *Syntax-directed presentation*, the figures, commentary and `deceq` are replaced by `fig:rules` and its premise table, and `rem:adams-judgements` moves there, revised since it refers to `congr` |
| 12 | chapter intro: "…which we prove Ctx to be an initial model of" | adjust later: `Ctx` is now an S-structure by construction; initiality is in its own chapter |

---

## 2. New §Judgements: overview

```
J.1  Judgements on a raw syntax C-system C(T, M)        [general; Voevodsky]
       raw judgements → telescope judgements → structural operations
       → structural rules → regular subquotient → intersections
J.2  GATs over C-systems                                [general; Cartmell, ALN, Voevodsky]
       GAT over C-systems → S-structure / C(S)-system → HrS
J.3  Raw realizations and term C-systems                [general; new]
       raw realization → S-closed → least → C_{S,ρ} → S-structure → uniqueness
J.4  The term C-system of ToS^ω                         [instance]
       ρ for HrS on Ctxr → which equations hold raw → the rules of ToS^ω → Ctx
```

**Why this order.**
- J.1 comes first because the structural rules do not depend on S. J.1 is also the only place
  where the general theory of C-systems (Subsystems paper) enters.
- J.2 precedes J.3 because a raw realization is a realization *of* S.
- HrS is introduced in J.2 as the example of a GAT over C-systems, so that J.4 only has to
  provide ρ.

---

## 3. J.1 Judgements on a raw syntax C-system

Fix a relative monad T on J_S and a T-module M : Kl(T) → Set^S, as in `def:sorted-c-system`.
Write X = (Γ, c) for objects of C(T, M), and X ⋈ [m] for the extension of X by a decoration
m ∈ M(Γ)_s. A *telescope* d = (m₁, …, m_k) over X is a sequence of decorations with
m_j ∈ M(Γ ⋈ [s₁,…,s_{j−1}])_{s_j}. The objects whose k-fold `ft` is X are exactly the X ⋈ d.

### 1. `def:raw-judgements`

The four sets of raw judgements of C(T, M):

| set | elements | notation |
|---|---|---|
| Ob | objects X | ⊢ X |
| Õb | triples (X, m, t), with m ∈ M(Γ)_s, t ∈ T(Γ)_s | X ⊢ t : m |
| Ob_eq | triples (X, m, m′), with m, m′ ∈ M(Γ)_s of the **same** sort s | X ⊢ m ≡ m′ |
| Õb_eq | quadruples (X, m, t, t′), with t, t′ ∈ T(Γ)_s | X ⊢ t ≡ t′ : m |

Abbreviation: X ⊢ m for ⊢ X ⋈ [m].

Commentary (one sentence each):
- By the remark after `prop:sorted-c-system`, the sections of p_{X ⋈ [m]} are the elements of
  T(Γ)_s, so Õb is Voevodsky's set of sections.
- For `Ctxr`, the four forms read ⊢ Γ, Γ ⊢ e : E, Γ ⊢ E ≡ E′ and Γ ⊢ e ≡ e′ : E, where E is
  an entry of arity α and e ∈ Expr(Γ^↓ ⋈ α).

**Why "same sort".** A raw term of m is then also a raw term of every m′ that m can be equal
to. This is what makes the witnesses of regularity explicit (item 5). Lean has the
corresponding fact as `Rel.arity`.

### 2. `def:telescope-judgements`

For a telescope d = (m₁, …, m_k) over X:
- X ⊢ d := ⊢ X ⋈ d;
- X ⊢ () : () holds, and X ⊢ (t₁, t) : (m₁, d′) := X ⊢ t₁ : m₁ and X ⊢ t : d′[t₁];
- X ⊢ (t₁, t) ≡ (t₁′, t′) : (m₁, d′) := X ⊢ t₁ ≡ t₁′ : m₁ and X ⊢ t ≡ t′ : d′[t₁].

Commentary:
- For `Ctxr`, a telescope over Γ is a decorated arity Θ : Dec(Γ^↓, Θ^↓), and a sequence of
  terms is a substitution t : Θ^↓ ⇝ Γ^↓. So these are the familiar Γ ⊢ Θ, Γ ⊢ t : Θ and
  Γ ⊢ t ≡ t′ : Θ.
- The equality is left-leaning (the tail is compared at d′[t₁]) because an equality judgement
  is made at a single type.

**Why here.** The structural rules (item 4) weaken and substitute in telescopes, the example
in J.4 uses Γ ⊢ t : Θ, and the presentation theorem translates the seven forms into these.
Left-leaning was a presentational choice in the old figures. Here it is forced, which is
worth one clause.

### 3. `def:structural-operations` and `lem:structural-operations`

For an extension X ⋈ [m] with m of sort s:
- **Weakening.** d↑ := ((inl ⋈ [s₁,…,s_{j−1}])^M(d_j))_j for a telescope d over X. Likewise
  t↑ via the T-action, with inl : Γ → Γ ⋈ [s] in Kl(T).
- **Substitution.** For X ⊢ u : m and a telescope d over X ⋈ [m]:
  d[u] := ((⟨id_Γ, u⟩ ⋈ [s₁,…,s_{j−1}])^M(d_j))_j. Likewise t[u], with
  ⟨id_Γ, u⟩ : Γ ⋈ [s] → Γ the copairing in Kl(T).
- **Generic term.** v_m := η(z), where z is the last variable of Γ ⋈ [s]. Then
  X ⋈ [m] ⊢ v_m : m↑.

The notation f ⋈ Φ is the one introduced in the coproduct remark after the definition of J_S.

`lem:structural-operations`: under the identification of item 1, these are Voevodsky's
B-system operations T, T̃, S, S̃ and δ of C(T, M) (Relative paper, Def. 5.11; for S = 1 they
are the formulas of Thm. 6.10). Proof: unfold `def:sorted-c-system`, using
T(X, Y) = p_X^*(Y), S(r, Y) = r^*(Y) and δ(X) = s_{id_X}.

For `Ctxr`:
- weakening is renaming;
- substitution is the Kleisli action of 𝔼, i.e. hereditary substitution, at the appropriate
  depth (`def:action-decorations`, `lem:depth-derived`);
- v_E is the η-expansion of the last slot.

**Why.** The structural rules are stated in terms of these operations. Making them explicit
for C(T, M) is the step that turns Voevodsky's abstract closure conditions into inference
rules on raw syntax. Voevodsky does the same in the Module paper (§4, before Prop. 4.1).

### 4. `fig:structural-rules` and `def:structurally-closed`

This is Voevodsky's Module Prop. 4.1 (1)–(6) and Prop. 6.2 (2)–(7), transcribed. Here m, n
are decorations, d a telescope, t, u terms.

Contexts and terms (Module Prop. 4.1):
```
(1)  ⊢ pt
(2)  ⊢ X⋈[m]                              ⟹ ⊢ X
(3)  X ⊢ t : m                             ⟹ ⊢ X⋈[m]
(4)  ⊢ X⋈[m],  X⋈d ⊢ t : n                ⟹ X⋈[m]⋈d↑ ⊢ t↑ : n↑                (weakening)
(5)  X ⊢ u : m,  X⋈[m]⋈d ⊢ t : n          ⟹ X⋈d[u] ⊢ t[u] : n[u]              (substitution)
(6)  ⊢ X⋈[m]                              ⟹ X⋈[m] ⊢ v_m : m↑                  (variable)
```
Equality (Module Prop. 6.2):
```
(2a–d)  X ⊢ m ≡ m′ ⟹ X ⊢ m;   X ⊢ m ⟹ X ⊢ m ≡ m;   symmetry;   transitivity
(3a–d)  the same for X ⊢ t ≡ t′ : m
(4a)    X ⊢ m ≡ m′,  X⋈[m]⋈d ⊢ n ≡ n′          ⟹ X⋈[m′]⋈d ⊢ n ≡ n′          (context conversion)
(4b)    X ⊢ m ≡ m′,  X⋈[m]⋈d ⊢ t ≡ t′ : n      ⟹ X⋈[m′]⋈d ⊢ t ≡ t′ : n      (context conversion)
(4c)    X ⊢ n ≡ n′,  X ⊢ t ≡ t′ : n            ⟹ X ⊢ t ≡ t′ : n′              (type conversion)
(5a,b)  weakening of type and term equalities
(6a,b)  substitution of a term into type and term equalities
(7a)    X⋈[m]⋈d ⊢ n,  X ⊢ u ≡ u′ : m           ⟹ X⋈d[u] ⊢ n[u] ≡ n[u′]
(7b)    X⋈[m]⋈d ⊢ t : n,  X ⊢ u ≡ u′ : m       ⟹ X⋈d[u] ⊢ t[u] ≡ t[u′] : n[u]
```
`def:structurally-closed`: a quadruple J = (J_Ob, J_Õb, J_Ob,eq, J_Õb,eq) of subsets of the
four sets of item 1 is *structurally closed* if it is closed under these rules.

**Why Voevodsky's list, and not "closed under pt, ft, ∂, T, T̃, S, S̃, δ" directly.**
- It reads as inference rules.
- It is minimal. Voevodsky, Module Rem. 4.2: "they are precisely the ones which are necessary
  and sufficient for a given collection of contexts and judgements to define a C-system."
  This is the strongest available justification for calling them *the* structural rules.
- Rule (5) uses hereditary substitution in our instance. This is where the computation of
  the canonical syntax lives.

**Why the equality judgements are relative to one context and one type.** This is
Voevodsky's choice (C_eq, C̃_eq). The regular congruence on whole contexts and on sections
is then *defined* from them (item 5, Module Def. 6.1).

### 5. `prop:structural-subquotient`

Let J be structurally closed. Then:
1. (J_Ob, J_Õb) is a C-subsystem of C(T, M);
2. the relations ∼ on J_Ob and ≃ on J_Õb defined from J_Ob,eq and J_Õb,eq as in Module
   Def. 6.1 form a regular congruence on it. Contexts are equal if their last types are equal
   and their `ft`s are equal; terms are equal if their contexts and types are equal and the
   term equality holds.

Hence C(T, M)/J is a C-system, and the quotient map from the C-subsystem is a homomorphism
(Subsystems Lemma 5.2).

*Proof.* Voevodsky's for S = 1: Module Props. 4.1, 6.2 and 6.11, via Subsystems Prop. 4.3,
Lemma 5.2 and Prop. 5.4. The proofs use only `lem:structural-operations` and the fact that a
term of m depends only on the sort of m. That fact gives the explicit witnesses
X_F := F ⋈ [m] and s′ := (X′, t) for conditions (3) and (4) of Subsystems Prop. 5.4; these
are Module Prop. 6.11 (2), (3).

Conversely, every C-subsystem with a regular congruence satisfying Module Prop. 6.11 (2), (3)
arises from exactly one structurally closed J. Those conditions say that raw types and terms
can be moved along ∼. These are the regular subquotients meant whenever "least regular
subquotient" is said, ordered by inclusion of their quadruples.

⚑ **To check.** Go through Voevodsky's proofs in the sorted setting line by line. I expect no
surprises, but have not done it.

**Why.** This is the bridge between the rules and C-systems. It is the only proposition in
the chapter whose proof is "Voevodsky's, sorted", and it is what justifies the word
"structural".

### 6. `lem:closed-intersections`

Every rule of `fig:structural-rules` is a Horn clause (premises ⟹ conclusion, no
existentials). So structurally closed quadruples are closed under arbitrary componentwise
intersection, and form a complete lattice.

**Why.** The rest of J.3 depends on this one line: it gives the *least* closed quadruple.
It is also the place to say, in one sentence, why we work with C(T, M) rather than with an
arbitrary C-system (see D2).

---

## 4. J.2 GATs over C-systems

### 7. `def:gat-over-c-systems`

Let 𝕋_CwF be the GAT of categories with families. A *GAT over C-systems* is a GAT S
extending 𝕋_CwF (Cartmell) such that:
- every further symbol has the form o : (Γ : Ctx)(x₁ : A₁)⋯(x_k : A_k) → B;
- each Aᵢ and B is Ty(Γ.Δ) or Tm(Γ.Δ, C), for telescopes Δ and types C built from the
  preceding inputs;
- the equations include, for every further symbol, its stability equation
  o(x⃗)[f] = o(x⃗[f]).

**Why a GAT, and not Voevodsky-style operations on B-sets directly.**
- A GAT gives one uniform language for the typing of operations *and* for equations. The
  equations include conditional ones such as reflection: an equation S = S′ in the context
  (S, S′, t : Tm(IdSort S S′)).
- Item 11 needs exactly that language, to generate rules mechanically.
- The B-set reading is recovered in item 8.

**Why outputs over extensions are allowed.** HrS's `unlam` has its output in Tm(Γ.a, c). In
B-set terms this is harmless: Voevodsky's λ is a map Õb₂(Γ) → Õb₁(Γ), and its inverse is
`unlam`.

### 8. `def:s-structure`

- An *S-structure* on a C-system CC is a model of S whose 𝕋_CwF-part is the CwF of CC.
  Types over Γ are Ob₁(Γ), and terms are sections (ALN Props. 41, 45).
- Concretely, each further symbol becomes a family of maps between subsets of iterated fibre
  products of Ob_k(Γ) and Õb_k(Γ), natural in Γ under f*.
- A *C(S)-system* is a C-system with an S-structure. A homomorphism of C(S)-systems is a
  C-system homomorphism that commutes with the further symbols.

Remark (one sentence): a C(S)-system is the same as a contextual model of S, with strict
morphisms (ALN Props. 41, 45, 48).

**Why.** This is precisely Voevodsky's "C(S)-system" from the RDP formulation of the
conjecture, with Opr(S) given by a GAT instead of being derived from rules.

### 9. `def:hrs` (the GAT of models of ToS^ω)

| symbol | typing |
|---|---|
| U | (Γ) → Ty(Γ) |
| El | (S : Tm(Γ, U)) → Ty(Γ) |
| Bind | (a : Ty(Γ)) (c : Ty(Γ.a)) → Ty(Γ) |
| lam | (a)(c)(e : Tm(Γ.a, c)) → Tm(Γ, Bind a c) |
| unlam | (a)(c)(t : Tm(Γ, Bind a c)) → Tm(Γ.a, c) |
| IdSort | (S S′ : Tm(Γ, U)) → Ty(Γ) |
| reflSort | (S : Tm(Γ, U)) → Tm(Γ, IdSort S S) |
| IdElement | (S : Tm(Γ, U)) (l r : Tm(Γ, El S)) → Ty(Γ) |
| reflElement | (S)(l : Tm(Γ, El S)) → Tm(Γ, IdElement l l) |

Equations:
- stability of every symbol;
- lam ∘ unlam = id and unlam ∘ lam = id;
- irrelevance: t = t′ for t, t′ : Tm(IdSort S S′), and likewise for IdElement;
- reflection: S = S′ in the context (S, S′, t : Tm(IdSort S S′)), and l = r likewise.

Remarks:
- (Bind, lam) is a (Π,λ)-structure: Voevodsky, arXiv:1503.07072, Defs. 2.2–2.3. Bind_Γ is a
  map Ob₂(Γ) → Ob₁(Γ), and lam_Γ is a bijection Õb₂(Γ) → Õb₁(Γ) over it.
- Lean: `HrS.Structure` (`HrS/Structure.lean`), which does not require contextuality. Lean
  omits the stability of unlam, reflSort and reflElement; these are derivable (from
  `lam_subst` and bijectivity, and from irrelevance).

**Why here, and not in the Initiality chapter.** J.4 needs HrS to say what is realised. As
an example, it also makes the abstract format of item 7 concrete. The Initiality chapter
then starts from C(HrS)-systems as already defined.

---

## 5. J.3 Raw realizations and term C-systems

### 10. `def:raw-realization`

Assume that the sorts of all symbols and equations of S are well formed using only the
equations of 𝕋_CwF and the stability equations.
- A *raw realization* ρ of S in C(T, M) interprets the further symbols of S in the CwF of
  C(T, M), so that the stability equations hold.
- E_ρ denotes the set of equations of S satisfied by ρ.

Commentary (one sentence): by item 1, ρ consists of operations on decorations and raw terms
that commute with the T-actions.

**Why the assumption.** ρ must be typed as in S even though it may violate equations of S.
The assumption guarantees that the typing never depends on a violated equation. HrS
satisfies it: `El_subst` is typed using `U_subst`, `IdElement_subst` using `El_subst`, and
`lam_subst` using `Bind_subst`, all of which are stability equations.

### 11. `def:s-closed`

A structurally closed J is *S-closed* (with respect to ρ) if it is closed under the following
rule schemes, generated from S and ρ:
- **Formation**, one rule per symbol o : (Γ)(x⃗ : A⃗) → B.
  - Premises: ⊢ X, and for each input xᵢ, either X⋈Δᵢ ⊢ xᵢ (if Aᵢ = Ty(Γ.Δᵢ)) or
    X⋈Δᵢ ⊢ xᵢ : Cᵢ (if Aᵢ = Tm(Γ.Δᵢ, Cᵢ)).
  - Conclusion: X⋈Δ ⊢ ρ(o)(x⃗), with ": ρ(C)" if B is a sort of terms.
  - Δᵢ, Cᵢ and Δ are evaluated through ρ.
- **Congruence**, one rule per symbol: the same, with ≡ in premises and conclusion. Δᵢ and
  Cᵢ are evaluated at the left-hand inputs.
- **Equation**, one rule per equation l = r of S: the formation premises of its context, and
  the conclusion X⋈Δ ⊢ ρ(l) ≡ ρ(r), with ": ρ(C)" for term equations.

Commentary (one sentence): the equations in E_ρ yield instances of reflexivity, hence
redundant rules.

**Why all equations, not only the imposed ones.** The scheme then needs nothing but S and ρ.
Dropping the redundant rules is an observation, not part of the definition.

**Why the schemes have this shape.**
- The formation scheme is the GAT's own introduction rule for o, with the context Γ made
  explicit and o replaced by ρ(o).
- The congruence scheme is what makes ρ descend to the quotient.
- The equation scheme is what makes the equations of S hold there.

### 12. `lem:least-s-closed`

All schemes are Horn, so by `lem:closed-intersections` there is a least S-closed quadruple
J_{S,ρ}. Its elements are exactly the judgements derivable by `fig:structural-rules` and the
schemes of item 11.

### 13. `def:term-c-system`

C_{S,ρ} := C(T, M)/J_{S,ρ}, which is a C-system by `prop:structural-subquotient`.

**Why the name.** It matches Voevodsky's "term C-system" (Relative paper, introduction) and
his CC(Στ, Σο, S) (RDP notes, slide 16). The difference is that the rules are generated by
(S, ρ), not given.

### 14. `prop:term-c-system-structure`

C_{S,ρ} carries a unique S-structure for which the quotient map from the C-subsystem J_{S,ρ}
preserves ρ.

*Proof sketch.*
1. The formation rules close the C-subsystem under ρ.
2. Inputs that are equal in the quotient can be represented by inputs typed on the nose,
   using the explicit conversion witnesses of item 5. The congruence rules then make the
   operations well defined on classes.
3. Stability holds upstairs, so it descends.
4. The equation rules give the equations of S in the quotient.

### 15. `prop:term-c-system-generated`

Any two homomorphisms of C(S)-systems C_{S,ρ} → D are equal.

*Proof.* The judgements of J_{S,ρ} on whose classes the two homomorphisms agree form an
S-closed quadruple. An equality judgement is included when both sides are included. Conclude
by leastness.

The Lean analogue for HrS is `HrS.Morphism.agree_closed` (`HrS/Closed.lean`) together with
`Ctx.generated` (`Ctx/Generation.lean`), stated for the syntax-directed model.

**Why it belongs here and not in the Initiality chapter.** It is formal. It is the "half" of
initiality that the B-system route gives for free, and it is used again in the presentation
theorem (§7) to identify `Ctx` with Lean's model.

---

## 6. J.4 The term C-system of ToS^ω

### 16. `def:raw-realization-hrs`

| symbol | ρ on `Ctxr` |
|---|---|
| U_Γ | []sort |
| El(S) | []of(S) |
| Bind(E, [Θ]β) | [E, Θ]β, using Dec(Ξ, [α] ⋈ γ) = Ent(Ξ, α) × Dec(Ξ ⋈ [α], γ) |
| lam, unlam | the identity of Expr(Γ^↓ ⋈ [α] ⋈ γ) = Expr(Γ^↓ ⋈ ([α] ⋈ γ)) |
| IdSort(S, S′) | []eq(S, S′) |
| reflSort(S) | S |
| IdElement_S(l, r) | []eq(l, r) |
| reflElement_S(l) | l |

The Lean counterparts are on the subquotient, not on raw syntax: `Ob.Entry.sort`,
`Ob.Entry.of`, `Ob.Entry.id`, `Ob.Fill.idRefl`, and `mk_cons` (Bind).

### 17. `prop:raw-realization-hrs`

ρ is a raw realization of HrS in `Ctxr`, and E_ρ consists of all equations of HrS except
irrelevance (×2) and reflection (×2).

*Proof sketch.*
- Stability follows from `def:action-decorations` and `lem:depth-derived`.
- lam/unlam follows from `rem:concatenation` and the isomorphism of
  `prop:decoration-modules`.
- Irrelevance and reflection visibly fail on raw syntax.

**Why this matters.** This is the precise content of "canonical syntax": every equation of
the framework except the two about equality types already holds on raw syntax, so only
those two are imposed by the quotient. One sentence in the chapter can say this; it ties
back to the Canonical LF remark in the intro.

Also worth one sentence: IdSort and IdElement are realised by the same raw boundary `eq`,
and IdElement forgets S. The premises of the rules tell the two apart, and synthesis
recovers S.

### 18. `fig:hrs-rules`

The output of item 11 for (HrS, ρ), omitting the redundant equation rules and premises
that are derivable from the others:
```
Formation
  U            ⊢ Γ                                               ⟹ Γ ⊢ []sort
  El           Γ ⊢ S : []sort                                    ⟹ Γ ⊢ []of(S)
  Bind         Γ⋈[E] ⊢ [Θ]β                                      ⟹ Γ ⊢ [E,Θ]β
  lam          Γ⋈[E] ⊢ e : [Θ]β                                  ⟹ Γ ⊢ e : [E,Θ]β
  unlam        Γ⋈[E] ⊢ [Θ]β,  Γ ⊢ e : [E,Θ]β                     ⟹ Γ⋈[E] ⊢ e : [Θ]β
  IdSort       Γ ⊢ S : []sort,  Γ ⊢ S′ : []sort                  ⟹ Γ ⊢ []eq(S,S′)
  reflSort     Γ ⊢ S : []sort                                    ⟹ Γ ⊢ S : []eq(S,S)
  IdElement    Γ ⊢ S : []sort,  Γ ⊢ l : []of(S),  Γ ⊢ r : []of(S) ⟹ Γ ⊢ []eq(l,r)
  reflElement  Γ ⊢ S : []sort,  Γ ⊢ l : []of(S)                  ⟹ Γ ⊢ l : []eq(l,l)
Congruence (one per symbol), e.g.
  El           Γ ⊢ S ≡ S′ : []sort                               ⟹ Γ ⊢ []of(S) ≡ []of(S′)
  Bind         Γ ⊢ E ≡ E′,  Γ⋈[E] ⊢ [Θ]β ≡ [Θ′]β′                ⟹ Γ ⊢ [E,Θ]β ≡ [E′,Θ′]β′
  lam          Γ⋈[E] ⊢ e ≡ e′ : [Θ]β                             ⟹ Γ ⊢ e ≡ e′ : [E,Θ]β
  …
Reflection
  Γ ⊢ S : []sort,  Γ ⊢ S′ : []sort,  Γ ⊢ t : []eq(S,S′)               ⟹ Γ ⊢ S ≡ S′ : []sort
  Γ ⊢ S : []sort,  Γ ⊢ l : []of(S),  Γ ⊢ r : []of(S),  Γ ⊢ t : []eq(l,r) ⟹ Γ ⊢ l ≡ r : []of(S)
Irrelevance
  (premises as above),  Γ ⊢ t : []eq(S,S′),  Γ ⊢ t′ : []eq(S,S′)    ⟹ Γ ⊢ t ≡ t′ : []eq(S,S′)
  (premises as above),  Γ ⊢ t : []eq(l,r),   Γ ⊢ t′ : []eq(l,r)     ⟹ Γ ⊢ t ≡ t′ : []eq(l,r)
```
Together with `fig:structural-rules`, this *is* the definition of the judgements of ToS^ω.

**Why some premises stay.**
- `unlam` keeps Γ⋈[E] ⊢ [Θ]β, and IdElement and reflElement keep Γ ⊢ S : []sort. These
  are not derivable from the other premises without an inversion principle for Bind and El,
  and there is no such rule.
- Inversion is a theorem about the least set, part of the presentation theorem, not a rule.

**Why list the congruence rules only by example.** They are generated by a uniform scheme,
and listing all nine adds no information. If the figure should be complete, list them; it is
a matter of taste.

### 19. `def:ctx` and corollary

- `Ctx := C_{HrS,ρ}`.
- Corollary, of items 14 and 15: `Ctx` is a C(HrS)-system, and any two homomorphisms of
  C(HrS)-systems out of `Ctx` are equal.

### 20. Example (optional, but recommended)

Derive Γ ⊢ x(t) : []β[t] from x : Γ ∋ [Θ]β and Γ ⊢ t : Θ, with β not an equation:
1. the variable rule (6) and weakening (4) give Γ ⊢ η_x : [Θ]β;
2. unlam, which is the identity on raw syntax, gives Γ⋈Θ ⊢ η_x : []β;
3. substitution (5), iterated along t, gives Γ ⊢ t ⋆ η_x : []β[t];
4. finally t ⋆ η_x = x(t), as in `act_copair_eta` (`Ctx/Generation.lean`).

**Why.** None of the rules mentions the raw constructor x(t). Without one worked
derivation, the reader cannot see how the syntax of ToS^ω arises from the B-system
definition. The same computation with β = eq(l, r) followed by reflection gives the old
`hyp` rule; that can be a single sentence.

---

## 7. Later sections of the chapter (outline only)

### Syntax-directed presentation

This section presents the rules of `Typing/Rules.lean`, reorganised so that every rule and
every premise follows from six principles. The reorganised system derives exactly Lean's
judgements, by unfolding definitions, so the formalized metatheory and the initiality proof
apply unchanged. Its judgement set is J_SD.

Changes to the existing text:
- moved here: the paragraph on judgement forms (350–353), `tab:judgement-forms`, the MLTT
  paragraph (377), and `rem:adams-judgements` (revised);
- replaced by the figure and the premise table below: `fig:rules-wf`, `fig:rules-eq`, the
  commentary (501–508) and `deceq`.

**Principles.**
- **P1. Bidirectionality.** Expressions synthesise their boundary: Γ ⊢ e ⇒ ∂_Γ(e). Every
  other position checks against an entry: Γ ⊢ u : E. Conversion happens in exactly one place,
  where a synthesised boundary meets a declared one.
- **P2. Lists are free.** Telescopes and substitutions are lists of entries and of fillers.
  Their judgements are componentwise, with the tail instantiated by the left component.
  Left-leaning is forced because equality is a judgement at a single type (Voevodsky).
- **P3. Hypotheses are used by instantiation.** A slot x : Γ ∋ [Θ]β is used by giving
  Γ ⊢ t : Θ. If β is not an equation, the use gives the expression x(t) (`ap`). If
  β = eq(l, r), it gives the equality l[t] ≡ r[t] (`hyp`). These are the two cases of one
  rule, with the same premise.
- **P4. Equality is a congruence.** It is an equivalence, compatible with substitution of
  equals (`congr`). `congr` is Voevodsky's functionality rule, (6b) and (7b) of
  `fig:structural-rules`, kept primitive.
- **P5. Two invariants.** A premise appears exactly when one of these needs it.
  - **R1.** Equal expressions are well formed, over any raw Γ.
  - **R2.** Over a well-formed Γ, equal expressions synthesise equal boundaries.

  Together they are the syntax-directed form of "an equality judgement presupposes
  membership, at a single type" (Module Prop. 6.2 (2a), (3a)).
- **P6. Equation slots carry no data.** Checking u against [Θ]eq(l, r) means
  Γ⋈Θ ⊢ l ≡ r, for any u. Equality of substitutions skips equation slots. This is the
  syntactic reading of irrelevance and reflection.

**Judgement forms.** All are made over a raw context Γ.

| form | reading | Lean |
|---|---|---|
| Γ ⊢ e ⇒ β | e is well formed, and β = ∂_Γ(e) | `Wf_e` |
| Γ ⊢ e ≡ e′ | equality of expressions | `Eq_e` |
| Γ ⊢ u : E | u checks against the entry E | `Wf_s` at a one-entry telescope |
| Γ ⊢ t : Θ | checking, listwise | `Wf_s` |
| Γ ⊢ β bd, Γ ⊢ E, Γ ⊢ Θ | formation | `Wf_bd`, `Wf_t` |
| Γ ⊢ β ≡ β′, Γ ⊢ t ≡ t′ : Θ, Γ ⊢ Θ ≡ Θ′ | defined componentwise | `Eq_bd`; `Wf_s σ ∧ Wf_s θ ∧ Eq_s σ θ` (the premises of `congr`); `Eq_t` |

Γ ⊢ u : E has the same form as the term judgement of J.1 (item 1). The comparison below
relates the two.

Here Γ ⊢ t ≡ t′ : Θ includes the well-formedness of both sides, unlike Lean's `Eq_s`. Its
only use is as a premise of `congr`, where Lean bundles the same three facts.

**`fig:rules`.**
```text
Use of a slot           x : Γ ∋ [Θ]β,  Γ ⊢ t : Θ
  (ap)    β not an equation                              ⟹  Γ ⊢ x(t) ⇒ β[t]
  (hyp)   β = eq(l,r),  Γ⋈Θ ⊢ l,  Γ⋈Θ ⊢ r                ⟹  Γ ⊢ l[t] ≡ r[t]

Checking against an entry (one clause per boundary kind), then lists
  Γ⋈Θ ⊢ u ⇒ β′,  Γ⋈Θ ⊢ β′ ≡ β       (β not an equation)  ⟹  Γ ⊢ u : [Θ]β
  Γ⋈Θ ⊢ l ≡ r                                            ⟹  Γ ⊢ u : [Θ]eq(l,r)     (any u)
  Γ ⊢ () : ()          Γ ⊢ u : E,  Γ ⊢ t : Θ[u]          ⟹  Γ ⊢ (u,t) : (E,Θ)

Formation
  Γ ⊢ sort bd          Γ ⊢ S : []sort  ⟹  Γ ⊢ of(S) bd
  Γ ⊢ l ⇒ β,  Γ ⊢ r ⇒ β′,  Γ ⊢ β ≡ β′                    ⟹  Γ ⊢ eq(l,r) bd
  Γ ⊢ Θ,  Γ⋈Θ ⊢ β bd   ⟹  Γ ⊢ [Θ]β        Γ ⊢ ()        Γ ⊢ E,  Γ⋈[E] ⊢ Θ  ⟹  Γ ⊢ (E,Θ)

Equality
  Γ ⊢ e ⇒ β  ⟹  Γ ⊢ e ≡ e          symmetry          transitivity
  (congr)  Γ ⊢ Θ,  Γ ⊢ t ≡ t′ : Θ,  Γ⋈Θ ⊢ e ≡ e′          ⟹  Γ ⊢ e[t] ≡ e′[t′]

Defined componentwise
  Γ ⊢ t ≡ t′ : Θ  :=  Γ ⊢ t : Θ,  Γ ⊢ t′ : Θ,  and t_i ≡ t′_i at every non-equation slot
                      (each over its binding instantiated by t)
  Γ ⊢ β ≡ β′      :=  sort ≡ sort;   of S ≡ of S′ iff S ≡ S′;   eq(l,r) ≡ eq(l′,r′) iff l ≡ l′, r ≡ r′
  Γ ⊢ Θ ≡ Θ′      :=  entry by entry
```

**Where each premise comes from.**

| premise | reason |
|---|---|
| `ap`: Γ ⊢ t : Θ; β not an equation | P3 |
| `hyp`: Γ⋈Θ ⊢ l, Γ⋈Θ ⊢ r | R1: Γ is raw, so the declared sides must be checked (used in `Eq_e.wf_left`/`wf_right`) |
| reflexivity: Γ ⊢ e | R1 |
| `congr`: well-formedness of t and t′ | R1; bundled into t ≡ t′ : Θ |
| `congr`: Γ ⊢ Θ | R2: Γ⋈Θ must be well formed for its boundaries to compare (used in `Eq_e.boundaryOf`, `SubstitutionLemma.lean:511`) |
| `congr`: no premises for e, e′ | already implied by e ≡ e′, through R1 |
| checking: β′ ≡ β | P1, the single conversion point |
| formation of `of(S)`: S checks against []sort | P1: the argument of `of` sits in a position with declared boundary `sort` |
| formation of `eq(l,r)`: both sides synthesise, then compare | P1: an equation has no expected boundary |
| left-leaning tails | P2 |
| arbitrary filler at equation slots | P6 |

**Relation to `Rules.lean`.** It is a matter of unfolding:
- `Wf_s` is the listwise form of checking;
- the premises `hσ`, `hθ` and `agree` of `congr` are together Γ ⊢ t ≡ t′ : Θ;
- `Eq_t` is the componentwise definition.

So J_SD is the judgement set of `Rules.lean`, and Ctxr/J_SD is `Ctx.model`. The bidirectional
notation is paper-only.

**Optional, not adopted: per-constructor congruence.** Replace `congr` by
x(t) ≡ x(t′) whenever t ≡ t′ : Θ. Equality would then be syntax-directed, apart from symmetry
and transitivity, and functionality would become a theorem, proved by a hereditary induction
like the substitution lemma. Adams' obstacle (equal substitutions not known to be well formed)
should not arise, since R1 is built into t ≡ t′ : Θ. This would be new Lean work and is
unverified.

**Why separate.** This is Lean's definition (`Typing/Rules.lean`). All the formalized
metatheory and the initiality proof are about it. It is the *presentation* in which
derivations are by structural recursion on raw syntax.

### Metatheory

The Lean results, for the syntax-directed system:
- renaming and weakening;
- η (`Typing/Eta.lean`);
- the hereditary substitution lemma (`Typing/SubstitutionLemma.lean`);
- presuppositions;
- equivalence and conversion (`Typing/Equivalence.lean`, `Typing/Invariance.lean`).

**How the work divides between the two rule systems.**

| | canonical rules (J.1–J.4) | syntax-directed rules |
|---|---|---|
| weakening, substitution, conversion, functionality | rules, so free | theorems: the substitution lemma, Invariance, `congr` |
| being a C-system | the structural rules are exactly this (`prop:structural-subquotient`) | follows from the theorems above |
| inversion; no confusion between `sort`, `of` and `eq`; injectivity of Bind | not available directly | free: one rule per constructor (`Ctx/Inversion.lean`) |
| deciding well-formedness, given equality | no | one traversal |

The canonical rules need only two things beyond their definition:
1. `prop:structural-subquotient`;
2. the inclusion J_HrS ⊆ J_SD, which uses the metatheory of the syntax-directed rules.

Everything else, such as inversion for the canonical rules, is transported along ι.

### Comparison with the syntax-directed rules

- **Translation of the seven forms into the four**, under ⊢ Γ:

  | syntax-directed judgement | translation |
  |---|---|
  | Γ ⊢ e | Γ ⊢ e : []∂_Γ(e), with ∂_Γ(e) not an equation |
  | Γ ⊢ β bd | Γ ⊢ []β |
  | Γ ⊢ Θ | ⊢ Γ ⋈ Θ |
  | Γ ⊢ t : Θ | as in item 2 |
  | equalities | the corresponding equality judgements, with the presuppositions made explicit |

  J_SD denotes the quadruple of four-form judgements whose translations are derivable by the
  syntax-directed rules. Lean's `Ctx.model` is Ctxr/J_SD, up to the C-system/CwF
  correspondence (ALN).
- **`prop:canonical-in-syntax-directed`.** J_HrS ⊆ J_SD. *Proof:* J_SD is HrS-closed, so the
  inclusion follows by leastness. For the closure:
  - structural closure is the metatheory: weakening, the substitution lemma, conversion, and
    η for the variable rule;
  - formation under ρ is immediate: `dec-cons`, the boundary rules, and concatenation of
    decorated arities for lam/unlam;
  - congruence comes from the equality rules;
  - reflection is `hyp`;
  - irrelevance holds because `Eq_s` ignores equation-slot fillers.
- **`cor:canonical-iso`.** The homomorphism ι : Ctx → Ctxr/J_SD induced by the inclusion,
  which is the identity on raw representatives, is an isomorphism of C(HrS)-systems.
  *Proof:* by Lean's initiality of Ctxr/J_SD there is a homomorphism κ back. κ∘ι = id by
  item 15, and ι∘κ = id by initiality.
- **The sets are not equal.** J_HrS ⊊ J_SD. Over Γ = (A : sort, a : of(A)), J_SD contains
  Γ ⊢ a : []eq(A, A), whereas J_HrS contains only Γ ⊢ A : []eq(A, A) (reflSort). The two
  are equal in J_SD by irrelevance, so ι is still bijective on classes.
- **`def:saturation`.** J^sat is the least quadruple closed under the rules of J_HrS plus one
  rule:

  X ⊢ t : [Θ]eq(l,r)  ⟹  X ⊢ t′ : [Θ]eq(l,r), for every raw t′.

  It must be a *closure*, not merely J_HrS with fillers added. Variables of equation slots
  can occur inside arguments at equation slots (e.g. f(η_x) with f : [y : eq(a,b)] sort), so
  substitution propagates arbitrary fillers into other judgements.
- **`thm:presentation`** (optional). J_SD = J^sat.
  - (⊆) Induction on syntax-directed derivations. Each syntax-directed rule is derivable from
    the B-system rules plus saturation:
    - `ap` as in item 20;
    - `hyp` as `ap` at an equation slot followed by reflection;
    - `sub-eq` from reflSort/reflElement, conversion and saturation;
    - `congr` from (7b) and (6b);
    - the remaining rules from formation and congruence.

    `Generation.lean` is the quotient-level version of this induction.
  - (⊇) `prop:canonical-in-syntax-directed`, plus closure of J_SD under saturation, which
    holds because `Wf_s` ignores equation-slot fillers.

**Why this order.**
- The isomorphism, which is all the Initiality chapter needs, uses only the inclusion
  J_HrS ⊆ J_SD, i.e. the metatheory. So it comes right after the metatheory.
- The exact description J_SD = J^sat is about derivability, not about the model. It
  justifies calling the syntax-directed figure a presentation of the canonical rules, and
  can be reduced to a remark if space is short.
- Ctx is not shown initial independently. It is initial *because* ι identifies it with
  Lean's model, and the isomorphism is ι itself: canonical and syntactic, not merely "two
  initial objects are isomorphic".

---

## 8. Consequences for the Initiality chapter

- HrS and C(HrS)-systems are already defined in the well-formed syntax chapter, so the
  *Models* part shrinks to recalling them.
- The rule ↔ operation dictionary table of the old plan is replaced by item 16 together with
  `fig:hrs-rules`.
- Existence: Lean proves Ctxr/J_SD (`Ctx.model`) initial. By `cor:canonical-iso`,
  Ctx ≅ Ctxr/J_SD via ι, so `Ctx` is initial.
- **General formulation.**
  - IC(S, C(T, M), ρ): C_{S,ρ} is initial.
  - The fully annotated raw syntax of S, and the canonical conjecture.
  - Relative form: given the canonical conjecture, IC holds iff an elaboration
    homomorphism C_{S,ρ} → C_{S,ρ_S} exists.
  - The counterexample: ρ identifying two constants.
  - Place in the discussion: Voevodsky's RDP formulation, Kaposi–Xie (SOGAT → GAT), Uemura.

---

## 9. Formalized vs paper

| item | status |
|---|---|
| J.1 (raw judgements, structural rules, subquotient) | paper; Voevodsky's proofs, sorted |
| J.2 HrS | Lean `HrS.Structure` (non-contextual; ALN for the contextual reading) |
| J.3 general construction, items 14, 15 | paper; formal and short |
| J.4 ρ and its laws | Lean, on the subquotient (`Ctx/Universe.lean`, `Ctx/Identity.lean`, `Ctx/Binding.lean`); the raw-level statement is paper |
| item 15 for HrS | Lean `Morphism.agree_closed` + `Ctx.generated` (syntax-directed model) |
| presentation theorem | paper, using the Lean metatheory; (⊆) mirrors `Ctx/Generation.lean` |
| initiality | Lean (`Initiality/`) |

---

## 10. Citations

Existing keys:
- `Voevodsky2014Module`: Props. 4.1, 6.2, 6.11, Rem. 4.2, Def. 6.1;
- `Voevodsky2014Subsystems`: Prop. 4.3, Def. 5.1, Lemma 5.2, Prop. 5.4;
- `Voevodsky2016Relative`: Def. 5.11, Thm. 6.10, introduction;
- `AhrensLumsdaineNorth2024`: Props. 41, 45, 48;
- `Cartmell1986`;
- `HaselwarterBauer2023`, `KaposiXie2024`, `Uemura2023`.

To add:
- Voevodsky, *Products of families of types in the C-systems defined by a universe
  category*, arXiv:1503.07072 (Defs. 2.2–2.3);
- Voevodsky, *From syntax to semantics of dependent type theories — formalized*, RDP 2015
  notes, Warsaw, 30 June 2015 (slides 15–18);
- a reference for CwFs, and for 𝕋_CwF written as a GAT (Dybjer 1996, *Internal type
  theory*, for CwFs).

---

## 11. Open items

1. **Name and macro of the GAT.** "HrS" as in Lean, or a name derived from ToS^ω?
2. **Reference for 𝕋_CwF as a GAT.** Dybjer 1996 defines CwFs but does not write out the GAT.
   Is there a preferred source?
3. **Notation clash.** Γ ⊢ u : E and Γ ⊢ t : Θ denote both the judgements of J.1 (items 1
   and 2) and the syntax-directed checking judgements. They agree up to saturation. Options:
   mark the syntax-directed ones (e.g. ⊢ₛ), or keep one symbol and let the comparison justify
   it.
4. **⚑ Item 5.** Check the sorted versions of Module Props. 4.1/6.2 against Voevodsky's
   proofs.
5. **Stability equations of unlam, reflSort and reflElement.** Add them to HrS on paper
   (Lean derives them), or relax item 7 to "stability equations hold or are derivable".
6. **Congruence rules in `fig:hrs-rules`.** List all of them, or give the scheme with
   examples (item 18)?
