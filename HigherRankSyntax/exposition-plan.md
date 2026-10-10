# Raw higher-rank syntax and its relative monad: exposition plan

Notes for writing the exposition (2026-10-09). Three parts:

- **Part I. Outline.** The points to make, in order, with status tags.
- **Part II. Examples.** Raw expressions by rank. The high end is type-theoretic translations, as in the talk.
- **Part III. "The substitution lemma once for all".** What the observation says and why it holds.

Checking:
- Every example and computation below was run through a Python mirror of `Expr`, `Expr.η` and `Subst.act` (hereditary, faithful to `act_left`/`act_middle`/`act_right`).
- Every Lean name was checked against the tree.
- Literature claims were checked against the sources; the unverified ones are marked.
- The type-theoretic translation examples II.17, II.18, II.21, II.23, II.24 and II.32 were computed and checked once, without the independent second pass the other examples had.

Sources:
- **talk** = Ahman–Bauer, *One syntax to rule them all*, SSTT Stockholm, 20 May 2022 (handwritten notes, 17 pp.).
- **MATH.md** = Andrej's write-up at the repository root.
- **BHL** = Bauer–Haselwarter–Lumsdaine 2020.
- **HB** = Haselwarter–Bauer, JAR 2023.
- **PK** = Petković Komel, PhD thesis 2021.

## Conventions

- **Arities.** An arity is a finite list of arities. Named slots are cosmetic: `[A, B:[x]]` is `[[], [[]]]`.
- **Expressions.** Written with named binders: `Π(A, x. B(x))`. In `x(ȳ₁. t₁, …)`, the i-th argument binds the slots of the i-th slot of x's arity.
- **Rank.** `rank [] = 0` and `rank [α₁,…,αₙ] = 1 + max rank αᵢ`, as in the talk and MATH.md. The rank of a slot is the rank of its arity:

  | slot | rank |
  |---|---|
  | variable, constant | 0 |
  | operation or metavariable | 1 |
  | binder | 2 |
  | schema | 3 |

  The rank of a theory is its rank as an arity: GAT 2, SOGAT 3, Ξ_data 4. Older notes (initiality.md, data-schemas.md) count slots from 1, one more than here; theory ranks agree.
- **Status tags.**
  - [Lean]: proved in the live tree.
  - [Lean, pruned]: formalized once, since removed.
  - [paper]: standard or a short argument, not formalized.
  - [open].

---

# Part I. Outline

## 0. Motivation

- **Three kinds of symbols, three replacements** (talk p.2):
  ```text
  substitution    variable      ↦ expression                                x ↦ suc 0 + y
  instantiation   metavariable  ↦ abstracted expression                     B ↦ x. Vec(suc x)
  transformation  symbol        ↦ expression with abstracted metavariables  ∃ ↦ A B. ‖Σ(x:A). B(x)‖
  ```
- **Each kind is developed separately.** Each has renamings, an action, identity and composition laws, and laws for its interaction with the other two. Classical developments go level by level:
  - BHL: Props 3.19, 3.20, 3.27; raw syntax maps in Def 6.22.
  - HB: substitution (Thm 3.8) and instantiation (Thm 3.13) are separate theorems.
  - PK: three relative monads, Ch. 7–8.
- **The levels depend on each other.** A transformation acts through instantiation (PK Def 8.2.5), and an instantiation acts through substitution (BHL Def 3.24). The talk's abstract: "three levels of substitution, each depending on the previous one".
- **The question.**
  - Talk p.3: "How do we know we are not missing some laws? … very tedious to prove all the laws three times (we did it)".
  - PK §11.2: whether one can "unify the syntax of all three kinds of variables … and prove the theorems about them in a uniform way".
- **Deliverables.**
  - One datatype with one constructor, over arities that are also contexts.
  - One operation, hereditary substitution. Renaming, substitution, instantiation, transformation and their mixtures are instances of it.
  - One set of laws: the relative-monad laws, obtained through one interchange lemma.
  - (Outlook) One typed substitution lemma.

## 1. Arities and slots

- **Def.** `Ar` is the set of finite lists of arities (finite rose trees). The empty list is written `1` when it serves as the unit.
- **Def.** A slot of `Γ = [γ₁,…,γₙ]` is a position i, and its arity is γᵢ. `Γ ∋ α` is the set of slots of arity α.
- **Def.** `Γ ⋈ Δ` is concatenation. The slots of `Γ ⋈ Δ` are the slots of Γ followed by those of Δ (`inl`, `inr`); `1` has no slots.
- **Remark (contexts are arities).** A signature Σ, a metavariable context Θ and a variable context Γ are arities, and so is `Σ ⋈ Θ ⋈ Γ` (talk p.10: "([Σ, Θ, Γ], cl) is just an arity!").
- **Def (rank)** as in the conventions, counted from 0 as in the talk and MATH.md.
  - This is the literature's "order" of an operator, a type or a theory (Adams 2008, Arkor–McDermott), and Kleene's type level.
  - Logic's "second-order variable" (Fiore–Hur's metavariable) has rank 1.
  - Remark once that older notes and `agda/Rank.agda` count slots from 1.
- **Prop.** The relation "α is the arity of a slot of Γ" is well-founded (α is a proper subtree). Every recursion below goes along it: η, hereditary substitution, interchange, the typed substitution lemma. On paper this is structural recursion on rose trees. [Lean: `Carrier.subWf`]
- **Remark (λ-reading).** The arity `[α₁,…,αₙ]` is the simple type `⟦α₁⟧ → ⋯ → ⟦αₙ⟧ → o` over one base type o, and its rank is the order of that type.
- **Remark (classes).** The talk and MATH.md decorate each entry with a syntactic class (`Arity = List Arity × Class`). The development is classless; classes are sort declarations of the judgement layer (`Bd.sort`). Say where classes would enter: an extra index on slots and on `Expr`.
- **Side remark (formalization).** In the Lean an arity ℓ is represented by the endofunction `ℓ ++ −`, so ⋈ is composition. Then `(Γ ⋈ Δ) ⋈ Ξ = Γ ⋈ (Δ ⋈ Ξ)` and `Γ ⋈ 1 = Γ = 1 ⋈ Γ` hold by `rfl` (checked), and `Expr ((Γ ⋈ Δ) ⋈ Ξ)` and `Expr (Γ ⋈ (Δ ⋈ Ξ))` are the same type. On paper nothing is needed.

## 2. Expressions

- **Def.** For `x : Γ ∋ [α₁,…,αₙ]` and `tᵢ ∈ Expr(Γ ⋈ αᵢ)`, `x(t₁,…,tₙ) ∈ Expr Γ`. [Lean: `Expr.ap`]
- **Point: one constructor.** Every head is a slot. Variables, metavariables, symbols, rules and schemas are all slots of the context. Only their rank and their position in the context tell them apart.
- **Notation.** `x(ȳ₁. t₁, …, ȳₙ. tₙ)`. Names are cosmetic: the syntax is well scoped by construction, with no α-conversion and no wrong-arity terms.
- **Prop.** The arguments of x form a substitution: `Args Γ α = Subst α Γ` (by `rfl`). Hence an expression is a slot together with an instantiation of its arity: `x(t) = t*(η x)`. [Lean: `act_inst_η`]
  - This is the side remark in the talk's Agda: "the ts in the definition of Expr is just a substitution".
- **Remark (λ-reading).**
  - `Expr Γ` is the set of β-normal η-long terms of type o in context Γ.
  - `Expr(Γ ⋈ α)` is the set of such terms of type `⟦α⟧`, i.e. abstractions over α.
  - `x(…)` is a spine.
  - Example: `Expr [f:[x], a] = {a, f(a), f(f(a)), …}`, the Church numerals.
- **Remark.** `Expr 1 = ∅`, and also `Expr [f:[x]] = ∅`. Closed expressions need constants, so the base cases come from a theory.
- Induction principle; the rank table of Part II.

## 3. Renamings and η-expansion

- **Def.** A renaming `ρ : Γ → Δ` maps slots to slots of the same arity. Arities and renamings form a category 𝔸, in which ⋈ is a coproduct and 1 is initial. `ρ ⇑ Ξ = ρ + id_Ξ`. [Lean]
- **Action.** Renamings act on expressions by renaming heads and extending under binders. The action is functorial. [Lean]
- **Def (η-expansion).** For `x : Γ ∋ α` with `α = [α₁,…,αₙ]`, `η x := x(η y₁, …, η yₙ) ∈ Expr(Γ ⋈ α)`, where the yᵢ are the slots of α. It is defined by structural recursion on α and is natural in renamings. [Lean]
- **Point.** η is the identity substitution: since the syntax has only long normal forms, a slot becomes a term only after η-expansion.
- **History (one sentence at most).** The 2021–23 Agda attempts had η, but the action and composition of substitutions failed the termination checker. The Lean (2024–26) defines them by well-founded recursion on arities.

## 4. Substitution

- **Def.** `Subst Δ Γ := Π_{x : Δ ∋ α} Expr(Γ ⋈ α)`: each slot of Δ goes to an abstraction of its arity over Γ.
  - Values at slots of rank 0/1/2 are expressions / abstractions over variables / abstractions over metavariables.
  - Direction: this is a Kleisli map Δ → Γ, and a context morphism Γ → Δ.
- **Defs.** The identity (η); renamings as substitutions (`x ↦ η(ρ x)`); copairing; `Subst [α] Γ ≅ Expr(Γ ⋈ α)`.
- **Def (hereditary substitution).** For `σ : Subst Δ (Γ ⋈ Ξ)` and `e ∈ Expr(Γ ⋈ Δ ⋈ Φ)`, define `σ^Φ e ∈ Expr(Γ ⋈ Ξ ⋈ Φ)`. The prefix Γ is kept, the block Δ is replaced by Ξ, and the depth Φ is traversed:
  ```text
  head x in Γ or Φ:   x(t₁,…,tₙ) ↦ x(σ^{Φ⋈α₁} t₁, …, σ^{Φ⋈αₙ} tₙ)
  head z : Δ ∋ α:     z(t₁,…,tₙ) ↦ ι(σ z),  where ι := [yᵢ ↦ σ^{Φ⋈αᵢ} tᵢ] : Subst α (Γ ⋈ Ξ ⋈ Φ)
                      and ι acts with prefix Γ ⋈ Ξ, block α, depth 1
  ```
  [Lean: `Subst.act`; `act_left`, `act_middle`, `act_right`]
- **Point (the cascade).** In the second clause the block is α, whose slots have smaller rank than z. Replacing a slot of rank r triggers replacements of slots of rank < r, all the way down to 0.
- **Prop (well-definedness).** By lexicographic induction on (arity of the block, expression). [Lean]
- **Remark (why prefix and depth).**
  - The depth grows under binders.
  - The prefix makes the block of the hereditary call exactly α. Without it the block would be `Γ ⋈ Ξ ⋈ α`, which is not smaller.
  - Otherwise the prefix is inessential: with an empty new block, acting with prefix S equals acting by `copair(η_S, σ)` with empty prefix. [Lean: `act_copair_prefix`; the case of a non-empty new block is not stated in the repo]
- **Remark (λ-reading).** `σ^Φ e` is the β-normal η-long form of the ordinary substitution instance. Only framework-level redexes are contracted: an object-level `app(lam(…), …)` stays.
- **Def.** `comp σ θ x := θ^β(σ x)`.
- **Thm (unit laws)** [Lean: `act_id`, `act_η`].
  - The η-substitution acts as the identity.
  - σ acting on `η x` gives `σ x`.
  - Proof: a mutual induction. The identity law needs instantiation of an η-expanded head (`x(t) = t*(η x)`), and that needs the identity law at the smaller arity.
- **Thm (interchange, i.e. the substitution lemma)** [Lean: `act_interchange`]: `θ^Ω(κ e) = (θ_*κ)(θ^Ψ e)`, that is
  ```text
  e[κ/Ψ][θ/Θ] = e[θ/Θ][κ[θ/Θ]/Ψ]        (κ's values may mention Θ; θ_*κ = κ with θ applied to its values)
  ```
  - Barendregt 2.1.16, `M[x:=N][y:=L] = M[y:=L][x:=N[y:=L]]`, is the case of single rank-0 slots. Its side conditions x ≢ y and x ∉ FV(L) become scoping.
  - The talk's law `ρ_*(σ_* t) = (ρ_* σ)_*(ρ_* t)` is the case where θ is a renaming.
  - Proof: induction on the unordered pair {arity of θ's block, arity of κ's block}, where at each step one entry decreases, and then on e.
    - In the hereditary case the two substitutions swap roles, so no ordered measure works.
    - This is the technical heart of the development; present it in full.
- **Thm (associativity)** [Lean: `act_comp`, at any prefix]: `(comp σ θ)^Φ = θ^Φ ∘ σ^Φ`. The proof is induction on e; the hereditary case is the interchange law at the head's arity.
- **Derived laws** [Lean]:
  - renaming versus substitution: `act_rename`, an instance of `act_square`;
  - weakening cancels: `act_rename_cancel`;
  - lifting under binders: `Subst.lift`, `lift_id`, `lift_comp`, `lift_assoc`.

## 5. The uniform pattern (summary; Part III in full)

- Over `Σ ⋈ Θ ⋈ Γ` (signature, metavariables, variables), the three operations are one action with three different splits:
  ```text
  operation        prefix   block   depth
  substitution     Σ ⋈ Θ    Γ       bound variables
  instantiation    Σ        Θ       Γ ⋈ bound
  transformation   1        Σ       Θ ⋈ Γ ⋈ bound
  ```
  Values see the prefix and the new block, never the depth.
- **Role is the block, not the rank.** One can instantiate a metavariable of symbol rank (`$` in eqPreserve, II.22) or transform a symbol of operation rank (the Mal'cev term, II.5).
- The classical defining clauses (BHL Def 3.24, PK Def 8.2.5) are all the hereditary clause.
- All laws, including the interaction laws between levels, follow from the interchange lemma and the monad laws.
- Translations are morphisms of the substitution monads T'_S → T'_{S′} (§7); their laws are again interchange. [paper; the ingredients are in Lean]

## 6. The relative monad

- **Def** (Altenkirch–Chapman–Uustalu): a relative monad over J : 𝔸 → 𝔼.
- **Thm** [Lean: `SyntaxMonad`]:
  - 𝔼 is the category of families indexed by the *set* of arities. The index is discrete: the talk's `Set^{C×Class}` must be read this way, because `Var γ (δ, cl)` is not functorial in δ.
  - `J Γ = (α ↦ Γ ∋ α)` and `T Γ = (α ↦ Expr(Γ ⋈ α))`.
  - The unit is η, and the extension `f*` at index α is substitution at depth α.
  - The laws are `act_id`, `act_η` and `act_comp`.
- **The Kleisli category.**
  - Objects are arities, and morphisms are `Subst` (definitionally).
  - The identity is η and composition is `comp`; ⋈ gives coproducts; `Subst [α] Γ ≅ T Γ α`.
  - J is fully faithful: renamings are exactly the family maps `J Γ → J Δ`.
- **Grading** [Lean]. `T Γ α = T(Γ ⋈ α) 1` definitionally, and the extension at index α is the extension of `lift σ α` at index 1 (`act_lift_depth`). This is the formal content of the talk's "Expr has to be suitably graded over C".
- **Modules** (Hirschowitz–Maggesi; Ahrens 2016). A left module is a functor out of the Kleisli category.
  - Examples: `Γ ↦ Expr(Γ ⋈ α)`, boundaries, telescopes (laws [Lean], packaging partly).
  - Arity modules and their tensor (a monoidal category) [Lean]. Telescopes concatenate exactly like ⊗; decorated telescopes were once a monoid object in it [Lean, pruned].
- **Remark.** Downstream, the development uses the laws directly, not this packaging.

## 7. Restrictions and special cases

- **Syntax over a fixed signature S.** `T'_S Γ α = Expr(S ⋈ Γ ⋈ α)`, with extension = action with prefix S.
  - Right unit and associativity hold at any prefix [Lean].
  - The left unit and the instance were formalized and then removed [Lean, pruned; re-porting is routine].
  - `Kl(T'_S)` is the full subcategory of the coslice `S/Kl(T)` on the objects `(S ⋈ Γ, inl)`.
  - The judgement layer consumes exactly these prefixed actions (`Subst.fill`, `Subst.instantiate`, `Subst.apply`).
- **Translations as monad morphisms** [paper; ingredients Lean]. A transformation `f : S → S′` acts on `T'_S Γ α` by f at depth `Γ ⋈ α`. This gives a morphism of relative monads `T'_S → T'_{S′}`:
  - unit law: `act_η_right`;
  - extension law: `act_interchange`;
  - functoriality: `act_id`, `act_comp`.

  One level down, instantiations `Θ → Θ′` are morphisms `T'_{S⋈Θ} → T'_{S⋈Θ′}`.
- **Precomposition** (talk p.16) [paper]. For F : 𝔹 → 𝔸, the data (J∘F, T∘F) is again a relative monad, and the laws transfer. Instances:
  - first-order syntax: Fin, i.e. contexts of rank-0 variables over S;
  - second-order syntax: metavariables and variables;
  - STLC: `n ↦ σ_T ⋈ [x₁…xₙ]`.

  At the bottom sits Voevodsky's equivalence of Lawvere theories with J_f-relative monads: for S whose slots have rank ≤ 1, `n ↦ Expr(S ⋈ [x₁…xₙ])` is the free Lawvere theory on S.
- **Caution** [paper, settled]. Restricting the index to [] on the full base is not a relative monad.
  - Counterexample: Γ = [m:[x], a], Δ = [b], with f : a ↦ b and g : b ↦ η(a).
  - So MATH.md §5.4.3 needs both a fixed prefix S and base Fin.
- **Variables versus argument-less metavariables** (talk p.9: "we will see later how to recover it"). Both are slots of arity []. The distinction is positional, i.e. which block they sit in. Compare PK Prop 4.3.6 ("promotion" of variables to metavariables).

## 8. Structural characterizations (remarks)

- **Containers** [paper]. `Expr` is the initial algebra of the indexed container `X ↦ (Γ ↦ Σ_α (Γ ∋ α) × Π_{i : α ∋ Λ} X(Γ ⋈ Λ))` (MATH.md §4).
- **Free CCC** [paper]. `Kl(T) ≅ Cl(λ→_o)^op ≃ (free CCC on one object)^op`, where `Cl(λ→_o)` is the category of contexts of λ→ with one base type, terms modulo βη.
  - Route: β-normal η-long forms are unique representatives (Keller–Altenkirch 2010); hereditary substitution computes normal forms; Lambek–Scott.
  - Direct proof that `Kl(T)^op` is cartesian closed: products are ⋈, the terminal object is 1, `Δ ⇒ [γ₁,…,γₘ] := [Δ⋈γ₁, …, Δ⋈γₘ]`, and transposition is the identity on terms.
  - Closest statements in print: Arkor–McDermott, *Higher-order algebraic theories* (L_ω(1) ≃ Λ_ω(1), the initial ω-order theory, with homs the β-short η-long terms built exactly like `Expr`); Fiore–Mahmoud 2010, Lemma 4.1 (the second-order slice).
- **Conjecture.** J-relative monads ≃ Ar-sorted Lawvere theories (many-sorted Voevodsky). Under it, `SyntaxMonad` corresponds to the free CCC on one object, with the →-types as sorts.
- **Open (talk p.15, "invert the picture").** Which relative monads express syntax with binding?
  - Candidate: `SyntaxMonad` is initial among graded J-relative monads.
  - BHL p.16 suggests "a scope-graded monad" (Orchard et al. 2020).

## 9. Related work (checked against the sources)

- **Closest raw-syntax prior art: Adams 2008**, *Lambda-free logical frameworks* (arXiv:0804.1879; from Aczel's unpublished note and Adams' 2004 thesis).
  - The same as here (§2.1–2.3 of the paper):
    - arities `(α₁,…,αₙ)` with base `0 = ()`, and "order" is exactly our rank;
    - one formation rule for objects, `z[[x⃗₁]M₁, …, [x⃗ₙ]Mₙ]`, the same as `Expr.ap`; abstractions occur only as arguments;
    - one syntactic class; types and terms are told apart only by kinds;
    - `z^η ≡ [x⃗] z[x⃗^η]`, the same as `Expr.η`;
    - hereditary instantiation by recursion on (arity, object); the substitution lemma by induction on the sum of orders.
  - Different:
    - heads come from two classes: constants (from a signature outside the context) and variables (from the context, which has an arity);
    - instantiation `{F/x}N` (Def 2.2) replaces a single variable x, of any arity, by an abstraction F. Several variables are handled by iterating it (`{F⃗/Δ}`). Constants are never replaced, so there are no translations;
    - the hereditary step plugs the arguments into F's parameters one at a time, whereas `Subst.act` substitutes the whole arity of the head in one call;
    - `{F/x}` maps objects to objects in one global named syntax. `Subst.act` maps `Expr(Γ ⋈ Δ ⋈ Φ)` to `Expr(Γ ⋈ Ξ ⋈ Φ)`, replacing a whole block simultaneously. So Adams has no composition of substitutions, no associativity law and no relative monad;
    - his substitution lemma, Lemma 3.3(1), states the one-slot case of `act_interchange`, but its proof is a single sentence ("by induction on the sum of the orders"). The case analysis is not written out. That includes the role swap when the head is the outer variable, which is what `.aux`/`.subst` and the unordered-pair measure handle. As printed, its side condition "y not free in M" must mean F;
    - variables are named, up to α-conversion;
    - the typing layer has kinds `Type`, `El(A)` and product kinds, a direct antecedent of the judgement layer; Cut is proved only for restricted specifications.
- **Canonical forms and hereditary substitution.**
  - Watkins–Cervesato–Pfenning–Walker 2002 (CMU-CS-02-101), where the operation is called "instantiation";
  - Harper–Licata 2007;
  - Keller–Altenkirch 2010, which shows that normal forms decide βη for λ→ with one base type.
- **Levels of variables.** Boespflug–Pientka 2011: n levels of variables and one hereditary substitution, but signature constants stay separate.
- **LF signature morphisms.** Harper–Sannella–Tarlecki 1994 (Def 6.1, Prop 6.2); Rabe–Schürmann 2009; Rabe 2013. Translations preserve typing, proved once for LF, but as a notion parallel to substitution.
- **Relative monads and modules.** Altenkirch–Chapman–Uustalu 2010/2015; Ahrens 2016; Hirschowitz–Maggesi 2007; Voevodsky 2016; Arkor–McDermott (abstract clones FSCD 2021; formal theory of relative monads).
- **Second-order syntax.**
  - Aczel 1978; Fiore–Plotkin–Turi 1999; Fiore–Hur 2010; Fiore–Mahmoud 2010;
  - Arkor–McDermott, *Higher-order algebraic theories*: metasubstitution is substitution of a higher-order variable (Remark 3.2); translations are theory maps;
  - Fiore–Szamozvancev 2022: substitution and metasubstitution laws generated once for every second-order signature (ranks ≤ 2).
- **Generic syntax.** Allais–Atkey–Chapman–McBride–McKinna 2018/2021 (binders bind first-order variables only, no metavariables).
- **The three-level line.**
  - BHL 2020: metavariables are fresh symbols (Def 3.22); instantiation is Def 3.24; raw syntax maps are Def 6.22.
  - HB 2023: metavariables are a separate class; no transformations.
  - PK 2021: three relative monads; type-theoretic transformations preserve derivability (Thm 9.1.3); §11.2 poses the question.
  - Formalizations: `formaltt` (Loutchmia–Taslak–Ahman–Bauer) and Andrej's Agda `dependent-type-theory-syntax`.
- **Translations.**
  - Boulier–Pédrot–Tabareau 2017;
  - the reader translation is Pédrot–Tabareau POPL 2020, not BPT;
  - Bernardy–Jansson–Paterson 2012;
  - Plotkin 1975;
  - Sabry–Wadler 1997.
- **Not verified yet** (check before citing): Nanevski–Pfenning–Pientka 2008; Fiore 2008; McBride 2005; Autosubst; Schäfer–Smolka–Tebbi 2015; Čubrić–Dybjer–Scott 1998; Statman 1979; Hamana 2004 (bibliographic data only); Lambek–Scott (only secondary confirmation).

## 10. Outlook (one bullet each)

- **Judgement layer** (it exists): boundaries `sort | of S | eq l r`, decorated telescopes, the seven judgements, `substitutionAt` (Part III.8), the category of contexts, initiality.
- **Algebras of the relative monad** (MATH.md §5): at rank 0 they are sets; above rank 0 they carry monoid actions; EM(T) is still to be identified.
- **Dependency** (MATH.md §6): shapes form a category, a directed container.
- **Equations as quotients** (talk p.17).
- **The talk's wish list**: linearity, and intrinsic syntax for dependent types.

## Decisions to fix before writing

- **Notation** for extension (⋈ or the talk's ⊕).
- **Direction and notation of substitutions**: `Subst Δ Γ`, written `σ : Δ ⇝ Γ` or `Kl(Δ, Γ)`. Say once that Kleisli maps and context morphisms point in opposite directions.
- **Notation for the action**: `σ^Φ`, `σ*` or `e[σ]`. Decide whether prefix and depth appear in it.
- **Names.** Named binders in the text, positions in the definitions.
- **Vocabulary.** "arity" and "slot" (rather than the talk's "syntactic context" and "variable").
- **Classes.** A remark, or a second running example with classes.

## Pitfalls for readers

- `T Γ α = Expr(Γ ⋈ α)` is an abstraction over α's slots, not "an expression of type α".
- `Subst Δ Γ` is a Kleisli map Δ → Γ but a context morphism Γ → Δ.
- The monad contracts only framework redexes; object-level `app(lam(…), …)` stays.
- Variables, argument-less metavariables and constants are all slots of arity []. Which one a slot "is" depends only on its position.
- The action is relative to a split. Prefix and depth are implicit parameters, and actions at different depths are related by `act_lift`.
- `Expr 1 = ∅`: closed expressions need constants.
- Older notes count slot ranks from 1; the exposition counts from 0, like the talk.
- `MATH.md` is out of date in six places; see the appendix.

## Order of presentation, and which proofs to give

1. Motivation, with the talk's three examples.
2. Arities as rose trees, slots, ⋈ and rank; the λ-reading as intuition.
3. Expressions, with the rank table of Part II.
4. Renamings, then η.
5. Substitution: `Subst`; the action with prefix, block and depth; the three-splits table; a transformation trace (II.16); termination.
6. Laws: unit laws, interchange, associativity, then derived laws.
7. The prefix construction T'_S, translations as monad morphisms, precomposition.
8. The uniform pattern (Part III).
9. The relative monad and its Kleisli category; modules briefly.
10. Structural results: free CCC, containers, Lawvere theories.
11. Related work and outlook.

Proofs:
- **In full:** η and the action with their measures; the unit laws (mutual induction); the interchange law, including the role swap and the unordered-pair measure; associativity from interchange (a few lines).
- **Sketch:** renaming functoriality; `act_ofRenaming`, `act_rename`; the lift laws; the Kleisli packaging; cartesian closure of `Kl(T)^op`.
- **State only:** modules and the tensor; containers; the free-CCC proposition; the Lawvere correspondence.

---

# Part II. Examples of raw expressions, by rank

Displayed signatures and expressions are in the checker's input syntax and were checked (`trunc` is written `‖·‖` in traces). A few inline formulas are abbreviated. For each example: the slots with their arities, the expression, and what it shows. "Cascade 3 → 2 → 1 → 0" lists the ranks of the slots replaced, in order, during one hereditary substitution.

## Rank 0: variables, constants, argument-less metavariables

**II.1 Universal instantiation** (Hilbert-style first-order logic; Enderton §2.4).
```text
0 : [];  R : [a, b];  imp : [p, q];  ∀ : [φ:[x]];   metavariables φ : [x], t : []
imp(∀(x. φ(x)), φ(t))
```
- The constant 0, the metavariable t, the bound x and an ambient variable y are all slots of arity [].
- Role is position: in an instance, t sits in the block, y in the prefix and x in the depth.
- Enderton's side condition "t substitutable for x" becomes scoping: `t ↦ x` is ill-scoped and rejected, and capture is avoided automatically.

## Rank 1: operations, first-order metavariables, equations

**II.2 Group terms.** Signature `u : [], m : [x, y], i : [x]`.
- The commutator `m(m(i(x), i(y)), m(x, y))`.
- Substituting `x ↦ m(y, z)` is the action with block `[x]` and prefix the signature. No abstraction is needed.

**II.3 An axiom is a slot.**
- `assoc : [x, y, z]`, declared by the equation `m(m(x, y), z) ≈ m(x, m(y, z))`.
- `assoc(a, i(a), b)` is a valid raw expression: the raw syntax cannot tell an axiom from a ternary operation.
- Only the boundary distinguishes them. Well-formed expressions may not be headed by an equation slot; `Eq_e.hyp` instantiates the axiom to `m(m(a, i(a)), b) ≈ m(a, m(i(a), b))`.

**II.4 A GAT: the theory of categories** (Cartmell).
```text
Ob : [];  Hom : [a, b];  id : [a];  comp : [a, b, c, g, f];  lunit, runit : [a, b, f];  assoc : [a, b, c, d, h, g, f]
comp(x, y, z, g, comp(x, x, y, f, id(x)))
```
- All slots have rank ≤ 1, so the theory, as an arity, has rank 2.
- The dependency of `Hom(a, b)` on a and b lives entirely in the judgement layer.

**II.5 One substitution, two readings** (Mal'cev).
- `p : [x, y, z]` with `p ↦ x y z. m(m(x, i(y)), z)`.
- If p is a metavariable, this is the instantiation that witnesses Mal'cev's condition for groups.
- If p is a symbol, it is a transformation interpreting Mal'cev algebras in groups (a theory morphism, because both Mal'cev identities hold in groups).
- At rank 1, instantiation and transformation are visibly one operation.

**II.6 A higher-level hypothesis** (LF, natural deduction).
```text
… impI : [P, Q, d:[u]];  allI : [A:[x], d:[x]];   context: A, B : [x],  h : [x, u]
allI(x. imp(A(x), B(x)), x. impI(A(x), B(x), u. h(x, u)))
```
- h is a rank-1 *variable*: an assumption "for all x, from u : A(x) infer B(x)".
- Substituting a derivation for h is a rank-1 replacement whose hereditary steps substitute x and u.
- Variables can have any rank; what makes h a variable is its block.

## Rank 2: binders, rules, and translations of binders

**II.7 The talk's Π and λ, without classes.**
- `Π : [A, B:[x]]` and `λ : [A, t:[x]]`.
- Π-formation's conclusion over its metavariables is `Π(A, x. B(x))`.
- The talk's instantiation `{A ↦ N, B ↦ x. Vec(suc(x))}` gives `Π(N, x. Vec(suc(x)))`. Cascade: B (1) → x (0).
- The class `tm` of the bound x becomes the boundary `of tm(A)`, a sort that depends on A, which a fixed class cannot express.

**II.8 MLTT as one context.**
```text
ty : [];  tm : [A];  Π : [A, B:[x]];  λ : [A, B:[x], b:[x]];  app : [A, B:[x], f, a];
β : [A, B:[x], b:[x], a];  η : [A, B:[x], f];  Σ, pair, fst, snd;  Id : [A, a, b];  refl : [A, a];  J : [A, a, C:[y, p], d, b, q]
```
- Formers, constructors, eliminators and the β/η rule slots all have rank 2.
- Even `app` is rank 2, because the boundary of an application needs the family `B : [x]`.
- J's motive binds two variables.

**II.9 The β-rule three ways.** The rule is `β : [A, B:[x], b:[x], a]`, declared `app(A, x. B(x), λ(A, x. B(x), x. b(x)), a) ≈ b(a)`.
- **As a symbol:** `β(N, x. N, x. suc(x), zero)`, a rule applied to arguments, i.e. an instantiation of its premise block.
- **As an instance:** `σ = {A ↦ N, B ↦ x. N, b ↦ x. suc(x), a ↦ y}` sends the right side `b(a)` to `suc(y)`. Cascade: b (1) → x (0).
- In the instance, the object-level substitution `b[a/x]` is performed by the framework's instantiation.

**II.10 Binders of ordinary mathematics.**
- `∀(x. ∃(y. =(m(x, y), u)))`.
- `∑(0, n, k. ∫(0, 1, x. pow(x, k)))`.
- `rec : [n, a, b:[k, r]]`, primitive recursion: one argument binds two variables.

**II.11 The PA induction scheme as one slot.**
- `ind : [φ:[n]]` with boundary `pf(⇒(∧(φ(0), ∀(n. ⇒(φ(n), φ(S(n))))), ∀(n. φ(n))))`.
- Infinitely many first-order axioms become one rank-2 slot, and its instances are fillings of the binding.
- The second-order axiom, which binds `X : [n]` under a quantifier, is one rank higher.

**II.12 Cubical.** `plam(i. λ(A, x. papp(app(p, x), i)))` proves function extensionality.
- A dimension variable is a rank-0 slot like a term variable; "the interval is a sort but not a type" is a judgement-layer fact.
- Kan composition `comp : [A:[j], φ, u:[h, j], a₀]` is also rank 2.

**II.13 Presentation decides the rank.**
- W-recursion, Martin-Löf 1984: `T : [c, d:[x, y, z]]`, rank 2, with the induction hypotheses reified as elements of Π-types.
- System F: `Λ : [D:[X], b:[X]]`, rank 2.
- Both reach rank 3 when the same data is a framework function (II.24, II.31).

**II.14 Unfolding definitions is a transformation.**
- `∃! ↦ φ. ∃(x. ∧(φ(x), ∀(y. ⇒(φ(y), =(y, x)))))`: φ is used twice, at different arguments.
- `let ↦ a b. app(lam(x. b(x)), a)`, `A × B ↦ Σ(A, _. B)`, `¬φ ↦ ⇒(φ, ⊥)`.

### Translations of rank-2 symbols (the talk's "transformation")

**II.15 All three at once.**
- One Kleisli map on the mixed block `[x, B:[n], ∃:[A, P:[z]]]`: `{x ↦ suc(zero), B ↦ n. Vec(n), ∃ ↦ A P. ‖Σ(A, z. P(z))‖}`.
- On `∃(N, y. Id(B(x), y, x))` it gives `‖Σ(N, z. Id(Vec(suc(zero)), z, suc(zero)))‖`.
- The definition of `Subst` never mentions rank.

**II.16 The talk's transformation, traced.** `∃ ↦ A B. ‖Σ(A, x. B(x))‖` on `∃(N, x. ∃(N, y. Id(N, x, y)))`:
```text
replace ∃ (rank 2) by A B. ‖Σ(A, x. B(x))‖         at  N, y. Id(N, x, y)
  replace A (rank 0) by N
  replace B (rank 1) by y. Id(N, x, y)              at  x′
    replace y (rank 0) by x′
replace ∃ (rank 2) …                                (outer occurrence, same steps)
result: ‖Σ(N, x. ‖Σ(N, x′. Id(N, x, x′))‖)‖
```
Transformation → instantiation → substitution: the talk's "three levels, each depending on the previous one" happen inside one call.

**II.17 Propositions as types** (HoTT book Def 3.7.1; also PK Ex 9.3.1).
- One Kleisli map on a block of ranks 0–2: `⊤ ↦ 𝟙`, `⊥ ↦ 𝟘`, `∧ ↦ ×`, `⇒ ↦ →`, `¬ ↦ (P. →(P, 𝟘))`, `∨ ↦ (P Q. ‖+(P, Q)‖)`, `∀ ↦ (A B. Π(A, x. B(x)))`, `∃ ↦ (A B. ‖Σ(A, x. B(x))‖)`, `= ↦ Id`.
- Translating `∀(N, x. ∃(N, y. ∨(P(x, y), =(N, x, y))))` gives `Π(N, x. ‖Σ(N, y. ‖+(P(x, y), Id(N, x, y))‖)‖)`.
- Cascade depth follows rank: binders 2 → 1 → 0, connectives 1 → 0, constants 0.
- Note: `= ↦ Id` is not in Def 3.7.1.

**II.18 The same translation on rules.**
- `∃i : [A, B:[x], a, p] ↦ A B a p. |pair(a, p)|`.
- `∃e : [A, B:[x], C, p, m:[x, q]] ↦ A B C p m. trec(C, z. split(C, x q. m(x, q), z), p)`.
  - The minor premise m binds a variable and a proof hypothesis, so ∃e has rank 2.
- **Computed:** translating an instance of ∃e equals instantiating the translated rule with the translated fillers. This is the interchange law between a rank-2 transformation and an instantiation of the premise block.
- **Typed** [paper]: the translated ∃e is derivable only if C is a mere proposition. That holds for every translated formula, but must be carried as a side condition.

**II.19 Plotkin's call-by-value CPS** (Plotkin 1975, clauses as in Sabry–Wadler 1997):
```text
lam ↦ b. λk. k (λx. b(λh. h x))
app ↦ l m. λk. l (λx. m (λy. x y k))
z   ↦ λk. k z            (free variables are slots too)
```
- A bound variable is untouched while the body is translated. It receives its translation `λh. h x` only when the rank-1 slot b is instantiated.
- Object-level redexes are not contracted, which is the source of Plotkin's administrative redexes.

**II.20 A syntactic model of type theory** (Boulier–Pédrot–Tabareau 2017, the intensional-function translation `[·]_f`).
```text
Π   ↦ A B. ×(Π(A, x. B(x)), Bool)
lam ↦ A M. pair(lam(A, x. M(x)), true)
app ↦ M N. app(π₁(M), N)
```
- Every clause has the form "symbol ↦ abstraction over its arity".
- BPT's Prop 3, `[M{x:=N}] ≡ [M]{x:=[N]}`, proved there "by induction on M", is an instance of the interchange law.
- **Same pattern in programming languages:** an effect handler is a substitution of operation symbols. `get : [k:[s]]` and `put : [v, k:[x]]` are rank-2 symbols, and the state handler is `{get ↦ k. λs. k(s) s, put ↦ v k. λs. k(()) v, ret ↦ v. λs. (v, s)}`. Handling is the action; checked, the result β-reduces to the expected stateful program.

**II.21 Raw versus typed: impredicative encodings into CC.**
- `∃ ↦ A B. Π(Prop, X. Π(Π(A, x. Π(B(x), q. X)), k. X))`, i.e. `Π(X:Prop). (Π(x:A). B(x) → X) → X`, and similarly for ∨, ⊥, Σ.
- As a Kleisli map it is fine, and the β-rules map to derivable equations.
- The clause for dependent Σ-elimination is ill-typed (cf. Geuvers 2001 for λP2). So it is not a well-formed translation of a theory with dependent Σ-elimination.
- Arity correctness says nothing about typing.

## Rank 3: schemas, eliminators of higher-order constructors, translations at rank 3

**II.22 The talk's schema, and a translation clause as its argument.**
```text
eqPreserve : [S:[A, B:[x]], A, A′, B:[x], B′:[x]]
:= Π(≃(A, A′), e. →(Π(A, x. ≃(B(x), B′(app(e, x)))), ≃(S(A, x. B(x)), S(A′, x. B′(x)))))
```
- `S ↦ A B. Σ(A, x. B(x))`: cascade S (2) → B (1) → x (0) inside the unfolding of eqPreserve (3).
- `S ↦ A B. ‖Σ(A, x. B(x))‖`, the talk's translation clause for ∃: a rank-3 schema quantifies over translation clauses of Π-like symbols.
- **Computed:** translating the instance `eqPreserve(A B. ∃(A, x. B(x)), …)` equals instantiating with the translated clause.
- Here S is a metavariable of symbol rank, so this rank-2 step is an *instantiation*: role is the block.

**II.23 Applying a translation is an instantiation one rank up.**
- Take `t : [lam:[b:[x]], app:[f, a]]`, a slot whose arity is the whole λ-signature. It has rank 3: a term generic in the signature (Böhm–Berarducci; "finally tagless", Carette–Kiselyov–Shan).
- The raw expression `t(CPS(lam), CPS(app))` reads "the CPS translation of the unknown term t".
- Instantiating `t ↦ lam app. lam(x. app(x, x))` produces exactly the CPS translation of λx. x x (checked equal). Cascade: t (3) → app (1), lam (2) → b (1) → x (0).
- The same holds for the formula-generic slot `Φ : [⊤, ⊥, ∧:[P, Q], …, ∀:[A, B:[x]], ∃:[A, B:[x]]]` and the propositions-as-types clauses (II.17).
- So a translation is literally an argument list for a rank-3 slot, and two translations are two argument lists.

**II.24 W-types with framework functions, and reification** (Nordström–Petersson–Smith 1990 ch. 15 → Martin-Löf 1984).
```text
NPS:   sup  : [a, b:[x]]                     rank 2     wrec : [a, b:[y, z:[x], u:[x]]]   rank 3
ML84:  sup′ : [a, b]                         rank 1     T    : [c, d:[x, y, z]]           rank 2
σ :    sup  ↦ a b. sup′(a, λ(x. b(x)))
       wrec ↦ a b. T(a, y z u. b(y, x. Ap(z, x), x. Ap(u, x)))
```
- Rank 3 comes from one place only: sup takes a framework function, so the induction hypothesis of wrec's method is itself a binder.
- σ is a translation whose block holds a rank-3 symbol. On NPS's `nrofnodes` program it gives ML84's program verbatim. Cascade: wrec (3) → b (2) → u (1) → x (0).
- The reverse translation reifies in the other direction. The two are mutually inverse modulo Π-β and Π-η.

**II.25 Π-elimination at rank 3** (NPS §7.2).
- `funsplit : [f, d:[y:[x]]]` with `apply(f, a) := funsplit(f, y. y(a))`.
- The computation rule `funsplit(λ(b), d) = d(b)` runs d (2) → y (1) → x (0).

**II.26 Brouwer ordinals.**
- `ol : [f:[n]]` has rank 2, and `rec : [z, s:[a, r], l:[f:[n], g:[n]], a]` has rank 3.
- Producing a binder costs rank 2; consuming one costs rank 3.

**II.27 Eliminators from your notes.**
- The eliminator of HOAS λ-syntax `ind : [C:[t], v:[x], a:[s, u, p, q], l:[b:[x], h:[x]], t]` (metatheory.md §2.1), used for `unbind_z := ind(…, b h. b(z), t)`.
- The generic `ind` of data schemas (data-schemas.md §4) reaches rank 3 with first-order constructors only.
- The towers iterator `iter` (internalizing-metatheory.md §1).

**II.28 Higher-level natural deduction** (Schroeder-Heister 1984).
- General ⊃-elimination `impGE : [P, Q, R, d, e:[h:[u]]]`: the minor premise discharges a *rule* `h : [u]` (from P infer Q).
- e has rank 2 and impGE has rank 3.

**II.29 Contextual modal type theory.**
- `box : [M:[x]]` has rank 2, and `letbox : [M, N:[u:[x]]]` has rank 3.
- `letbox(box(x. M(x)), u. N(u)) = N(x. M(x))` is the talk's instantiation, made object-level.

**II.30 call/cc** (Arkor–McDermott Ex 3.18).
- `callcc, C : [f:[g:[a]]]` have rank 3.
- The translation `callcc ↦ f. C(g. g(f(a. g(a))))` sends `callcc(k. k(c))` to `C(g. g(g(c)))`. Cascade 3 → 2 → 1 → 0.

**II.31 Fω with framework-level operators.**
- `∀₂ : [D:[F:[X]]]` has rank 3.
- Instantiating `F ↦ X. ⇒(X, X)` performs type-level β by hereditary substitution, with no rule needed.
- With kinds internal (`tapp`, `tβ`) the same type language has rank 2.

**II.32 Erasure** (Church-style MLTT to an untyped calculus).
- Values drop the type metavariables, for example `λ ↦ A B b. λ(x. b(x))`, and keep the computational binders, including the rank-3 `Wrec`.
- On NPS's `nrofnodes` the result is NPS's own untyped program.
- Typed: this is a well-formed translation only if types are presented as codes (`El`), not as sorts.

## Rank 4 and beyond: the talk's "rank 4, rank 5, … What about these?"

**II.33 A schema over schemas.**
- `AllOps : [P:[S:[A, B:[x]]]]`: "P holds of every Π-like operator".
- With `AllOps ↦ P. ∧(P(A B. Π(A, x. B(x))), P(A B. Σ(A, x. B(x))))`, the expression `AllOps(S. ≃(S(N, x. Vec(x)), S(N, x. Vec(x))))` unfolds by the cascade 4 → 3 → 2 → 1 → 0.

**II.34 Fω's iterator over higher-order functors.**
- `∀₃ : [D:[H:[F:[X], Y]]]`, rank 4, in `∀H. ∀F. (∀X. H F X → F X) → ∀A. μH A → F A`.
- With framework-level operators, every rank occurs.

**II.35 The eliminator of a syntax with a rank-3 constructor** has rank 4: "the induction hypothesis inherits the shape of the constructor argument" (beyond-sogats-examples.md §8.2). This is the route to rank 4 in internalized metatheory.

**II.36 Side list from analysis and recursion theory**, read framework-level. A quantifier over objects of type level k has rank k + 2:
- the function quantifier in Kleene's Π¹₁ normal form `∀¹(α. ∃(n. R(e, bar(k. α(k), n))))`: rank 3;
- `inf` over functions in the Dirichlet energy `inf(f. ∧(=(f(0), 0), =(f(1), 1)), f. ∫(0, 1, x. sq(deriv(y. f(y), x))))`: rank 3;
- Kohlenbach's `(∃²)`: rank 4;
- the existence of Kleene's ³E: rank 5.

All of these drop to rank 2 once finite types are reified.

## Observations to draw from the list

- **Role is position, not rank.** Symbol, metavariable and variable name the block. Arity [] serves as constant, metavariable and variable alike (II.1); `[φ:[x]]` serves as ∀, ∃, μ, ε and as a metavariable Q.
- **Rank depends on the presentation.** Reifying framework functions lowers it by one: W-types (II.13/II.24), Fω (II.31), System F against towers, Z₂ comprehension.
- **Producing a binder costs rank 2; consuming one costs rank 3.** The induction hypothesis has the shape of the constructor argument (II.24–II.27, II.35).
- **Applying a translation is an instantiation one rank up** (II.22, II.23).
- **Raw Kleisli maps always compose. Being a well-formed translation is a typed condition** (`Wf_sub`). It fails in instructive places:
  - ∃e without propositional bookkeeping (II.18);
  - dependent Σ-elimination in CC (II.21);
  - erasure with types as sorts (II.32).

## Where the pattern stops

- **Translations that inspect their translated arguments** are not Kleisli maps. Examples: bracket abstraction λ → SK, normalization, closure conversion. The exception is a target with an eliminator for its own syntax (metatheory.md, Ξ ↦ Ξ⁺).
- **Arity-changing translations** are not Kleisli maps into a first-order target with the same arities:
  - the standard translation of modal logic, whose formulas become predicates on worlds;
  - Kripke forcing;
  - parametricity, where each variable gets two images (Bernardy–Jansson–Paterson Def 3.9).

  They do become Kleisli maps into a target with λ, respectively with pairs, up to object-level β (checked on examples). Equivalently, they factor as `σ* ∘ L` for a fixed structural map L that threads a world or doubles slots. The general lemmas for this are open.
- **Typed failures.** The Gödel–Gentzen translation is a Kleisli map on formulas, but as a transformation of type theories it fails for generic ∨E and ∃E (PK Ex 9.3.7).

---

# Part III. "Prove the substitution lemma once for all"

## III.1 The short answer

- **One kind of thing.** Variables, metavariables and symbols are slots of one context `Σ ⋈ Θ ⋈ Γ`. They differ by the block they sit in and, typically, by rank.
- **One replacement.** Send each slot of arity α to an expression abstracted over α (a Kleisli map), and act hereditarily. Substitution, instantiation and transformation are this action with the block chosen as variables, metavariables or symbols.
- **One recursion.** "Three levels, each depending on the previous one" is one recursion on rank. Replacing a rank-r slot instantiates its value at the arguments, which replaces slots of rank < r.
- **One set of laws.** These are the relative-monad laws, and their only real content is the interchange lemma (Barendregt's substitution lemma, for blocks of any rank).
  - Every classical law, including the laws relating different levels, follows from them.
  - The cross-level laws say that translations are monad morphisms.
- **One typed lemma.** Judgements are stable under fillings, by induction on rank. Admissibility of substitution, admissibility of instantiation and preservation of derivability by translations are its instances.

## III.2 Two lemmas called "the substitution lemma"

- **Syntactic.** Substitutions compose, `e[σ][θ] = e[σ;θ]`; its core is Barendregt's `M[x:=N][y:=L] = M[y:=L][x:=N[y:=L]]`. The talk is about this one: "(the usual syntactic lemmas) ≃ (categorical structure of the relative monad)".
- **Typed.** Substitution preserves derivability. This is the talk's wish-list item 2, and the Lean has it (`Typing/SubstitutionLemma.lean`).
- Classically, each exists in three versions.

## III.3 The classical picture: three of everything

| kind | arity | replaced by | operation | talk p.2 |
|---|---|---|---|---|
| variable `x` | `[]` | expression | substitution | `x ↦ suc 0 + y` |
| metavariable `B` | `[x]` | expression abstracted over variables | instantiation | `B ↦ x. Vec(suc x)` |
| symbol `∃` | `[A, B:[x]]` | expression abstracted over metavariables | transformation | `∃ ↦ A B. ‖Σ(x:A). B(x)‖` |

**The definitions are nested.** The bracket on the right of each line is the operation one level down:
```text
substitution    x[σ]                = σ(x)
instantiation   I_*(M(e₁,…,eₙ))     = I(M)[x₁ := I_*e₁, …, xₙ := I_*eₙ]        BHL Def 3.24
transformation  f_*(S(e₁,…,eₙ))     = f(S)[M₁ := f_*e₁, …, Mₙ := f_*eₙ]       BHL Def 6.22, PK Def 8.2.5
```

**Typical laws.** Each is proved per kind, or per pair of kinds:

| | law |
|---|---|
| L1 | `e[id] = e` |
| L2 | `x[σ] = σ(x)` |
| L3 | `e[σ][θ] = e[σ;θ]` |
| L4 | `ρ_*(σ_* t) = (ρ_*σ)_*(ρ_* t)` (talk p.3) |
| L5 | renamings are substitutions; renaming is functorial |
| L6 | `(wk e)[x:=s] = e` |
| L7 | Barendregt's lemma |
| L8 | under binders: `(λx.t)[σ] = λx. t[σ⇑]`, `id⇑ = id`, `(σ;θ)⇑ = σ⇑;θ⇑` |
| L9 | instantiation × substitution: `I_*(t[x:=s]) = (I_*t)[x := I_*s]` |
| L10 | transformation × substitution: `f_*(t[x:=s]) = (f_*t)[x := f_*s]` (BPT Prop 3; PK Lemma 8.3.2) |
| L11 | transformation × instantiation: `f_*(I_*t) = (f_*I)_*(f_*t)` (PK Lemma 8.3.3) |

**The proofs are nested too.** L10 at a translated symbol needs to commute a substitution with the instantiation inside `f(S)[M := …]`, and L9 at a metavariable needs to commute it with the substitution inside `I(M)[x := …]`.

**The typed versions are nested as well:**
- admissibility of substitution: HB Thm 3.8; BHL Lemma 5.20;
- admissibility of instantiation: HB Thm 3.13; BHL Cor 4.43, "significantly more involved — more so than one might expect";
- preservation by transformations: PK Thm 9.1.3; BHL Prop 6.25; for LF signature morphisms, Harper–Sannella–Tarlecki Prop 6.2.

## III.4 The observation: one arity, one replacement

- **The arities line up:**
  ```text
  x          : []                                   a variable takes nothing
  B          : [x]                                  a metavariable takes variables
  ∃          : [A, B:[x]]                           a symbol takes metavariables (talk p.6: its argument
                                                    information "is the same as a metavariable arity")
  eqPreserve : [S:[A, B:[x]], A, A′, B:[x], B′:[x]] a schema takes symbol-shaped arguments
  ```
  The arguments of a symbol *are* the metavariables of its formation rule, and the arguments of a metavariable are the variables it abstracts.
- **So all three replacements are Kleisli maps.** Each sends a slot of arity α to an element of `Expr(target ⋈ α)`:
  - `x ↦ suc 0 + y` is in `Expr(target ⋈ [])`;
  - `B ↦ x. Vec(suc x)` is in `Expr(target ⋈ [x])`;
  - `∃ ↦ A B. ‖Σ(A, x.B(x))‖` is in `Expr(target ⋈ [A, B:[x]])`.

  A replacement is an element of `Subst`, i.e. a Kleisli map, and the three defining clauses of III.3 are one clause:
  ```text
  z(e₁,…,eₙ)[σ] = σ(z)[ y₁ := e₁[σ], …, yₙ := eₙ[σ] ]      (y₁,…,yₙ the slots of z's arity)
  ```
  For a variable (n = 0) it reads `x[σ] = σ(x)`. For a metavariable it is BHL Def 3.24, for a symbol PK Def 8.2.5. [Lean: `act_middle`]
- **What differs is only the block.** In `Σ ⋈ Θ ⋈ Γ`:
  ```text
  operation        prefix (kept)   block (replaced)   depth (traversed)
  substitution     Σ ⋈ Θ           Γ                  bound variables
  instantiation    Σ               Θ                  Γ ⋈ bound
  transformation   1               Σ                  Θ ⋈ Γ ⋈ bound
  ```
  - Values may mention the prefix and the new block, never the depth. This is why an instantiation in BHL/HB cannot mention the variables of the context; Fiore–Hur's metasubstitution is a different split, whose values may.
  - Every slot outside the block is sent to its η-expansion, the identity.
- **Role is the block, not the rank.** One can instantiate a metavariable of symbol rank (`$` in eqPreserve, II.22) or transform a rank-1 symbol (Mal'cev, II.5). One map can also do all three at once (II.15).

## III.5 One recursion: the cascade

- In the hereditary clause, the slots `y₁…yₙ` of z's arity have smaller rank than z.
- So the action at rank r calls the action at the ranks below. Termination: lexicographic on (arity of the block, expression).
- The talk's transformation (II.16) runs ∃ (2) → B (1) → x (0): a transformation calls an instantiation, which calls a substitution.
- **Bound variables are translated through the instantiation.** In CPS (II.19), the body's bound x receives its translation `λh. h x` when the rank-1 slot b of `lam ↦ b. λk. k(λx. b(λh. h x))` is instantiated.
- **Nothing new is needed above rank 2:** eqPreserve unfolds 3 → 2 → 1 → 0 (II.22), and AllOps 4 → 3 → 2 → 1 → 0 (II.33).
- **A transformation is an instantiation one rank up.**
  - Replacing the symbol Π by Σ (a transformation) and instantiating a rank-2 metavariable S by Σ in eqPreserve are the same computation.
  - Applying a translation τ to a term t is instantiating the rank-3 slot t in `t(τ(c₁),…,τ(cₙ))` (II.23).

## III.6 One set of laws

**The relative-monad laws:**

| law | Lean |
|---|---|
| `η* = id` | `act_id` |
| `f* ∘ η = f` | `act_η` |
| `(g* ∘ f)* = g* ∘ f*` | `act_comp` |

Renamings are Kleisli maps (`act_ofRenaming`), and renaming is functorial (`Renaming.act_id`, `Renaming.act_comp`).

**The only real work is in `act_comp`.** Its hereditary case is the interchange lemma at the arity of the head:
```text
e = z(a₁,…,aₙ),  z in σ's block, of arity α
(σ;θ)* e = (θ*(σ z))[ yᵢ := (σ;θ)* aᵢ ]
θ*(σ* e) = θ*( (σ z)[ yᵢ := σ* aᵢ ] )
         = (θ*(σ z))[ yᵢ := θ*(σ* aᵢ) ]        interchange (Barendregt's lemma at arity α)
         = (σ;θ)* e                             induction on the aᵢ
```
So associativity at a head of arity α *is* the substitution lemma for that head's instantiation. The interchange lemma is proved by induction on the unordered pair of block arities. In its hereditary case the two substitutions swap roles, so the measure only requires that some entry decreases.

**The classical laws, proved once:**

| | how it follows, for blocks of every rank |
|---|---|
| L1, L2, L3 | `act_id`, `act_η`, `act_comp` |
| L4 | `act_rename`: interchange with θ a renaming (also an instance of `act_square`) |
| L5 | `act_ofRenaming`, `Renaming.act_comp` |
| L6 | `act_rename_cancel` (from `act_square`, `act_id`, `Renaming.act_eta`) |
| L7 | `act_interchange` |
| L8 | `Subst.lift` and its laws (from `act_interchange`) |
| L9, L10, L11 | `act_interchange`, with the outer substitution on the earlier block: Θ before Γ for L9; Σ before Γ for L10; Σ before Θ for L11, where `f_*I` is the pushforward |

The base lemmas, each proved by its own induction and each once for every rank and block: `act_η_right`, `act_idOfη`/`act_inst_η`, `act_interchange`, `act_copair_prefix`, `act_instId_weaken`, `act_ofRenaming`(`_prefixed`), `act_comp`, `Renaming.act_eta`, `Renaming.act_id`/`act_comp`. Nothing is repeated per kind.

**"How do we know we are not missing some laws?"** Statement for total maps (empty prefix):
```text
θₘ* ∘ ⋯ ∘ θ₁* = σₙ* ∘ ⋯ ∘ σ₁*
  ⇔  (θ₁;⋯;θₘ)* = (σ₁;⋯;σₙ)*        act_comp
  ⇔  θ₁;⋯;θₘ = σ₁;⋯;σₙ              ⇒ by act_η (f = f* ∘ η, at every depth); ⇐ trivially
  ⇔  the two composites agree at every slot
```
So no law about composites of substitutions is a new axiom: each is a computation at one slot at a time. This needs three hypotheses:
- (H1) every operation is presented as the extension of a total map: prefixed actions via `act_copair_prefix`, depth shifts via `act_lift`, renamings via `act_ofRenaming`;
- (H2) the law is stated for all expressions;
- (H3) side conditions such as "x not free in e" are presented as weakenings, which `act_rename_cancel` discharges.

The method presupposes `act_comp`, i.e. the interchange lemma, which is the irreducible base. Not covered:
- arity-changing maps;
- non-equational facts (occurrence, size);
- a completeness theorem for actions at various prefixes and depths [open: the talk's "invert the picture"].

## III.7 Across levels: translations are monad morphisms

- Syntax over a signature S is the relative monad T'_S (§I.7), whose Kleisli maps substitute the variables.
- A transformation `f : S → S′` gives a morphism of relative monads `T'_S → T'_{S′}`:
  - unit law: `act_η_right`;
  - extension law `f_*(σ_* e) = (f_*σ)_*(f_* e)`: `act_interchange`;
  - functoriality: `act_id`, `act_comp`.
- One level down, an instantiation `Θ → Θ′` gives a morphism `T'_{S⋈Θ} → T'_{S⋈Θ′}`.
- **Consequence.** PK's three relative monads (substitutions, instantiations, transformations) and the commutation lemmas between them (PK Lemmas 8.3.1–8.3.4; BPT Prop 3; Fiore–Mahmoud Lemma 5.1) all live inside one monad. One interchange lemma gives both the substitution lemma within a level and the morphism laws across levels. This is the cleanest one-sentence form of Andrej's point. [paper; ingredients Lean]

## III.8 The typed lemma, once

- **`Ambient.Filling A A′ Ω`.** A Kleisli map `fill : Subst Γ Γ′` such that every slot x of arity α is
  - either *renamed*: `fill x = η y`, with matching declaration and binding;
  - or *filled*: α is the arity of a slot of Ω, and `fill x` is well formed with the translated boundary. For an equation slot, the two translated sides must be derivably equal instead.
- **`substitutionAt Ω`.** Expressions, computed boundaries, equality of boundaries, equality of expressions, declarations, telescopes and fillings are all carried along every filling at Ω.
  - Proof: well-founded induction on Ω.
  - The hereditary case uses the hypothesis at the arity of the filled slot. It is the typed shadow of the cascade.
- **Instances:**
  ```text
  Lean                                          block filled          classical theorem
  Wf_e / Eq_e / Eq_bd / Wf_t.instantiate        the variables         admissibility of substitution (HB Thm 3.8)
                                                the rule's premises   admissibility of instantiation (HB Thm 3.13)
  Wf_sub + Wf_t / Eq_t / Wf_s / Eq_s.subst_ambient   every slot       translations preserve derivability (PK Thm 9.1.3;
                                                                      LF: HST Prop 6.2)
  Wf_sub.id, Wf_sub.comp, Wf_sub.lift           —                     theories and translations form a category;
                                                                      translations under binders
  ```
  There is no expression-level `Wf_e.subst_ambient` lemma; expression-level preservation goes through one-entry telescopes.
- **What a particular translation still has to check:** only its generating rules. Each symbol must go to a well-formed abstraction with the translated boundary, and each equation slot to a derivable equation. Examples where it fails: II.18, II.21, II.32.

## III.9 What the pattern does not give

- Arity-changing and inspecting translations (end of Part II).
- Object-level computation: the action contracts framework redexes only.
- Non-equational properties: occurrence, size. The action can blow up size non-elementarily, as normalization does.

## III.10 What was there before, and what is new

- **Adams 2008** has the raw syntax and the substitution lemma at all ranks, but never substitutes constants.
- **Boespflug–Pientka 2011** unify n levels of variables under one hereditary substitution; constants stay separate.
- **LF signature morphisms** (HST 1994; Rabe): translation preserves typing, proved once for LF, but as a notion parallel to substitution.
- **Fiore–Szamozvancev 2022** generate substitution and metasubstitution with their laws, once for every second-order signature (ranks ≤ 2).
- **Arkor–McDermott** give the categorical picture: the free CCC on one object as the initial ω-order theory, metasubstitution as substitution of a higher-order variable, translations as theory maps.
- **PK 2021** has three relative monads and asks for the unification (§11.2).
- **New here.** One simultaneous Kleisli extension that also substitutes signature symbols, at every rank, with the three law families derived once as monad laws, and the typed lemma proved once. The literature check found no source that does this.

## III.11 Mental model

- **One kind of slot:** variables, metavariables, symbols and schemas are entries of one context. Their roles are blocks.
- **One replacement:** a slot of arity α goes to an abstraction over α. The expression `x(args)` is itself `x` together with such a replacement of its arity.
- **One recursion:** replacing a rank-r slot instantiates at rank < r. The classical three levels are three unrollings, and ranks 3 and 4 are more unrollings of the same code.
- **One base lemma:** interchange. It is associativity within a level and the monad-morphism law across levels.
- **One typed lemma:** induction on rank, with the hereditary case using the hypothesis at the filled slot's arity.

---

# Appendix. Notes on existing material

**MATH.md is out of date or wrong in six places:**
- It has result types `Ty`; the Lean is classless.
- §3 says the unit laws are formalized only for the empty prefix. The right unit law holds at every prefix, and the prefixed left unit and `PrefixedSyntaxMonad` were formalized and then pruned.
- §6.1/§6.5 say the judgement layer has not been started; `Typing/` exists.
- §5.4.3's "self-contained" atomic restriction is false on the full base (I.7).
- §5.5 infers a monad from the mere existence of `Lan_J T`. ACU's Thm 4.6 needs J well-behaved.
- §7 attributes *Finitary type theories* to BHL and cites a nonexistent repository. FTT is Haselwarter–Bauer (JAR 2023), and BHL's Coq code is `peterlefanulumsdaine/general-type-theories`.

**The talk:**
- It counts rank from 0, as this note does.
- `eqPreserve` (p.8) is its rank-3 example.
- p.8 writes `B(ex)` where `B′(e x)` is meant.
- Its Agda (`Syntax.agda`) is stuck on the termination of η.
- The repository's 2021–23 Agda got η through by well-founded recursion, but not the action and composition. The Lean resolved this with (i) definitional associativity, so that arguments are literal subterms, (ii) the prefix in the action, so that the hereditary call's block is the replaced slot's arity, and (iii) well-founded recursion on arities.
