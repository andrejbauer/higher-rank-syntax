# Initiality: formalization plan

`Ctx.model : HrS.Structure` (`Ctx/Model.lean`) is complete. What remains: for
every `M : HrS.Structure`, exactly one `HrS.Morphism Ctx.model M`, as a `def`,
with no choice in any definition.

Marks as in `initiality.md`: `[proved]`, `[routine]`, `[sorry]`, `[open]`.

---

## Why the interpretation is a relation first

A function on raw syntax landing in `M` cannot be defined directly. Two
clauses need a semantic equation that is a soundness fact about the function
being defined:

```text
Wf_bd.eq    heq : Eq_bd (Ξ ⋈ Θ) (boundaryOf l) (boundaryOf r)
            M.IdElement ⟦l⟧ ⟦r⟧ needs ⟦l⟧ ⟦r⟧ : M.Tm Γ (M.El s) at ONE s;
            heq gives Eq_e S S' for the two sorts, so ⟦S⟧ = ⟦S'⟧ is needed.

Wf_s.cons   equation : Eq_e (Ξ ⋈ bind) l r          at an equational slot
            the filler must be a term of M.IdX ⟦l⟧ ⟦r⟧, so ⟦l⟧ = ⟦r⟧ is needed.
```

Soundness cannot be interleaved with the definition: `Eq_e.congr` over `Ξ` has
a premise over `Ξ ⋈ Θ` for an arbitrary `Θ`, so no measure shrinks the
ambient. The `of S` clause is fine by itself — `Eq_bd` relates boundaries of
one constructor and `Bd.act` preserves constructors, so `hsort` yields
`boundaryOf S = .sort` syntactically — which is why a tag-and-default design
looked close; it fails on the two clauses above. Type-valued judgements would
need Type-valued twins of `Weakening.lean` and `SubstitutionLemma.lean`.

**So: define the graph, then recompute the witness.**

1. `Sem*` are mutual inductive predicates, one constructor per syntactic form,
   indexed by the value. "Both at the same `s`" is an index shared by two
   premises, not a test.
2. Existence and soundness are one mutual induction on the seven judgements,
   in `Prop`.
3. The recursor recomputes the value from the syntax, taking `∃ T, Sem e T`
   as a `Prop` argument and returning `Σ T, Sem e T`:

```lean
interpTm (I : SemCtx Ξ) (e : Expr Δ) (h : ∃ T, SemTm Ξ e T) : Σ T, SemTm Ξ e T
```

At the two clauses above, `h` is inverted to a `Prop`, the recursive calls
return certified values, and functionality of `Sem` turns the certificates into
the equation the transport needs. No `Classical.choose`: `Sem` is functional
and its value is computable from the syntax, so the `∃` only justifies
transports. The output is certified, so `Quotient.lift` descends by soundness,
and the morphism is a `def`.

(`Ctx.model` already lists `Classical.choice` among its axioms through Mathlib
proof terms; an axiom-clean development would be a separate audit. What is
guaranteed here is that no definition uses choice.)

---

## The semantic side of telescopes

A chain carrying each entry's binding chain in its type is induction–recursion.
A bare chain of types, followed by a decoration *indexed by* the bare chain, is
not: `Bind` is defined on the shadow before the decoration exists.

```lean
inductive Chain (M : HrS.Structure) : M.Ob → C.Arity → M.Ob → Type
  | nil  {Γ} : Chain Γ 1 Γ
  | cons {Γ α Δ Γ'} (A : M.Ty Γ) (c : Chain (M.extend Γ A) Δ Γ') :
      Chain Γ (C.single α ⋈ Δ) Γ'

def Chain.Bind : Chain Γ Ω Γ' → M.Ty Γ' → M.Ty Γ            -- recursion on the chain

inductive Tele (M : HrS.Structure) : {Γ Ω Γ'} → Chain M Γ Ω Γ' → Type
  | nil  {Γ} : Tele (Chain.nil (Γ := Γ))
  | cons {c_b : Chain Γ α Γ_b} (d_b : Tele c_b) (B : M.Ty Γ_b) (A : M.Ty Γ)
      (hA : A = Chain.Bind c_b B) {c : Chain (M.extend Γ A) Δ Γ'} (d : Tele c) :
      Tele (Chain.cons A c)
```

The arity index is phantom semantically; it makes `Tele.slot` the recursion of
`dTel.declaration`, by `C.split`. As with `dTel`, `cases` on a decoration at a
concrete arity fails dependent elimination; inversions are written as matches
with the chain as a variable index, both branches present. `Tele.slot d x`
returns the slot's binding decoration and declaration type reindexed along the
projections of the entries after it, with `A_x = Bind c_x B_x` and the variable
`v_x`: exactly what the `ap` clause must `unlam` against.

---

## The relations

Mutual inductive predicates, indexed by the value:

```text
SemTele Ξ Θ   (Γ : M.Ob) (d : Tele c)                    Θ over Ξ, starting at Γ
SemBd   Ξ Θ β (B : M.Ty Γ')                              the declaration at the end of Θ
SemTm   Ξ e   ⟨Γ, a, t⟩                                  one Σ index
SemSub  Ξ Θ σ (d : Tele c) (s : M.Sub Γ Γ')              a section of c.projection
SemAmb  Ξ     := SemTele .nil Ξ M.empty
```

The `ap` constructor:

```text
SemAmb  Ξ d                                   d : Tele c,  c : Chain M.empty Δ Γ
d.slot x = ⟨d_x, B_x, A_x, v_x, hA⟩            read off, weakened over the rest
SemSub  Ξ (Ξ.binding x) args d_x s            s : M.Sub Γ Γ_x
──────────────────────────────────────────────────────────────────────
SemTm Ξ (ap x args) ⟨Γ, substTy B_x s, substTm (c_x.unlam (hA ▸ v_x)) s⟩
```

`SemBd.of` demands `SemTm (Ξ ⋈ Θ) S ⟨Γ', M.U Γ', s⟩` and yields `M.El s`;
`SemBd.eqEl` demands both sides at `M.El s` for one `s`; `SemSub.cons` at an
equational entry has the premise `tl = tr` and the filler `IdX_refl` transported
along it. Functionality, `SemTm Ξ e T → SemTm Ξ e T' → T = T'`, is induction on
one derivation and inversion on the other; every syntactic form has one
constructor.

---

## Passes

**1. Chains and decorations.** `HrS/Chain.lean`. `Chain`, `concatenate`
(strictly associative), `projection`, `Bind`, `lam`, `unlam` (inverse), `subst`
with `lift` and the square with the projections, `Bind_subst` and `lam_subst`
iterated, `pair` (a section of `cons A c` from a term of `A` and a section of
`c` reindexed along the pairing). Then `Tele`, `Tele.subst`, `Tele.slot`,
`Tele.concatenate`. Pure `M`, no syntax. `[open]`

**2. Relations.** `Initiality/Relation.lean`. The mutual inductive above, its
inversion lemmas, functionality, and concatenation:
`SemAmb (Ξ ⋈ Θ) (d ++ d_Θ) ↔ SemAmb Ξ d ∧ SemTele Ξ Θ d_Θ`. `[open]`

**3. Weakening and slots.** `Initiality/Weakening.lean`. Renaming along
`Ambient.Renaming.weaken` and its `extend`s is reindexing along
`Chain.projection`; hence, for `SemAmb Ξ d`, `d.slot x` is the interpretation
of `Ξ.binding x` and `Ξ.declaration x`. Mirrors `Wf_t.declaration` and
`Wf_t.binding` (`Typing/Weakening.lean:274,312`). `[open]`

**4. Substitution.** `Initiality/Substitution.lean`. Interpreting a substituted
expression, boundary, telescope or filling is the interpretation reindexed
along the lifted chain substitution; instantiation as the `copair` case. Same
recursion as `Subst.act` (lexicographic on the block arity and `Expr.Subterm`)
and the same `threeway` split; mirrors `substitutionAt`
(`Typing/SubstitutionLemma.lean:222–560`). The boundary form is what `SemBd.of`
needs at existence. Largest item; three passes. `[open]`

**5. Existence and soundness.** `Initiality/Soundness.lean`. One mutual
induction on `Wf_e, Eq_e, Eq_bd, Wf_s, Eq_s, Wf_bd, Wf_t` under `Ambient.Wf Ξ`
and `SemAmb Ξ d`:

```text
Wf_*  ⟹  ∃ value, Sem* value
Eq_*  ⟹  Sem* at either side gives one value
```

`Eq_e.hyp` is `IdSort_reflect` / `IdElement_reflect` at the slot's variable
after `unlam`; `Eq_e.congr` is pass 4. `[open]`

**6. Recomputation.** `Initiality/Interp.lean`. `interpTm`, `interpSub` mutual,
then `interpTele`, `interpBd`; each takes the ambient's decoration with its
`SemAmb` certificate and an `∃` hypothesis, returns a `Σ` with certificate.
Termination on `Expr.Subterm` with the filled telescope's length, the parent
expression carried as a ghost argument, as `Subst.act` carries its block arity.
`[open]`

**7. Descent and the morphism.** `Initiality/Morphism.lean`. `Quotient.lift`
of pass 6 over `Ob`, `Ty₁`, `Tm₁`, `⟶`, respect by soundness of `Eq_t`, `Eq_s`,
`Eq_e` with functionality, through the quotient tower of `Ctx/`; the 22 fields,
each a `Sem` fact on representatives. `onSub` is `Chain.lift` after the
section, for a filling of the target's ambient weakened from arity `1`. `[open]`

**8. Uniqueness.** `Initiality/Uniqueness.lean`. Any `F : Morphism Ctx.model M`
satisfies `Sem` with the values `F.onOb [Ξ]`, `F.onTy [e]`, …, where `[−]` is
the class in `Ctx`: induction on raw syntax, each step one `_mk` lemma of the
model (`Bind_mk`, `lam_mk`, `El_ofFill`, `pair_mk`, `lift_mk`, …) followed by
the matching `on*` law of `F`. Functionality then gives `F = ⟦−⟧`. `[open]`

**9. The statement.** `Unique (HrS.Morphism Ctx.model M)`, a `def`. `[open]`

---

## Sequencing and size

1 → 2 → 3 → 4 → 5 → 6 → 7 → 9; 8 needs 2, 3 and 7. Pass 4 is the risk and can
start after 2 while 3 is open. The whole is of the order of `Typing/`: passes
3–5 are semantic twins of `Weakening.lean` and `SubstitutionLemma.lean`, pass 6
is the price of computability, and pass 7 reuses the quotient tower of `Ctx/`.
