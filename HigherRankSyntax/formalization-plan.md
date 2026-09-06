# Formalization plan

The target is a **natural model** over the syntax of generalized algebraic
theories with equations: a representable natural transformation
`q : 𝒯̃₀ ⟶ 𝒯₀` of presheaves on the category of contexts, where a context is a
well-formed ambient, `𝒯₀ Γ` is the telescopes over `Γ`, and `𝒯̃₀ Γ` is the
telescopes together with a filling. Everything below is the route from the
present code to that statement. `equational-telescopes-core.md` is the
mathematical reference; section numbers cite it.

## Where the code stands

*Complete, no `sorry`.* The raw layer: the list carrier (`Carrier.lean`,
`ListCarrier.lean`), `Expr`, `Renaming`, `Subst`, `Dispatch`, `Instantiation`,
`Interchange`, `MonadLaws`, `SyntaxMonad`, and the relative-monad wrapper
`RelativeMonad/*`.

*The typing layer,* 438 lines in three files:

| file | contents |
|------|----------|
| `Typing/Boundary.lean` | `Bd` — a slot's declaration (`sort`, `of S`, `eq l r`); its renaming, substitution and instantiation; `isEq`; functoriality |
| `Typing/Telescope.lean` | `dTel` and its five structural recursions — `rename`, `actBase`/`instantiate`, `concatenate`, `declaration`, `binding` — with their computation lemmas, `slotCases`, `declaration_concatenate_inl/inr`, `boundaryOf`, `Ambient`, `Ambient.extend` |
| `Typing/Rules.lean` | the mutual block `Wf_e`, `Eq_e`, `Eq_bd`, `Wf_s`; the turnstile notations; `Wf_bd`, `Wf_t`, `Ambient.Wf`; `Wf_t.declaration` (the one standing `sorry`) |

*Not started:* §8 (the metatheory) and §§9–13 (the model).

## Standing decisions

**The carrier is the list carrier**, fixed as a global `C`; the `Carrier` record
remains as the interface. `before`, `after`, `factor`, `inclusion`, `before_inl`,
`before_inr`, `before_inclusion`, `before_of_lt` and `subWf` are now unused by the
library and could be dropped from the record; doing so means editing the structure
and its instance.

**Telescopes are inductive and declarations are stored pre-weakened.**

```lean
inductive dTel : C.Arity → C.Arity → Type where
  | nil  {Ω} : dTel Ω 1
  | cons {Ω α Δ} (binding : dTel Ω α) (boundary : Bd (Ω ⋈ α))
      (rest : dTel (Ω ⋈ C.single α) Δ) : dTel Ω (C.single α ⋈ Δ)
```

`cons` **prepends**: the first declaration takes the arguments `binding`, asserts
`boundary` — stated where its arguments are visible — and is followed by `rest`,
read over the base extended by it. Prepending is what makes every recursion
structural: each matches on `dTel Ω Δ` with both indices variables.

`declaration` and `binding` return a slot's data already weakened into the whole
telescope, so `C.before` appears in no type and nothing is transported. That a
declaration mentions only earlier entries is a theorem, not a typing constraint.

**Quotients, not setoids**, objects quotiented too. Enabled by 7.4 comparing
arities strictly, so `≈`-equal telescopes share an arity and the statements carry
no transport; 8(10) is the theorem that makes it sound.

**All six judgements are inductive, in one mutual block.** `Wf_e`, `Eq_e`,
`Eq_bd`, `Wf_s`, `Wf_bd`, `Wf_t`. `Wf_bd` and `Wf_t` were `def`s outside the block
until A7.6; they are inductives so that `Eq_e.congr` can take `Wf_t Ξ Θ` as a
premise, which the boundary half of 8(7) needs — `Wf_t` cannot be a `def` and also
appear in a constructor of the family it is defined over. `Wf_t.cons` mirrors
`dTel.cons`; `Wf_bd` has one constructor per boundary. `Ambient.Wf` and `Eq_t`
stay `def`s after the block.

**The hypothesis rule is stated in applied form.** §6.5(2) of the note concludes at
`Ξ ⋈ ⇑(Ξ.binding q)`, a compound ambient, so the rule can never be applied at a
weakened target and the system is not closed under weakening. `Eq_e.hyp` therefore
takes arguments `args` filling `Ξ.binding q` and concludes `Ξ ⊢ args ⋆ l ≈ args ⋆ r`,
at the ambient itself — the same shape as `Wf_e.ap`. The note's form is the instance
`args = Subst.instId`, recovered once 8(5) is available, so `≈` is unchanged.

**Naming.** Shapes and telescopes take upper-case Greek only; substitutions
`σ θ κ`; slots and indices lower-case. No abbreviations.

---

# Part I — the metatheory (§8)

## The dependency order

Derived from the rule shapes in `Typing/Rules.lean`, case by case. Write **W** for
weakening, **D** for `Wf_t.declaration`, **S2/S3/S4** for 8(2)/8(3)/8(4).

    raw lemmas → W → D → { 8(5) , fold(S2+S3+S4) } → 8(6), 8(7) → 8(9)–8(11)

**There is no validity obligation.** One might expect a statement *V* — the
components of a well-formed expression's computed boundary are well formed — because
S2, where the head lies in the ambient, must produce `Eq_bd Ξ B B`. It must not be
discharged by `Eq_e.refl`, which would need *V* and create the cycle
S4 → S2 → V → S3 → S4. It is discharged instead by **`Eq_e.congr`**, a *constructor*
— a rule of the system, not a theorem about it — from

- `hσ = hθ := fill`, the `Wf_s Ξ (Ξ.binding x) args` inside S3 at the same point;
- `agree`, by `Eq_e.refl` on `fill.filler z`;
- `h := Eq_e.refl` of `Wf_e (Ξ.extend (Ξ.binding x)) S`, which is **D**.

**8(5) does not wait for the fold.** `Wf_s.eta`'s `equation` premise is `Eq_e.hyp`,
whose premises are literally what `Wf_t` supplies, i.e. D.

## A7.1 — the raw layer for §8

**Done.** `dTel.rename_comp`, `binding_concatenate_inr`, `binding_concatenate_inl`,
`declaration_rename`, `binding_rename`, `concatenate_assoc`, `boundaryOf_weaken`
(**8(1)**), `boundaryOf_eta`, `Eq_t`, and `Renaming.inl_comp` restored.

Two things came out differently than planned. **`Eq_t` needs no injectivity lemma**:
defined slot-wise rather than by a double match, it never has to compare two `cons`
shapes, because a shared arity index already gives `Θ.declaration z` and
`Θ'.declaration z` the same type. It is a well-founded recursion on the slot's binding
arity under `C.subWf`, exactly the old `Eq_d`'s measure — the only well-founded
definition left in the development. And **`boundaryOf_eta` lost its right-hand side**:
it is now `(concatenate Ξ (Ξ.binding x)).boundaryOf (Expr.η x) = Ξ.declaration x`,
where the old statement carried `Bd.rename (Ξ.inclusion x ⇑ʳ α) (Ξ.boundary x)`.

The `instantiate`-versus-`rename` and `Subst.act`-versus-`rename` commutations are
deferred to A7.2, to be read off W's actual goals rather than guessed.

## A7.2 — W, weakening

**Done.** `Wf_e.weaken`, `Eq_e.weaken`, `Eq_bd.weaken`, `Wf_s.weaken` — one `mutual`
block, structural on the derivations — together with `Wf_bd.weaken`, and the
`Ambient.Renaming` structure they are stated over.

Weakening is stated for a **renaming of ambients** — a renaming of arities carrying
each slot to one binding the same entries and declared the same way — rather than for
a literal insertion. Only then is the source ambient a variable, which `cases` needs:
`Eq_e.hyp` refines the ambient, and a statement over `Ξ.extend Ψ` cannot be eliminated
against it. `Ambient.Renaming.weakenBy` and `.extend` supply the instances, and
`.extend` is what reaches the premises of `Wf_s`, which live at extended ambients.

The commutations the `Wf_s` and `Eq_e.congr` cases need all descend from one
naturality square, `act_square`, which is **associativity of Kleisli composition**
(`act_comp`) once both renamings are read as substitutions — no induction over
expressions. From it: `lift_square`, `Bd.act_square`, `dTel.actBase_square`,
`dTel.instantiate_rename`, and the two facts every `Wf_s` premise uses,
`dTel.act_declaration_rename` and `dTel.instantiate_binding_rename`.

*Notes.* Three telescopes name the three parts of the ambient — `Ξ` of arity `Δ`
before the insertion point, `Θ` of arity `Ω` inserted, `Ψ` of arity `Φ` after — so
the ambient goes from `Ξ, Ψ` to `Ξ, Θ, Ψ`, and the four statements are

    Γ, Ψ ⊢ e        Γ, Ψ ⊢ e ≡ e'      Γ, Ψ ⊢ β ≡ β'      Γ, Ψ ⊢ σ : Χ
    ──────────      ────────────────   ────────────────   ───────────────
    Γ, Θ, Ψ ⊢ e     Γ, Θ, Ψ ⊢ e ≡ e'   Γ, Θ, Ψ ⊢ β ≡ β'   Γ, Θ, Ψ ⊢ σ : Χ

with everything relabelled along `Renaming.inl Δ Ω ⇑ʳ Φ : (Δ ⋈ Φ) →ʳ ((Δ ⋈ Ω) ⋈ Φ)`
— the same slot, shifted past the inserted block. `Ψ` is relabelled as well, since a
telescope over `Ξ` must be re-read over `Ξ, Θ`; `Wf_s` relabels both the telescope
being filled and the filling. In Lean the first of the four is

```lean
Wf_e (Ξ.extend Ψ) e →
  Wf_e ((Ξ.extend Θ).extend (dTel.rename (Renaming.inl Δ Ω) Ψ))
    (⟦ Renaming.inl Δ Ω ⇑ʳ Φ ⟧ʳ e)
```

**The insertion must be in the middle, not at the end.** `Wf_s`'s premises at a slot
are stated over `Ξ.extend (dTel.instantiate σ (Θ.binding z))`, an ambient that is
already an extension, so the induction descending into them needs its hypothesis at
"`Ξ` extended by something" with the inserted block still before it. Taking `Ψ := nil`
recovers weakening at the end.

Each case moves `declaration` and `binding` across the insertion, which is exactly
what A7.1's `declaration_concatenate_inl`, `binding_concatenate_inl`,
`declaration_rename` and `binding_rename` say. The `instantiate`-versus-`rename` and
`Subst.act`-versus-`rename` commutations are to be read off the goals of the `Wf_s`
and `Eq_e.congr` cases, not guessed in advance.

## A7.3 — D, `Wf_t.declaration`

**Done.** `Wf_t.declaration`, together with `Wf_t.weaken` — 8(8) proper, a well-formed
telescope stays well formed — and `Ambient.Wf.weaken`, the form §9.3 consumes to make
`Filling Ξ (⇑Γ)` defined. `Rules.lean` is now purely definitional. Head case: `Wf_bd.weaken` along `Ambient.Renaming.weakenBy`. Tail case:
the induction hypothesis, `concatenate_assoc`, `declaration_tail`, `binding_tail`.

## A7.4 — 8(5), the variable rule

**Done.** `Wf_e.eta` and `Wf_s.eta`, in `Typing/Eta.lean`, together with the lemmas
they rest on: `dTel.actBase_id`, `dTel.actBase_comp` (`actBase` is functorial),
`dTel.rename_id`, `dTel.instantiate_rename_inl`, `Bd.act_instId_weaken`,
`dTel.act_declaration_instId`, `dTel.instantiate_binding_instId`, `Wf_bd.refl` and
`Wf_t.binding`.

They are **not** structural but a mutual well-founded recursion, measure `(arity, tag)`
lexicographic with `C.subWf` on the arity: `Wf_e.eta` at `α` calls `Wf_s.eta` at the
same `α` (tag decreases), and `Wf_s.eta` at `Ω` calls both at a slot's binding arity
`Λ < Ω` via `⟨z⟩`. `Θ.binding z` is produced by a recursion, so it is not a structural
subterm and no plain induction would be accepted.

`declared` needed reflexivity of `Eq_bd` at a well-formed declaration — `Wf_bd.refl`,
three lines from `Eq_e.refl` — not the `Eq_e.congr` route the earlier design needed.
`equation` applies `Eq_e.hyp` at the slot `C.inl (C.inr z)` of the doubly extended
ambient with `Subst.instId` as its arguments, and `act_instId_weaken` collapses the
conclusion back to `l ≈ r`.

## A7.5 — the fold: 8(2), 8(3), 8(4) — **done**

*Produces.* `Typing/SubstitutionLemma.lean`. Five transports, one for each judgement,
stated over a **filling of ambients** `Ambient.Filling A A' Ω` — a substitution
that at every slot is either the η of a slot carrying the same declaration and the
same entries bound, both under the substitution, or a filler for the slot's
declared boundary, the filled slots having arities below `Ω`. This stands to
substitution as `Ambient.Renaming` stands to weakening, and for the same reason:
the source ambient must be a variable for the induction to case on the derivation.

The five (`Wf_e.subst_step`, `boundaryOf_subst_step`, `Eq_e.subst_step`,
`Eq_bd.subst_step`, `Wf_s.subst_step`) are one **structural** recursion over the
derivations. The block-arity drop — at a filled head the argument passes to the
entries that head binds — is an **outer** well-founded induction on `Ω` under
`C.subWf` (`substitutionAt`), because a derivation cannot appear in a
`termination_by` measure. `SubstitutionAt Ω` bundles the five statements at `Ω`.

Filling a literal block is `Wf_s.filling` (a filling of a telescope is a filling
of the ambient it extends) composed with `Ambient.Filling.extend`; the concrete
corollaries are `Wf_e.subst`, `Eq_e.subst`, `Eq_bd.subst`, `boundaryOf_subst`,
`Wf_s.subst`.

*Notes.* 8(2) carries one further hypothesis: that the transported source
boundary is equal to itself. At an η-head the two boundaries are equal on the
nose, and `Eq_bd` still needs a witness — which an ambient with an ill-formed
declaration does not have. Callers obtain it from `Eq_bd.trans h h.symm` on the
`declared` field they already hold. Well-formedness of the ambient is *not* a
hypothesis of any of the five, which is what keeps them independent of 8(9).

## A7.6 — the judgement block, 8(6), 8(7) — **done**

`Wf_bd` and `Wf_t` are inductives in the mutual block, with `Wf_bd.eq_left`,
`Wf_bd.eq_right`, `Wf_bd.eq_boundary` as the projections the old `∧`-form gave for
free. `Wf_bd.weaken`, `Wf_t.weaken`, `Wf_t.declaration`, `Wf_t.binding` and
`Wf_bd.refl` recurse on the derivation rather than on the telescope.

```lean
theorem Eq_e.ap (hΞ : Ambient.Wf Ξ) (x : Δ ∋ α) (args args' : Subst α Δ)
    (h : Ξ ⊢ Expr.ap x args) (h' : Ξ ⊢ Expr.ap x args')
    (agree : ∀ ⦃Λ⦄ (z : α ∋ Λ), ¬ (args ⋆ (Ξ.binding x).declaration z).isEq →
        Ξ ⋈ args ⋆ (Ξ.binding x).binding z ⊢ args z ≈ args' z) :
    Ξ ⊢ Expr.ap x args ≈ Expr.ap x args'

theorem Eq_e.wf_left  : ∀ {e e' : Expr Δ}, Ξ ⊢ e ≈ e' → Ξ ⊢ e
theorem Eq_e.wf_right : ∀ {e e' : Expr Δ}, Ξ ⊢ e ≈ e' → Ξ ⊢ e'
theorem Eq_e.boundaryOf : ∀ {Δ} {Ξ : Ambient Δ}, Ambient.Wf Ξ →
    ∀ {e e' : Expr Δ}, Ξ ⊢ e ≈ e' → Ξ ⊢ Ξ.boundaryOf e ≈ Ξ.boundaryOf e'
```

All three live in `SubstitutionLemma.lean`, since 8(7) consumes the fold's
corollaries and pairs with `boundaryOf_refl`. 8(6) is one application of
`Eq_e.congr` to `Eq_e.refl (Wf_e.eta …)` and `ap_eq_act_η` on both sides — the
note's second raw lemma is unnecessary because `binding` is pre-weakened. The two
well-formedness halves of 8(7) need no hypotheses: `hyp` and `congr` are both
`Wf_e.instantiate`.

`Eq_e.boundaryOf` is what forced `Eq_e.congr` to carry `Wf_t Ξ Θ` (A7.7): its
`refl` clause needs `boundaryOf_refl`, hence a well-formed ambient, and its
`congr` clause then needs `Ambient.Wf (Ξ ⋈ Θ)`, which `Wf_s Ξ Θ σ` does not give.
Auxiliaries added along the way: `Wf_e.instantiate`, `boundaryOf_instantiate`
(8(3), 8(2) with no suffix — the note's own form), `Eq_bd.congr`,
`Wf_t.concatenate`, `Wf_s.agree`, `dTel.concatenate_nil`.

## A7.7 — 8(9) in the fold — **done**; then 8(10), 8(11)

**Done:** `Eq_e.congr` carries `(hΘ : Wf_t Ξ Θ)`. The fold has seven members: the
five of A7.5 plus `Wf_bd.subst_step` and `Wf_t.subst_step`, recursing on their own
derivations; `SubstitutionAt` gained the fields `declaration` and `telescope`. The
new premise is supplied at its two use sites by `Wf_t.weaken` and
`Wf_t.subst_step` — which is why the rule change and the two members had to land
together. `Wf_bd.weaken` and `Wf_t.weaken` moved into the weakening block for the
same reason. Exported: `Wf_t.subst`, 8(9)'s first half.

```lean
theorem Wf_t.subst (hσ : Wf_s Ξ Θ σ) {Λ : C.Arity} {T : dTel ((Δ ⋈ Ω) ⋈ Φ) Λ}
    (h : Wf_t (Ξ ⋈ Θ ⋈ Ψ) T) : Wf_t (Ξ ⋈ σ ⋆ Ψ) (σ ⋆ T)
```

*Produces.* 8(9)'s second half — for one `Θ` with `Ξ ⊢ Θ`, two well-formed `σ, θ`
agreeing up to `≈` at every non-equational slot give `σ ⋆ Θ ≈ θ ⋆ Θ`; 8(10)
invariance of every judgement under an `≈`-equal ambient; 8(11) that `≈` on
telescopes, `∼` on fillings and 13.1's heterogeneous comparison are equivalences.

*Needs.* The fold; `Eq_t` from A7.1.

*Notes.* 8(10) is what makes the quotients sound and so must land before Part II.
8(11) is not immediate from 8(10): symmetry of `∼` compares components in two
different ambients, so it needs 8(9)'s second half, by induction over the slots in
order.

---

# Part II — the model (§§9–13)

## B1 — contexts and fillings (§9)

*Produces.* `Filling Ξ Θ` as the well-formed substitutions filling `Θ`; the
relation `∼` of 9.2, comparing components at non-equational slots only; the
category `Ctx` with well-formed ambients as objects and fillings of the weakened
codomain as morphisms; identity by 8(5) and composition by 8(4).

*Needs.* All of Part I.

*Notes.* Take the quotient here, objects included; 8(10) is what licenses it.
Equational slots are deliberately not compared: nothing constrains them (6.3) and
nothing depends on them.

## B2 — telescopes over a context (§10)

*Produces.* `𝒯₀ : Ctxᵒᵖ ⥤ Type`, the well-formed telescopes over a context modulo
`≈`; the extension `Γ ⋈ Θ` as an object of `Ctx`; the projection and its
universal property.

*Needs.* B1, 8(9).

## B3 — the monoid of telescopes (§11)

*Produces.* `TelFam := Over 𝒯₀`, telescope-shaped presheaves; the tensor
`(M ⊗ N) Γ := Σ (m : M Γ), N (Γ ⋈ shape m)` with unit `I Γ := PUnit`; the
associator and unitors; `𝒯₀` as a monoid object.

*Needs.* B2.

*Notes.* This is the semantic counterpart of `ArityMod` in
`RelativeMonad/ArityModuleTensor.lean`, with the constant module of raw arities
replaced by `𝒯₀`. The old `dTelMon` section stated the raw analogue over the
previous `dTel` and was deleted with its file; rebuild it here if it is wanted.

## B4 — expressions and boundaries (§12)

*Produces.* `ℰ₀ Γ` the well-formed expressions modulo `≈` and `ℬ₀ Γ` the
boundaries modulo `≈`, both presheaves with `σ ⋆ −` as the action; the natural
transformation `boundaryOf : ℰ₀ ⟶ ℬ₀`; `ℰ₀` as an object of `PSh(Ctx)/ℬ₀`.

*Needs.* 8(2), 8(3), 8(7), clause 6.5(3).

## B5 — the natural model (§13)

*Produces.* `𝒯̃₀ Γ := Σ (Θ : 𝒯₀ Γ), Filling Γ Θ` with the dependent equivalence of
13.1; `q := fst : 𝒯̃₀ ⟶ 𝒯₀`; the proof that `q` is representable — every pullback
of `q` along a representable is representable, the pullback of `𝒯̃₀ ⟶ 𝒯₀` along
`よΓ` being `よ(Γ ⋈ Θ)`.

*Needs.* B1–B4, 8(11) for the equivalence, 8(10) for the pullback square.

*Notes.* 13.1's relation varies the telescope as well as the filling, so it is not
9.2's `∼`; it typechecks because 7.4 forces equal arities.

## Open questions

Semantics beyond the syntactic model, and how a named theory such as MLTT sits in
the framework, are §15 of `equational-telescopes-core.md`.
