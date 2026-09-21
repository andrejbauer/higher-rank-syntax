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

*The typing layer,* with the substitution, invariance and telescope-agreement
proofs complete:

| file | contents |
|------|----------|
| `Typing/Boundary.lean` | `Bd` — a slot's declaration (`sort`, `of S`, `eq l r`); its renaming, substitution and instantiation; `isEq`; functoriality |
| `Typing/Telescope.lean` | `dTel` and its five structural recursions — `rename`, `actBase`/`instantiate`, `concatenate`, `declaration`, `binding` — with their computation lemmas, `slotCases`, `declaration_concatenate_inl/inr`, `boundaryOf`, `Ambient`, `Ambient.extend` |
| `Typing/Rules.lean` | the seven mutual judgements `Wf_e`, `Eq_e`, `Eq_bd`, `Wf_s`, `Eq_s`, `Wf_bd`, `Wf_t`; the turnstile notations; `Ambient.Wf`; prefix-structured `Eq_t` and `Eq_t.Both` |
| `Typing/Weakening.lean` | weakening, well-formed declarations and bindings, telescope reflexivity, and equality under concatenation |
| `Typing/Eta.lean` | well-formed generic expressions and identity fillings |
| `Typing/SubstitutionLemma.lean` | substitution for the judgements; `Wf_sub`, `Eq_sub`, their lifting lemmas, and agreement for expressions and boundaries |
| `Typing/Invariance.lean` | invariance under equal ambients; `Eq_t.Both.symm`, `Wf_sub.ofBoth`, and `Eq_t.agree` |

*Next:* §8(11), equivalence relations on telescopes and fillings.
*Not started:* §§9–13 (the model).

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

**All seven judgements are inductive, in one mutual block.** `Wf_e`, `Eq_e`,
`Eq_bd`, `Wf_s`, `Eq_s`, `Wf_bd`, `Wf_t`. `Wf_bd` and `Wf_t` were `def`s outside
the block until A7.6; they are inductives so that `Eq_e.congr` can take `Wf_t Ξ Θ`
as a premise, which the boundary half of 8(7) needs — `Wf_t` cannot be a `def` and
also appear in a constructor of the family it is defined over. `Eq_s Ξ Θ σ θ`
(notation `Ξ ⊢ σ ≈ θ : Θ`) is the agreement of two fillings at every
non-equational slot — the note's `∼` of 9.2 — and is inductive for the same
reason: it is the `agree` premise of `Eq_e.congr`. It is not visibly symmetric,
its slot premises being stated over the ambient built from `σ`; `Eq_s.symm` waits
on 8(10). `Wf_t.cons` mirrors `dTel.cons`; `Wf_bd` has one constructor per
boundary. `Ambient.Wf` stays a `def` after the block.

**`Eq_t` is a prefix-structured recursive `def`.** It recurses on its first
telescope and asserts a matching decomposition of the second; `Eq_t.nil` and
`Eq_t.cons` provide its constructor interface (see A7.8). It mirrors `Wf_t`: `Eq_t.cons`
compares the two declarations over `Ξ ⋈ bind`, the ambient built from the entries
the slot binds and the slots preceding it, and compares the tails over
`Ξ ⋈ dTel.cons bind boundary .nil`. The earlier form — a `def` reading
`declaration` and `binding` off the whole telescope, so comparing declarations
over `Ξ ⋈ Θ ⋈ Θ.binding z` — makes 8(10) false: at a slot `q` with
`Ξ.declaration q = .eq l r` binding nothing, the ambient `Ξ ⋈ Ξ.binding q`
proves `l ≈ r` by the hypothesis rule at `q` itself, so `.eq l r` is equal there
to `.eq l l`, and an ambient declaring the latter does not prove `l ≈ r`. The
weak form is recovered as `Eq_t.declaration` and `Eq_t.binding`, by weakening.

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
`Wf_t.concatenate`, `Wf_s.refl`, `dTel.concatenate_nil`.

## A7.7 — 8(9), substitution and telescope agreement — **done**

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

**Also done:** `Wf_t.refl` (a well-formed telescope is equal to itself) and
`Eq_t.subst` — `≈` on telescopes is stable under filling a block:

```lean
theorem Eq_t.subst (hσ : Wf_s Ξ Θ σ) {Φ : C.Arity} {Ψ : dTel (Δ ⋈ Ω) Φ} {Χ : C.Arity}
    {X X' : dTel ((Δ ⋈ Ω) ⋈ Φ) Χ} (h : Eq_t (Ξ ⋈ Θ ⋈ Ψ) X X') :
    Eq_t (Ξ ⋈ σ ⋆ Ψ) (σ ⋆ X) (σ ⋆ X')
```

`Wf_t.refl` recurses on the `Wf_t` derivation; `Eq_t.filling` on the first telescope.
`Eq_t.subst` is `Eq_t.filling` — `Eq_t A T T' → Eq_t A' (F.fill ⋆ T) (F.fill ⋆ T')`
for `F : Ambient.Filling A A' Ω` — at `Wf_s.fillBefore Ψ`; the boundary component
of a `cons` is `(substitutionAt Ω).boundaryEquality (F.extend bind)`, brought into
shape by `Bd.act_lift_depth`.

**Substitutions between ambients — done:** `Wf_sub A A' σ` (6.8) and
`Eq_sub A A' σ θ`, with `Eq_e.agree` (agreeing substitutions send a well-formed
expression to `≈`-equal ones), and 8(3), 8(9) in that form —
`Wf_e.subst_ambient`, `Wf_t.subst_ambient`. The raw bridges they rest on:
`act_copair_inr`, `Subst.instantiate_weaken`, `dTel.instantiate_weaken`,
`Renaming.fromUnit_extend`, and the right-weakening renaming of ambients
`Ambient.Renaming.weakenInto`.

**Also done:** `Wf_sub` and `Eq_sub` are stated slotwise, over the source
ambient's own declarations, with `Wf_sub.toFilling` / `Eq_sub.toAgreement`
converting to the `Wf_s A' (⇑A) σ` form the rules consume. That is what makes
`Wf_sub.lift` and `Eq_sub.lift` routine — at a source slot the conditions are
`hσ`'s weakened along `Ambient.Renaming.weaken A' (σ ⋆ T)`, at a new slot they are
`Wf_s.eta`'s, with `Bd.act_square`/`dTel.actBase_square` fed by `Subst.lift_inl`
doing the matching. Also landed: `Eq_bd.agree`, and the bridges
`Subst.act_weaken`, `Bd.act_weaken`, `dTel.rename_concatenate`,
`Renaming.eq_fromUnit`, `Ambient.weaken_concatenate`,
`Ambient.weaken_declaration`, `Ambient.weaken_binding`.

**Telescope agreement — done, using A7.8:** `Eq_t.agree` in
`Typing/Invariance.lean` has type

```lean
theorem Eq_t.agree {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    {σ θ : Subst Γ Γ'} (hA : Ambient.Wf A) (hA' : Ambient.Wf A')
    (hσ : Wf_sub A A' σ) (hθ : Wf_sub A A' θ) (hst : Eq_sub A A' σ θ) :
    ∀ {Χ : C.Arity} {T : dTel Γ Χ}, Wf_t A T → Eq_t A' (σ ⋆ T) (θ ⋆ T)
```

The proof recurses structurally on `Wf_t`. At a `cons`, it first compares the
substituted bindings recursively. `Eq_t.toBoth` and `Eq_t.Both.concatenate`
then compare the extended ambients. `Eq_t.Both.symm` reverses that comparison,
and `Wf_sub.ofBoth` moves the lifted `θ` into the `σ`-extended ambient.
`Eq_bd.agree`, `Wf_bd.refl` and `Bd.act_lift_depth` compare the boundaries.
The binding and boundary comparisons assemble equality of the singleton heads;
the same transport now permits recursion on the tail. Both recursive calls are
on subderivations, with no call on the assembled singleton head.

`hA'` supplies reflexivity of the target ambient when extending each telescope
equality to an ambient equality. Removing that hypothesis would require a
stronger invariance interface. `Wf_sub.ofBoth` itself only needs well-formedness
of the source and the given equality of targets; its declared-boundary clause
uses `boundaryOf_ofBoth` followed by `Eq_bd.ofBoth`.

*Next.* 8(11): `Eq_t.symm` and `Eq_t.trans`, then equivalence of `∼` on fillings
and of 13.1's heterogeneous comparison. The completed invariance and agreement
lemmas supply the required changes of ambient.

*Needs.* The fold; `Eq_t` from A7.1; invariance from A7.8.

*Notes.* 8(10) is what makes the quotients sound and so must land before Part II.
8(11) is not immediate from 8(10): symmetry of `∼` compares components in two
different ambients, so it needs 8(9)'s second half, by induction over the slots in
order.

## A7.8 — 8(10), invariance under an equal ambient — **done**

*The prefix discipline, completed.* The note restricts to the entries preceding a
slot in all three telescope-level notions. `Wf_t` always did; `Eq_t` was corrected
first (the whole-telescope reading makes 8(10) false — see below); `Wf_s` now does
too:

```lean
inductive Wf_s : {Δ Ω : C.Arity} → Ambient Δ → dTel Δ Ω → Subst Ω Δ → Prop where
  | nil : Wf_s Ξ .nil σ
  | cons (equation : ∀ l r, boundary = .eq l r → Eq_e (Ξ ⋈ bind) l r)
      (filler : ¬ boundary.isEq → Wf_e (Ξ ⋈ bind) (σ (C.inl (C.singleSlot α))))
      (declared : ¬ boundary.isEq →
          Eq_bd (Ξ ⋈ bind) ((Ξ ⋈ bind).boundaryOf (σ (C.inl (C.singleSlot α)))) boundary)
      (hrest : Wf_s Ξ (dTel.instantiate (fun ⦃_⦄ i => σ (C.inl i)) rest)
                     (fun ⦃_⦄ j => σ (C.inr j))) :
      Wf_s Ξ (dTel.cons bind boundary rest) σ
```

Filling a telescope runs over its slots in order, the head filler being
substituted into the declarations that follow.  The slotwise reading is recovered
as `Wf_s.equation`, `Wf_s.filler`, `Wf_s.declared` and built by `Wf_s.slotwise`
(via `Wf_s.slotwise_actBase`, which generalizes the base substitution so the
recursion at `dTel.instantiate` is structural).  Both directions rest on
`Subst.copair_split` — filling a two-block arity is filling the first block then
the second — with `act_comp`, and on `dTel.declaration_head_instantiate`,
`dTel.binding_head_instantiate`, `dTel.declaration_tail_instantiate`,
`dTel.binding_tail_instantiate`.  `Wf_s.weaken` and `Wf_s.subst_step` were rewritten
on the new structure and both roughly halved: their head premises are unfilled, so
they reduce to `Eq_e/Wf_e/Eq_bd.weaken` at `ι.extend bind` resp. `…subst_step` at
`F.extend bind`, mirroring `Wf_bd.weaken` and `Wf_bd.subst_step`.

*`Eq_t` is a `def`, not an inductive.* Two families indexed by the same telescope
arity cannot be inverted together: after matching one, the other needs
`1 = C.single α ⋈ Ω` refuted or `C.single α ⋈ Ω = C.single α' ⋈ Ω'` solved, and
`C.Arity` has no constructors; the inversion lemma cannot even be proved, for the
same reason.  `Wf_s`, `Wf_t` and `Eq_s` must stay inductive — each is a premise of
a rule — and `Eq_t` is a premise of none, so it is the one that can be a
computation:

```lean
def Eq_t : {Δ Ω : C.Arity} → Ambient Δ → dTel Δ Ω → dTel Δ Ω → Prop
  | _, _, _, .nil, Θ' => Θ' = .nil
  | Δ, _, Ξ, .cons bind boundary rest, Θ' =>
      ∃ bind' boundary' rest', Θ' = dTel.cons bind' boundary' rest' ∧
        Eq_t Ξ bind bind' ∧ Eq_bd (Ξ ⋈ bind) boundary boundary' ∧
        Eq_t (Ξ ⋈ dTel.cons bind boundary .nil) rest rest'
```

Structural on the first telescope; the second stays a variable and its
decomposition is asserted propositionally, so it is read off by `obtain` and never
inverted.  `Eq_t.nil`, `Eq_t.cons`, `Eq_t.nil_inv`, `Eq_t.cons_inv` keep the
interface, and `Eq_t.weaken`, `Eq_t.concatenate`, `Eq_t.declaration`,
`Eq_t.binding`, `Eq_t.filling`, `Wf_t.refl` recurse on the telescope.

*Both readings.* `Eq_t` compares declarations over the ambient built from its
first telescope; `Eq_e.hyp` and `boundaryOf` need them over the second.
`Eq_t.Both Ξ Ξ' Θ Θ'` is `Eq_t` with both comparisons, again a `def` on the first
telescope, with `nil`/`cons`/`nil_inv`/`cons_inv`, `toEq_t`, `weaken`,
`concatenate`, `declaration_right`, `binding`, `filling` (one filling per side).

*Produces.* `Typing/Invariance.lean`: `Eq_bd.isEq`, then a nine-member mutual block
over `Eq_t.Both`, recursing structurally on the judgement —

```lean
Wf_e.ofBoth, boundaryOf_ofBoth, Eq_e.ofBoth, Eq_bd.ofBoth, Wf_s.ofBoth,
Eq_s.ofBoth, Wf_bd.ofBoth, Eq_t.Both.refl, Wf_t.ofBoth
```

then `Eq_t.toBoth`, which turns `Eq_t` into `Eq_t.Both` by recursion on the
telescope using the completed block, and the corollaries `Wf_e.ofEq`, `Eq_e.ofEq`,
`Eq_bd.ofEq`, `Wf_t.ofEq`, `Wf_s.ofEq`.  No `sorry`; the development depends only
on `propext`, `Classical.choice`, `Quot.sound`.

`Wf_s.ofBoth` matches the `Wf_s` derivation alone and reads `Eq_t.Both` off by
`cons_inv`; its head premises are unfilled, and its tail step is
`Eq_t.Both.filling (Wf_s.filling hκ) (Wf_s.filling hκ') rfl hrest'` with
`hκ : Wf_s A (dTel.cons bind boundary .nil) (σ ∘ inl)` and `hκ'` its transport —
the prefix filling on each side, which is what the `Wf_s` refactor was for.
`Wf_bd.ofBoth` takes `Eq_t.Both A B T T` rather than `Wf_t A T`, so that
`Eq_t.Both.refl` can be a member of the block rather than a prior theorem.

*Counterexample for the old `Eq_t`.* Reading declarations off the whole telescope,
at a slot `q` with `Ξ.declaration q = .eq l r` binding nothing, the ambient
`Ξ ⋈ Ξ.binding q` proves `l ≈ r` by the hypothesis rule at `q` itself, so
`.eq l r` is equal there to `.eq l l`; an ambient declaring the latter does not
prove `l ≈ r`.

*A factorization that is not available.* Splitting `Eq_t` into a binding-change
followed by a declaration-change fails at the first step: the binding-change
relation

```lean
inductive Eq_t.Binding : {Δ Ω : C.Arity} → Ambient Δ → dTel Δ Ω → dTel Δ Ω → Prop
  | nil | cons (hbind : Eq_t.Binding Ξ bind bind')
      (hrest : Eq_t.Binding (Ξ ⋈ dTel.cons bind boundary .nil) rest rest') : …
```

is equality — `Eq_t.Binding.eq`.  A `dTel` is its bindings, boundaries and tail,
so keeping every boundary strict while relating the bindings recursively leaves
nothing free.  `Eq_t` is generated by declaration-changes alone.

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
