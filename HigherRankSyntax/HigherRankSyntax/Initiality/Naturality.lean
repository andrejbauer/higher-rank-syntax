import HigherRankSyntax.Initiality.Interpretation
import HigherRankSyntax.Typing.Weakening

/-!
# Naturality of the interpretation

The interpretation is natural in the environment.

* Renaming the syntax along a renaming of slots is interpreting it at the
  environment renamed along that renaming: the value of a slot is the value of its
  image.
* Reindexing the environment along a substitution `σ` of the model reindexes the
  interpretation along `σ`: whatever is interpreted at the environment, reindexed
  along `σ`, is interpreted at the reindexed environment.
* The interpretation of a filling of a decoration from `g` is a section of the
  projection of the decoration's chain over `g`, and along it the generic value of
  every slot that is not an equation has as filler an interpretation of the slot's
  filler.
* Typed environments are stable under reindexing and under extension by the
  interpretation of a telescope.
-/

universe u

namespace HrS

variable {M : Structure.{u}}

/-! ### Reindexing an entry -/

/-- If every filler of `w`, reindexed along the lift of `σ` through `b`, is one of `w'`,
then a term an entry is given by `w`, reindexed along `σ`, is a term the reindexed entry
is given by `w'`. -/
theorem Chain.entryTerm_subst
    {Γ Δ : M.Ob} {α : C.Arity} (b : Chain M Γ α) (σ : M.Sub Δ Γ) (B : Boundary M b.last)
    (w : Part (Filler M b.last)) (w' : Part (Filler M (b.subst σ).last))
    (hw : ∀ v ∈ w, v.subst (b.lift σ) ∈ w') {t} (ht : t ∈ b.entryTerm B w) :
  Chain.Bind_subst_entry rfl σ ▸ M.substTm t σ ∈ (b.subst σ).entryTerm (B.subst (b.lift σ)) w'
  := by
  have hlam : ∀ v : Filler M b.last,
      Bind_subst_entry rfl σ ▸ M.substTm (b.lam v.tm) σ
        = (b.subst σ).lam (v.subst (b.lift σ)).tm := by
    intro v
    apply eq_of_heq
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b := (b.subst σ).lam (M.substTm v.tm (b.lift σ)))
    · rw [← lam_subst]
      symm
      apply eqRec_heq
    · congr 1
      · apply Boundary.subst_ty
      · symm
        apply eqRec_heq
  cases B with
  | sort =>
      obtain ⟨s, hs, rfl⟩ := (mem_entryTerm_sort b w).mp ht
      apply (mem_entryTerm_sort _ w').mpr
      use ((Filler.mk .sort s).subst (b.lift σ)).tm, hw _ hs
      apply hlam ⟨.sort, s⟩
  | of S =>
      obtain ⟨e, he, rfl⟩ := (mem_entryTerm_of b S w).mp ht
      apply (mem_entryTerm_of _ _ w').mpr
      use ((Filler.mk (.of S) e).subst (b.lift σ)).tm, hw _ he
      apply hlam ⟨.of S, e⟩
  | eqSort S S' =>
      obtain ⟨rfl, rfl⟩ := (mem_entryTerm_eqSort b S S' w).mp ht
      apply (mem_entryTerm_eqSort _ _ _ w').mpr
      use rfl
      symm
      apply Eq.trans _ (lam_unlam _ _)
      congr 1
      apply M.IdSort_irrelevant
  | eqElement S l r =>
      obtain ⟨rfl, rfl⟩ := (mem_entryTerm_eqElement b S l r w).mp ht
      apply (mem_entryTerm_eqElement _ _ _ _ w').mpr
      use rfl
      symm
      apply Eq.trans _ (lam_unlam _ _)
      congr 1
      apply M.IdElement_irrelevant

namespace Environment

/-! ### Renaming -/

/-- An environment renamed along a renaming `ρ` of slots: the value of a slot is the
value of its image under `ρ`. -/
def rename {Γ : M.Ob} {Δ Φ : C.Arity} (E : Environment M Γ Δ) (ρ : Φ →ʳ Δ) :
    Environment M Γ Φ :=
  fun _ x => E (ρ x)

/-- Renaming an environment and then extending it by a decoration is extending it
and then renaming it along `ρ` extended by the new slots. -/
theorem extend_rename
    {Γ : M.Ob} {Δ Φ Ω : C.Arity} (E : Environment M Γ Δ) (ρ : Φ →ʳ Δ)
    {c : Chain M Γ Ω} (d : Decoration M c) :
  (E.rename ρ).extend d = (E.extend d).rename (ρ ⇑ʳ Ω)
  := by
  funext _ x
  obtain ⟨y, rfl⟩ | ⟨z, rfl⟩ := C.cover _ _ x
  · simp only [rename, extend_inl, Renaming.extend_inl]
  · simp only [rename, extend_inr, Renaming.extend_inr]

/-- An extended environment, renamed along the inclusion of the old slots, is the
environment reindexed along the projection of the chain. -/
theorem rename_inl_extend
    {Γ : M.Ob} {Δ Ω : C.Arity} (E : Environment M Γ Δ) {c : Chain M Γ Ω}
    (d : Decoration M c) :
  (E.extend d).rename (Renaming.inl Δ Ω) = E.subst c.projection
  := by
  funext _ y
  apply extend_inl

/-- Pairing fillers along a decoration from `g` gives the same result at two
environments over `Γ` when the fillers agree at their extensions by every
decoration. -/
theorem pairFillers_congr
    {Γ : M.Ob} {Δ₁ Δ₂ : C.Arity} (E₁ : Environment M Γ Δ₁) (E₂ : Environment M Γ Δ₂) :
    ∀ {Y : M.Ob} {Ω : C.Arity} {c : Chain M Y Ω} (d : Decoration M c) (g : M.Sub Γ Y)
      (fillers₁ : ∀ ⦃Λ : C.Arity⦄, Ω ∋ Λ → ∀ {Z : M.Ob}, Environment M Z (Δ₁ ⋈ Λ) →
        Part (Filler M Z))
      (fillers₂ : ∀ ⦃Λ : C.Arity⦄, Ω ∋ Λ → ∀ {Z : M.Ob}, Environment M Z (Δ₂ ⋈ Λ) →
        Part (Filler M Z)),
      (∀ ⦃Λ : C.Arity⦄ (i : Ω ∋ Λ) {c' : Chain M Γ Λ} (D : Decoration M c'),
        fillers₁ i (E₁.extend D) = fillers₂ i (E₂.extend D)) →
      E₁.pairFillers d g fillers₁ = E₂.pairFillers d g fillers₂
  | _, _, _, .nil, _, _, _, _ => rfl
  | _, _, _, .cons _ _ _ _ _, g, fillers₁, fillers₂, h => by
      rw [pairFillers, pairFillers, h]
      congr 1
      funext t
      apply pairFillers_congr
      intro _ j _ D
      apply h

/-- A renamed expression is interpreted as the expression at the renamed
environment. -/
theorem interpret_rename :
    ∀ {Γ : M.Ob} {Δ Φ : C.Arity} (E : Environment M Γ Δ) (ρ : Φ →ʳ Δ) (e : Expr Φ),
      E.interpret (⟦ ρ ⟧ʳ e) = (E.rename ρ).interpret e
  | _, _, _, E, ρ, .ap x args => by
      rw [Renaming.act_ap, interpret_ap, interpret_ap]
      congr 1
      funext _
      congr 1
      apply pairFillers_congr
      intro _ i _ D
      rw [interpret_rename, extend_rename]

/-- A filling with renamed fillers is interpreted as the filling at the renamed
environment. -/
theorem interpretFilling_rename
    {Γ Y : M.Ob} {Δ Φ Ω : C.Arity} (E : Environment M Γ Δ) (ρ : Φ →ʳ Δ) (τ : Subst Ω Φ)
    {c : Chain M Y Ω} (d : Decoration M c) (g : M.Sub Γ Y) :
  E.interpretFilling (fun ⦃Λ⦄ i => ⟦ ρ ⇑ʳ Λ ⟧ʳ (τ i)) d g = (E.rename ρ).interpretFilling τ d g
  := by
  apply pairFillers_congr
  intro _ i _ D
  rw [interpret_rename, extend_rename]

/-- A renamed boundary is interpreted as the boundary at the renamed environment. -/
theorem interpretBoundary_rename
    {Γ : M.Ob} {Δ Φ : C.Arity} (E : Environment M Γ Δ) (ρ : Φ →ʳ Δ) (β : Bd Φ) :
  E.interpretBoundary (β.rename ρ) = (E.rename ρ).interpretBoundary β
  := by
  cases β with
  | sort => rfl
  | of S => rw [Bd.rename, interpretBoundary, interpretBoundary, interpret_rename]
  | eq l r =>
      rw [Bd.rename, interpretBoundary, interpretBoundary, interpret_rename, interpret_rename]

/-- A telescope over a renamed base is interpreted as the telescope at the renamed
environment. -/
theorem interpretTelescope_rename :
    ∀ {Γ : M.Ob} {Δ Φ Ω : C.Arity} (E : Environment M Γ Δ) (ρ : Φ →ʳ Δ) (Θ : dTel Φ Ω),
      E.interpretTelescope (Θ.rename ρ) = (E.rename ρ).interpretTelescope Θ
  | _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, ρ, .cons bind boundary rest => by
      rw [dTel.rename, interpretTelescope, interpretTelescope, interpretTelescope_rename]
      congr 1
      funext T
      rw [interpretBoundary_rename, ← extend_rename]
      congr 1
      funext B
      congr 1
      apply Eq.trans (interpretTelescope_rename _ (ρ ⇑ʳ C.single _) rest)
      rw [extend_rename]
      rfl

/-! ### Reindexing -/

/-- Pairing fillers along a decoration from `f` after `g` is pairing them along the
decoration reindexed along `f` from `g`, followed by the lift of `f` through the
chain. -/
theorem pairFillers_comp
    {Γ : M.Ob} {Δ : C.Arity} (E : Environment M Γ Δ) :
    ∀ {Y Y' : M.Ob} {Ω : C.Arity} {c : Chain M Y Ω} (d : Decoration M c) (f : M.Sub Y' Y)
      (g : M.Sub Γ Y')
      (fillers : ∀ ⦃Λ : C.Arity⦄, Ω ∋ Λ → ∀ {Z : M.Ob}, Environment M Z (Δ ⋈ Λ) →
        Part (Filler M Z)),
      E.pairFillers d (M.comp f g) fillers
        = (E.pairFillers (d.subst f) g fillers).map (M.comp (c.lift f))
  | _, _, _, _, .nil, _, _, _ => rfl
  | _, _, _, _, .cons (b := b) db B A hA d, f, g, fillers => by
      simp only [pairFillers, Decoration.subst, Chain.lift]
      erw [Part.map_bind]
      have hT : M.Tm Γ ((b.subst (M.comp f g)).Bind (B.subst (b.lift (M.comp f g))).ty)
          = M.Tm Γ (((b.subst f).subst g).Bind
              ((B.subst (b.lift f)).subst ((b.subst f).lift g)).ty) := by
        rw [← Chain.Bind_subst_entry hA, ← Chain.Bind_subst_entry (Chain.Bind_subst_entry hA f),
          M.substTy_comp]
      congr 1
      · congr 1
        · apply Chain.subst_comp
        · apply HEq.trans _ (heq_of_eq (Boundary.subst_comp _ _ _))
          congr 1
          · rw [Chain.subst_comp]
          · apply Chain.lift_comp
        · congr 1
          · rw [Chain.subst_comp]
          · congr 1
            · apply Chain.subst_comp
            · apply Decoration.subst_comp
      · apply Function.hfunext hT
        intro t t' htt
        apply heq_of_eq
        apply Eq.trans _ (pairFillers_comp E d (M.lift A f) _ _)
        rw [M.lift_comp_pair]
        congr 2
        apply eq_of_heq
        apply HEq.trans (eqRec_heq _ _)
        apply HEq.trans htt
        symm
        apply HEq.trans (eqRec_heq _ _)
        apply eqRec_heq

/-- If the fillers are stable under reindexing, a pairing of them at an environment,
reindexed along `σ`, is a pairing of them at the reindexed environment from the
reindexed substitution. -/
theorem pairFillers_subst
    {Γ Γ' : M.Ob} {Δ : C.Arity} (E : Environment M Γ Δ) (σ : M.Sub Γ' Γ) :
    ∀ {Y : M.Ob} {Ω : C.Arity} {c : Chain M Y Ω} (d : Decoration M c) (g : M.Sub Γ Y)
      (fillers : ∀ ⦃Λ : C.Arity⦄, Ω ∋ Λ → ∀ {Z : M.Ob}, Environment M Z (Δ ⋈ Λ) →
        Part (Filler M Z)),
      (∀ ⦃Λ : C.Arity⦄ (i : Ω ∋ Λ) {Z Z' : M.Ob} (E' : Environment M Z (Δ ⋈ Λ))
        (τ : M.Sub Z' Z) (v : Filler M Z), v ∈ fillers i E' → v.subst τ ∈ fillers i (E'.subst τ)) →
      ∀ s ∈ E.pairFillers d g fillers, M.comp s σ ∈ (E.subst σ).pairFillers d (M.comp g σ) fillers
  | _, _, _, .nil, g, _, _, s, hs => by
      obtain rfl := Part.mem_some_iff.mp hs
      apply Part.mem_some
  | _, _, _, .cons (α := α) (b := b) db B A hA d, g, fillers, hfill, s, hs => by
      obtain ⟨t, ht, hs'⟩ := Part.mem_bind_iff.mp hs
      have ht₁ := Chain.entryTerm_subst (b.subst g) σ (B.subst (b.lift g)) _ _ (hfill _ _ _) ht
      have hb : (b.subst g).subst σ = b.subst (M.comp g σ) := by
        symm
        apply Chain.subst_comp
      have hB : HEq ((B.subst (b.lift g)).subst ((b.subst g).lift σ))
          (B.subst (b.lift (M.comp g σ))) := by
        symm
        apply HEq.trans _ (heq_of_eq (Boundary.subst_comp _ _ _))
        congr 1
        · rw [Chain.subst_comp]
        · apply Chain.lift_comp
      have hw : HEq (fillers (C.inl (C.singleSlot α))
            ((E.extend (db.subst g)).subst ((b.subst g).lift σ)))
          (fillers (C.inl (C.singleSlot α)) ((E.subst σ).extend (db.subst (M.comp g σ)))) := by
        rw [← extend_subst]
        congr 1
        · rw [Chain.subst_comp]
        · congr 1
          symm
          apply Decoration.subst_comp
      obtain ⟨t₂, ht₂, htt⟩ := Chain.entryTerm_congr hb hB hw ht₁
      apply Part.mem_bind_iff.mpr
      use t₂, ht₂
      convert pairFillers_subst E σ d _ _ (fun _ j => hfill (C.inr j)) s hs' using 2
      rw [M.pair_comp]
      congr 2
      apply eq_of_heq
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans (HEq.symm htt)
      apply HEq.trans (eqRec_heq _ _)
      symm
      apply HEq.trans (eqRec_heq _ _)
      congr 1
      · apply Chain.Bind_subst_entry hA g
      · apply eqRec_heq

/-- Whatever an expression is interpreted as at an environment, reindexed along `σ`,
the expression is interpreted as at the reindexed environment. -/
theorem interpret_subst :
    ∀ {Γ Γ' : M.Ob} {Δ : C.Arity} (E : Environment M Γ Δ) (σ : M.Sub Γ' Γ) (e : Expr Δ)
      (w : Filler M Γ), w ∈ E.interpret e → w.subst σ ∈ (E.subst σ).interpret e
  | Γ, Γ', _, E, σ, .ap x args, w, hw => by
      rw [interpret_ap] at hw ⊢
      obtain ⟨hne, hw⟩ := Part.mem_assert_iff.mp hw
      obtain ⟨s, hs, rfl⟩ := (Part.mem_map_iff _).mp hw
      have hcomp := pairFillers_comp (E.subst σ) (E x).binding.decoration σ (M.identity Γ')
        (fun _ i _ E' => E'.interpret (args i))
      rw [M.comp_identity] at hcomp
      have hs' := pairFillers_subst E σ (E x).binding.decoration (M.identity Γ) _
        (fun _ i _ _ E' τ => interpret_subst E' τ (args i)) s hs
      rw [M.identity_comp, hcomp] at hs'
      obtain ⟨s', hs'', hss⟩ := (Part.mem_map_iff _).mp hs'
      apply Part.mem_assert_iff.mpr
      use mt (Boundary.isEq_subst _ _).mp hne
      apply (Part.mem_map_iff _).mpr
      use s', hs''
      rw [← Filler.subst_comp, ← hss, Filler.subst_comp]
      rfl

/-- The interpretation of a filling, reindexed along `σ`, is the interpretation of
the filling at the reindexed environment from the reindexed substitution. -/
theorem interpretFilling_subst
    {Γ Γ' Y : M.Ob} {Δ Ω : C.Arity} (E : Environment M Γ Δ) (σ : M.Sub Γ' Γ)
    (τ : Subst Ω Δ) {c : Chain M Y Ω} (d : Decoration M c) (g : M.Sub Γ Y) (s : M.Sub Γ c.last)
    (hs : s ∈ E.interpretFilling τ d g) :
  M.comp s σ ∈ (E.subst σ).interpretFilling τ d (M.comp g σ)
  := by
  apply pairFillers_subst E σ d g _ (fun _ i _ _ E' τ' => interpret_subst E' τ' (τ i)) s hs

/-- The interpretation of a boundary, reindexed along `σ`, is the interpretation of
the boundary at the reindexed environment. -/
theorem interpretBoundary_subst
    {Γ Γ' : M.Ob} {Δ : C.Arity} (E : Environment M Γ Δ) (σ : M.Sub Γ' Γ) (β : Bd Δ)
    (B : Boundary M Γ) (hB : B ∈ E.interpretBoundary β) :
  B.subst σ ∈ (E.subst σ).interpretBoundary β
  := by
  cases β with
  | sort =>
      obtain rfl := (mem_interpretBoundary_sort E B).mp hB
      apply (mem_interpretBoundary_sort _ _).mpr rfl
  | of S =>
      obtain ⟨t, ht, rfl⟩ := (mem_interpretBoundary_of E S B).mp hB
      apply (mem_interpretBoundary_of _ S _).mpr
      use ((Filler.mk .sort t).subst σ).tm, interpret_subst E σ S _ ht
      rfl
  | eq l r =>
      apply (mem_interpretBoundary_eq _ l r _).mpr
      rcases (mem_interpretBoundary_eq E l r B).mp hB with
        ⟨tl, tr, hl, hr, rfl⟩ | ⟨S, tl, tr, hl, hr, rfl⟩
      · left
        use ((Filler.mk .sort tl).subst σ).tm, ((Filler.mk .sort tr).subst σ).tm,
          interpret_subst E σ l _ hl, interpret_subst E σ r _ hr
        rfl
      · right
        use M.U_subst σ ▸ M.substTm S σ, ((Filler.mk (.of S) tl).subst σ).tm,
          ((Filler.mk (.of S) tr).subst σ).tm, interpret_subst E σ l _ hl,
          interpret_subst E σ r _ hr
        rfl

/-- The interpretation of a telescope, reindexed along `σ`, is the interpretation of
the telescope at the reindexed environment. -/
theorem interpretTelescope_subst :
    ∀ {Γ Γ' : M.Ob} {Δ Ω : C.Arity} (E : Environment M Γ Δ) (σ : M.Sub Γ' Γ)
      (Θ : dTel Δ Ω) (T : Telescope M Γ Ω), T ∈ E.interpretTelescope Θ →
      T.subst σ ∈ (E.subst σ).interpretTelescope Θ
  | _, _, _, _, E, σ, .nil, T, hT => by
      obtain rfl := (mem_interpretTelescope_nil E T).mp hT
      apply (mem_interpretTelescope_nil _ _).mpr rfl
  | _, _, _, _, E, σ, .cons bind boundary rest, T, hT => by
      obtain ⟨T₀, hT₀, B, hB, A, hA, R, hR, rfl⟩ :=
        (mem_interpretTelescope_cons E bind boundary rest T).mp hT
      apply (mem_interpretTelescope_cons _ bind boundary rest _).mpr
      use T₀.subst σ, interpretTelescope_subst E σ bind T₀ hT₀, B.subst (T₀.chain.lift σ)
      constructor
      · erw [extend_subst]
        apply interpretBoundary_subst _ _ _ _ hB
      · use M.substTy A σ, Chain.Bind_subst_entry hA σ, R.subst (M.lift A σ)
        constructor
        · erw [extend_subst E (.cons T₀.decoration B A hA .nil)]
          apply interpretTelescope_subst _ (M.lift A σ) rest R hR
        · rfl

/-! ### Sections and slots -/

/-- The interpretation of a filling of a decoration from `g` is a section of the
projection of the decoration's chain over `g`. -/
theorem interpretFilling_projection
    {Γ : M.Ob} {Δ : C.Arity} (E : Environment M Γ Δ) :
    ∀ {Y : M.Ob} {Ω : C.Arity} {c : Chain M Y Ω} (τ : Subst Ω Δ) (d : Decoration M c)
      (g : M.Sub Γ Y) (s : M.Sub Γ c.last), s ∈ E.interpretFilling τ d g →
      M.comp c.projection s = g
  | _, _, _, τ, .nil, g, s, hs => by
      obtain rfl := (mem_interpretFilling_nil E τ g s).mp hs
      apply M.identity_comp
  | _, _, _, τ, .cons db B A hA d, g, s, hs => by
      obtain ⟨t, _, hs'⟩ := (mem_interpretFilling_cons E τ db B A hA d g s).mp hs
      rw [Chain.projection, M.comp_assoc]
      erw [interpretFilling_projection E _ d _ s hs']
      apply M.projection_pair

/-- Along the interpretation `s` of a filling `τ` of a decoration, the generic value of
a slot `z` that is not an equation, reindexed along `s`, has as filler an interpretation
of `τ z` at the environment extended by the value's binding decoration. -/
theorem interpretFilling_slot
    {Γ : M.Ob} {Δ : C.Arity} (E : Environment M Γ Δ) :
    ∀ {Y : M.Ob} {Ω : C.Arity} {c : Chain M Y Ω} (τ : Subst Ω Δ) (d : Decoration M c)
      (g : M.Sub Γ Y) (s : M.Sub Γ c.last), s ∈ E.interpretFilling τ d g →
      ∀ ⦃β : C.Arity⦄ (z : Ω ∋ β), ¬ (d.slot z).filler.boundary.IsEq →
        ((d.slot z).subst s).filler
          ∈ (E.extend ((d.slot z).subst s).binding.decoration).interpret (τ z)
  | _, _, _, _, .nil, _, _, _ => fun _ z _ => (C.unit_is_empty z).elim
  | _, _, _, τ, .cons (b := b) db B A hA d, g, s, hs => by
      obtain ⟨t, ht, hs'⟩ := (mem_interpretFilling_cons E τ db B A hA d g s).mp hs
      apply slotCases
      · intro hz
        generalize hv : ((Decoration.cons db B A hA d).slot (C.inl (C.singleSlot _))).subst s = v
        rw [Decoration.slot_head] at hv hz
        simp only [Chain.last] at hv
        rw [← Value.subst_comp, interpretFilling_projection E _ d _ s hs',
          Decoration.headValue_subst_pair] at hv
        subst hv
        obtain ⟨v, hv, rfl⟩ : ∃ v, (⟨B.subst (b.lift g), v⟩ : Filler M _)
            ∈ (E.extend (db.subst g)).interpret (τ (C.inl (C.singleSlot _)))
              ∧ t = (b.subst g).lam v := by
          cases B with
          | sort => apply (Chain.mem_entryTerm_sort _ _).mp ht
          | of S => apply (Chain.mem_entryTerm_of _ _ _).mp ht
          | eqSort S S' => apply (hz trivial).elim
          | eqElement S l r => apply (hz trivial).elim
        convert hv using 2
        apply Eq.trans _ (Chain.unlam_lam _ v)
        congr 1
        apply eq_of_heq
        apply HEq.trans (eqRec_heq _ _)
        apply eqRec_heq
      · intro _ y hy
        rw [Decoration.slot_tail] at hy ⊢
        apply interpretFilling_slot E _ d _ s hs' y hy

/-! ### Typed environments -/

/-- Extending an environment by a decoration with a first entry is extending it by
that one entry and then by the rest of the decoration. -/
theorem extend_cons
    {Γ : M.Ob} {Δ α Ω : C.Arity} (E : Environment M Γ Δ) {b : Chain M Γ α}
    (db : Decoration M b) (B : Boundary M b.last) (A : M.Ty Γ) (hA : A = b.Bind B.ty)
    {c : Chain M (M.extend Γ A) Ω} (d : Decoration M c) :
  E.extend (.cons db B A hA d) = (E.extend (.cons db B A hA .nil)).extend d
  := by
  funext _ x
  obtain ⟨y, rfl⟩ | ⟨z, rfl⟩ := C.cover _ _ x
  · rw [extend_inl, C.inl_inl _ _ _ y]
    erw [extend_inl, extend_inl, ← Value.subst_comp]
    simp only [Chain.projection, Chain.last, M.comp_identity]
  · induction z using slotCases with
    | head =>
        rw [extend_inr, Decoration.slot_head, C.inr_inl]
        erw [extend_inl, extend_inr, Decoration.slot_head, ← Value.subst_comp]
        simp only [Chain.projection, Chain.last, M.identity_comp]
    | tail w =>
        rw [extend_inr, Decoration.slot_tail, C.inr_inr]
        erw [extend_inr]
        rfl

/-- A typed environment reindexed along a substitution is typed by the same
ambient. -/
theorem Typed.subst
    {Γ Γ' : M.Ob} {Δ : C.Arity} {E : Environment M Γ Δ} {Ξ : Ambient Δ} (h : E.Typed Ξ)
    (σ : M.Sub Γ' Γ) :
  (E.subst σ).Typed Ξ
  := by
  intro _ x
  obtain ⟨hT, hB⟩ := h x
  constructor
  · apply interpretTelescope_subst E σ _ _ hT
  · erw [extend_subst]
    apply interpretBoundary_subst _ _ _ _ hB

/-- An environment typed by `Ξ`, extended by the interpretation of a telescope `Θ` at
it, is typed by `Ξ ⋈ Θ`. -/
theorem Typed.extend
    {Γ : M.Ob} {Δ Ω : C.Arity} {E : Environment M Γ Δ} {Ξ : Ambient Δ} (h : E.Typed Ξ)
    {Θ : dTel Δ Ω} {T : Telescope M Γ Ω} (hT : T ∈ E.interpretTelescope Θ) :
  (E.extend T.decoration).Typed (Ξ ⋈ Θ)
  := by
  induction Θ generalizing Γ with
  | nil =>
      obtain rfl := (mem_interpretTelescope_nil E T).mp hT
      intro _ x
      obtain ⟨y, rfl⟩ | ⟨z, rfl⟩ := C.cover _ _ x
      · rw [extend_inl, dTel.binding_concatenate_inl, dTel.declaration_concatenate_inl]
        erw [interpretTelescope_rename, interpretBoundary_rename, ← extend_rename,
          rename_inl_extend]
        apply h.subst _ y
      · apply (C.unit_is_empty z).elim
  | cons bind boundary rest _ ihrest =>
      obtain ⟨T₀, hT₀, B, hB, A, rfl, R, hR, rfl⟩ :=
        (mem_interpretTelescope_cons E bind boundary rest T).mp hT
      have h₁ : (E.extend (Decoration.cons T₀.decoration B _ rfl .nil)).Typed
          (Ξ ⋈ dTel.cons bind boundary .nil) := by
        intro _ x
        obtain ⟨y, rfl⟩ | ⟨z, rfl⟩ := C.cover _ _ x
        · rw [extend_inl, dTel.binding_concatenate_inl, dTel.declaration_concatenate_inl]
          erw [interpretTelescope_rename, interpretBoundary_rename, ← extend_rename,
            rename_inl_extend]
          apply h.subst _ y
        · induction z using slotCases with
          | head =>
              rw [extend_inr, Decoration.slot_head, dTel.binding_concatenate_inr,
                dTel.declaration_concatenate_inr, dTel.binding_head, dTel.declaration_head]
              erw [interpretTelescope_rename, interpretBoundary_rename, ← extend_rename,
                rename_inl_extend, Value.subst_identity]
              simp only [Chain.projection, Chain.last, M.comp_identity]
              constructor
              · apply interpretTelescope_subst E _ bind _ hT₀
              · erw [extend_subst]
                apply interpretBoundary_subst _ _ _ _ hB
          | tail u => apply (C.unit_is_empty u).elim
      have hrest := ihrest h₁ hR
      erw [dTel.concatenate_assoc] at hrest
      erw [extend_cons]
      apply hrest

end Environment

end HrS
