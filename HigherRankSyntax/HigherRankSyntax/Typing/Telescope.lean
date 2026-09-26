import HigherRankSyntax.Typing.Boundary

/-!
# Decorated telescopes

`dTel Ω Δ` is a telescope over the base `Ω` whose slots form `Δ`.  Each entry
carries the telescope of entries it binds and its declaration; the entries after
it are over the base extended by it.  `declaration T x` and `binding T x` are the
declaration of the slot `x` and the telescope of entries it binds, weakened into
the whole telescope.
-/

/-- `dTel Ω Δ` is a telescope over the base `Ω` with slots `Δ`.  An entry of arity `α`
consists of the telescope `dTel Ω α` of the entries it binds and a boundary over
`Ω ⋈ α`; the entries after it form a telescope over `Ω ⋈ C.single α`. -/
inductive dTel : C.Arity → C.Arity → Type where
  | nil {Ω : C.Arity} : dTel Ω 1
  | cons {Ω α Δ : C.Arity} (binding : dTel Ω α) (boundary : Bd (Ω ⋈ α))
      (rest : dTel (Ω ⋈ C.single α) Δ) : dTel Ω (C.single α ⋈ Δ)

/-- Case analysis on a slot of `C.single α ⋈ Δ`: it is `C.inl (C.singleSlot α)` or
`C.inr y` for a slot `y` of `Δ`. -/
theorem slotCases
    {α Δ : C.Arity} {motive : ∀ ⦃β : C.Arity⦄, (C.single α ⋈ Δ) ∋ β → Prop}
    (head : motive (C.inl (C.singleSlot α)))
    (tail : ∀ ⦃β : C.Arity⦄ (y : Δ ∋ β), motive (C.inr y))
    ⦃β : C.Arity⦄ (x : (C.single α ⋈ Δ) ∋ β) :
  motive x
  := by
  rcases C.cover (C.single α) Δ x with ⟨z, rfl⟩ | ⟨y, rfl⟩
  · obtain rfl := C.single_arity z
    rw [C.single_slot_unique z]
    exact head
  · exact tail y

namespace dTel

/-- Reindex the base along a renaming. -/
def rename : {Γ Δ Ξ : C.Arity} → (Γ →ʳ Δ) → dTel Γ Ξ → dTel Δ Ξ
  | _, _, _, _, .nil => .nil
  | _, _, _, ρ, .cons (α := α) binding boundary rest =>
      .cons (rename ρ binding) (Bd.rename (ρ ⇑ʳ α) boundary)
        (rename (ρ ⇑ʳ C.single α) rest)

/-- Renaming the base along `θ ∘ʳ ρ` is renaming it along `ρ` and then along `θ`. -/
theorem rename_comp {Γ Δ Ξ : C.Arity} (ρ : Γ →ʳ Δ) (θ : Δ →ʳ Ξ) :
  ∀ {Ψ : C.Arity} (T : dTel Γ Ψ), rename (θ ∘ʳ ρ) T = rename θ (rename ρ T)
  | _, .nil => rfl
  | _, .cons bind boundary rest => by
      simp only [rename, Renaming.extend_comp, Bd.rename_comp, rename_comp]

/-- Append a telescope over the extended base. -/
def concatenate : {Ω Δ Ξ : C.Arity} → dTel Ω Δ → dTel (Ω ⋈ Δ) Ξ → dTel Ω (Δ ⋈ Ξ)
  | _, _, _, .nil, Ψ => Ψ
  | _, _, _, .cons binding boundary rest, Ψ =>
      .cons binding boundary (concatenate rest Ψ)

/-- Reindex the base by a substitution. -/
def actBase : {Γ Δ Ψ : C.Arity} → Subst Γ Δ → dTel Γ Ψ → dTel Δ Ψ
  | _, _, _, _, .nil => .nil
  | _, _, _, σ, .cons (α := α) bind boundary rest =>
      .cons (actBase σ bind) (Bd.act (Γ := 1) σ α boundary)
        (actBase (Subst.lift σ (C.single α)) rest)

/-- Fill the block `Ω` of the base `Γ ⋈ Ω` by `σ : Subst Ω Γ`. -/
def instantiate {Γ Ω Ψ : C.Arity} (σ : Subst Ω Γ) (Θ : dTel (Γ ⋈ Ω) Ψ) : dTel Γ Ψ :=
  actBase (Subst.copair (Subst.id Γ) σ) Θ

/-- The declaration of a slot of arity `β`, a boundary over `Ω ⋈ Δ ⋈ β`. -/
def declaration : {Ω Δ : C.Arity} → dTel Ω Δ → {β : C.Arity} → (Δ ∋ β) → Bd (Ω ⋈ Δ ⋈ β)
  | _, _, .nil, _, x => (C.unit_is_empty x).elim
  | Ω, _, .cons (α := α) (Δ := Δ) _ boundary rest, _, x =>
      match C.split (C.single α) Δ x with
      | .inl z =>
          cast (congrArg (fun γ => Bd (Ω ⋈ (C.single α ⋈ Δ) ⋈ γ)) (C.single_arity z).symm)
            (Bd.rename (Renaming.inl Ω (C.single α ⋈ Δ) ⇑ʳ α) boundary)
      | .inr y => declaration rest y

/-- The telescope over `Ω ⋈ Δ` of the entries a slot binds. -/
def binding : {Ω Δ : C.Arity} → dTel Ω Δ → {β : C.Arity} → (Δ ∋ β) → dTel (Ω ⋈ Δ) β
  | _, _, .nil, _, x => (C.unit_is_empty x).elim
  | Ω, _, .cons (α := α) (Δ := Δ) bind _ rest, _, x =>
      match C.split (C.single α) Δ x with
      | .inl z =>
          cast (congrArg (fun γ => dTel (Ω ⋈ (C.single α ⋈ Δ)) γ) (C.single_arity z).symm)
            (rename (Renaming.inl Ω (C.single α ⋈ Δ)) bind)
      | .inr y => binding rest y

/-- The declaration of the first entry is its boundary, weakened into the whole
telescope. -/
@[simp]
theorem declaration_head
    {Ω α Δ : C.Arity}
    (bind : dTel Ω α) (boundary : Bd (Ω ⋈ α)) (rest : dTel (Ω ⋈ C.single α) Δ) :
  declaration (.cons bind boundary rest) (C.inl (C.singleSlot α))
    = Bd.rename (Renaming.inl Ω (C.single α ⋈ Δ) ⇑ʳ α) boundary
  := by
  simp only [declaration, C.split_inl]
  rfl

/-- The declaration of a later entry is its declaration in the remaining
telescope. -/
@[simp]
theorem declaration_tail
    {Ω α Δ β : C.Arity}
    (bind : dTel Ω α) (boundary : Bd (Ω ⋈ α)) (rest : dTel (Ω ⋈ C.single α) Δ)
    (y : Δ ∋ β) :
  declaration (.cons bind boundary rest) (C.inr y) = declaration rest y
  := by
  simp only [declaration, C.split_inr]

/-- The entries bound by the first entry are its binding telescope, weakened into
the whole telescope. -/
@[simp]
theorem binding_head
    {Ω α Δ : C.Arity}
    (bind : dTel Ω α) (boundary : Bd (Ω ⋈ α)) (rest : dTel (Ω ⋈ C.single α) Δ) :
  binding (.cons bind boundary rest) (C.inl (C.singleSlot α))
    = rename (Renaming.inl Ω (C.single α ⋈ Δ)) bind
  := by
  simp only [binding, C.split_inl]
  rfl

/-- The entries bound by a later entry are those it binds in the remaining
telescope. -/
@[simp]
theorem binding_tail
    {Ω α Δ β : C.Arity}
    (bind : dTel Ω α) (boundary : Bd (Ω ⋈ α)) (rest : dTel (Ω ⋈ C.single α) Δ)
    (y : Δ ∋ β) :
  binding (.cons bind boundary rest) (C.inr y) = binding rest y
  := by
  simp only [binding, C.split_inr]

/-- A slot of `Ψ` has the same declaration in `concatenate Θ Ψ` as in `Ψ`. -/
theorem declaration_concatenate_inr {Ω Δ Ξ : C.Arity} :
  ∀ (Θ : dTel Ω Δ) (Ψ : dTel (Ω ⋈ Δ) Ξ) {β : C.Arity} (z : Ξ ∋ β),
    (concatenate Θ Ψ).declaration (C.inr z) = Ψ.declaration z
  | .nil, Ψ, _, z => congrArg Ψ.declaration (C.unit_left Ξ z)
  | .cons bind boundary rest, Ψ, _, z => by
      rw [← C.inr_inr]
      apply Eq.trans (declaration_tail ..)
      apply declaration_concatenate_inr

/-- A slot of `Θ` has as declaration in `concatenate Θ Ψ` its declaration in `Θ`,
weakened past `Ψ`. -/
theorem declaration_concatenate_inl {Ω Δ Ξ : C.Arity} :
  ∀ (Θ : dTel Ω Δ) (Ψ : dTel (Ω ⋈ Δ) Ξ) {β : C.Arity} (y : Δ ∋ β),
    (concatenate Θ Ψ).declaration (C.inl y)
      = Bd.rename (Renaming.inl (Ω ⋈ Δ) Ξ ⇑ʳ β) (Θ.declaration y)
  | .nil, _, _, y => (C.unit_is_empty y).elim
  | .cons bind boundary rest, Ψ, _, y => by
      induction y using slotCases with
      | head =>
        rw [declaration_head, ← C.inl_inl]
        apply Eq.trans (declaration_head ..)
        rw [← Bd.rename_comp, ← Renaming.extend_comp, Renaming.inl_inl]
        rfl
      | tail w =>
        rw [declaration_tail, ← C.inr_inl]
        apply Eq.trans (declaration_tail ..)
        apply declaration_concatenate_inl

/-- A slot of `Ψ` binds the same entries in `concatenate Θ Ψ` as in `Ψ`. -/
theorem binding_concatenate_inr {Ω Δ Ξ : C.Arity} :
  ∀ (Θ : dTel Ω Δ) (Ψ : dTel (Ω ⋈ Δ) Ξ) {β : C.Arity} (z : Ξ ∋ β),
    (concatenate Θ Ψ).binding (C.inr z) = Ψ.binding z
  | .nil, Ψ, _, z => congrArg Ψ.binding (C.unit_left Ξ z)
  | .cons bind boundary rest, Ψ, _, z => by
      rw [← C.inr_inr]
      apply Eq.trans (binding_tail ..)
      apply binding_concatenate_inr

/-- A slot of `Θ` binds in `concatenate Θ Ψ` the entries it binds in `Θ`, weakened
past `Ψ`. -/
theorem binding_concatenate_inl {Ω Δ Ξ : C.Arity} :
  ∀ (Θ : dTel Ω Δ) (Ψ : dTel (Ω ⋈ Δ) Ξ) {β : C.Arity} (y : Δ ∋ β),
    (concatenate Θ Ψ).binding (C.inl y) = rename (Renaming.inl (Ω ⋈ Δ) Ξ) (Θ.binding y)
  | .nil, _, _, y => (C.unit_is_empty y).elim
  | .cons bind boundary rest, Ψ, _, y => by
      induction y using slotCases with
      | head =>
        rw [binding_head, ← C.inl_inl]
        apply Eq.trans (binding_head ..)
        rw [← rename_comp, Renaming.inl_inl]
        rfl
      | tail w =>
        rw [binding_tail, ← C.inr_inl]
        apply Eq.trans (binding_tail ..)
        apply binding_concatenate_inl

/-- Renaming the base along `ρ` renames the declaration of a slot `z : Δ ∋ β` along
`(ρ ⇑ʳ Δ) ⇑ʳ β`. -/
theorem declaration_rename {Ω Ω' : C.Arity} (ρ : Ω →ʳ Ω') :
  ∀ {Δ : C.Arity} (T : dTel Ω Δ) {β : C.Arity} (z : Δ ∋ β),
    (rename ρ T).declaration z = Bd.rename ((ρ ⇑ʳ Δ) ⇑ʳ β) (T.declaration z)
  | _, .nil, _, z => (C.unit_is_empty z).elim
  | _, .cons bind boundary rest, _, z => by
      induction z using slotCases with
      | head =>
        simp only [rename, declaration_head, ← Bd.rename_comp, ← Renaming.extend_comp,
          Renaming.inl_comp]
      | tail w =>
        rw [rename, declaration_tail, declaration_tail, Renaming.extend_assoc]
        apply declaration_rename

/-- Renaming the base along `ρ` renames the base of the entries a slot binds along
`ρ ⇑ʳ Δ`. -/
theorem binding_rename {Ω Ω' : C.Arity} (ρ : Ω →ʳ Ω') :
  ∀ {Δ : C.Arity} (T : dTel Ω Δ) {β : C.Arity} (z : Δ ∋ β),
    (rename ρ T).binding z = rename (ρ ⇑ʳ Δ) (T.binding z)
  | _, .nil, _, z => (C.unit_is_empty z).elim
  | _, .cons bind boundary rest, _, z => by
      induction z using slotCases with
      | head =>
        simp only [rename, binding_head, ← rename_comp, Renaming.inl_comp]
      | tail w =>
        rw [rename, binding_tail, binding_tail, Renaming.extend_assoc]
        apply binding_rename

/-- If `κ (ρ x) = ⟦ ρ' ⇑ʳ α ⟧ʳ (κ' x)` for every slot `x : Γ ∋ α`, then acting on
the base by `κ` after renaming it along `ρ` is renaming it along `ρ'` after acting
by `κ'`. -/
theorem actBase_square
    {Γ Γ' Δ Δ' : C.Arity}
    (ρ : Γ →ʳ Γ') (ρ' : Δ →ʳ Δ') (κ : Subst Γ' Δ') (κ' : Subst Γ Δ)
    (h : ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α), κ (ρ x) = ⟦ ρ' ⇑ʳ α ⟧ʳ (κ' x)) :
  ∀ {Ψ : C.Arity} (T : dTel Γ Ψ), actBase κ (rename ρ T) = rename ρ' (actBase κ' T)
  | _, .nil => rfl
  | _, .cons bind boundary rest => by
      simp only [rename, actBase]
      congr 1
      · apply actBase_square ρ ρ' κ κ' h
      · apply Bd.act_square ρ ρ' κ κ' h
      · apply actBase_square _ _ _ _ (lift_square ρ ρ' κ κ' h _)

/-- Filling the block `Ω` by `σ` commutes with renaming the base `Γ` along `ρ`,
when the fillers of `σ` are renamed along `ρ` as well. -/
theorem instantiate_rename
    {Γ Γ' Ω Ψ : C.Arity}
    (ρ : Γ →ʳ Γ') (σ : Subst Ω Γ) (T : dTel (Γ ⋈ Ω) Ψ) :
  instantiate (fun ⦃Λ⦄ i => ⟦ ρ ⇑ʳ Λ ⟧ʳ (σ i)) (rename (ρ ⇑ʳ Ω) T)
    = rename ρ (instantiate σ T)
  := by
  apply actBase_square
  intro α x
  rcases C.cover Γ Ω x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · simp only [Renaming.extend_inl, Subst.copair_inl, Subst.id, Renaming.act_eta]
  · simp only [Renaming.extend_inr, Subst.copair_inr]

/-- Acting on the base by `κ` acts on the declaration of a slot `z : Δ ∋ β` by
`Subst.lift κ Δ` at depth `β`. -/
theorem declaration_actBase {Ω Ω' : C.Arity} (κ : Subst Ω Ω') :
  ∀ {Δ : C.Arity} (T : dTel Ω Δ) {β : C.Arity} (z : Δ ∋ β),
    (actBase κ T).declaration z
      = Bd.act (Γ := 1) (Ξ := Ω' ⋈ Δ) (Subst.lift κ Δ) β (T.declaration z)
  | _, .nil, _, z => (C.unit_is_empty z).elim
  | _, .cons bind boundary rest, _, z => by
      induction z using slotCases with
      | head =>
        rw [actBase, declaration_head, declaration_head]
        symm
        apply Bd.act_square
        intro _ x
        apply Subst.lift_inl
      | tail w =>
        rw [actBase, declaration_tail, declaration_tail, Subst.lift_assoc]
        apply declaration_actBase

/-- Acting on the base by `κ` acts on the base of the entries a slot binds by
`Subst.lift κ Δ`. -/
theorem binding_actBase {Ω Ω' : C.Arity} (κ : Subst Ω Ω') :
  ∀ {Δ : C.Arity} (T : dTel Ω Δ) {β : C.Arity} (z : Δ ∋ β),
    (actBase κ T).binding z = actBase (Subst.lift κ Δ) (T.binding z)
  | _, .nil, _, z => (C.unit_is_empty z).elim
  | _, .cons bind boundary rest, _, z => by
      induction z using slotCases with
      | head =>
        rw [actBase, binding_head, binding_head]
        symm
        apply actBase_square
        intro _ x
        apply Subst.lift_inl
      | tail w =>
        rw [actBase, binding_tail, binding_tail, Subst.lift_assoc]
        apply binding_actBase

/-- Acting on the base by the identity substitution is the identity. -/
theorem actBase_id :
  ∀ {Γ Ψ : C.Arity} (T : dTel Γ Ψ), actBase (Subst.id Γ) T = T
  | _, _, .nil => rfl
  | _, _, .cons bind boundary rest => by
      simp only [actBase, Subst.lift_id, Bd.act_id, actBase_id]

/-- Acting on the base by `Subst.comp κ θ` is acting by `κ` and then by `θ`. -/
theorem actBase_comp {Γ Δ Ξ : C.Arity} (κ : Subst Γ Δ) (θ : Subst Δ Ξ) :
  ∀ {Ψ : C.Arity} (T : dTel Γ Ψ),
    actBase (Subst.comp (Γ := 1) κ θ) T = actBase θ (actBase κ T)
  | _, .nil => rfl
  | _, .cons bind boundary rest => by
      simp only [actBase]
      congr 1
      · apply actBase_comp
      · apply Bd.act_comp
      · rw [Subst.lift_comp]
        apply actBase_comp

/-- Renaming the base of `concatenate T U` along `ρ` renames the base of `T` along
`ρ` and that of `U` along `ρ ⇑ʳ Φ`. -/
theorem rename_concatenate {Γ Γ' Φ Ψ : C.Arity} (ρ : Γ →ʳ Γ') :
  ∀ (T : dTel Γ Φ) (U : dTel (Γ ⋈ Φ) Ψ),
    rename ρ (concatenate T U) = concatenate (rename ρ T) (rename (ρ ⇑ʳ Φ) U)
  | .nil, U => by
      rw [Renaming.extend_unit]
      rfl
  | .cons bind boundary rest, U => by
      simp only [concatenate, rename, rename_concatenate, Renaming.extend_assoc]
      rfl

/-- Acting by `Subst.ofRenaming ρ` on the base is renaming the base by `ρ`. -/
theorem actBase_ofRenaming {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) :
  ∀ {Ψ : C.Arity} (T : dTel Γ Ψ), actBase (Subst.ofRenaming ρ) T = rename ρ T
  | _, .nil => rfl
  | _, .cons bind boundary rest => by
      simp only [actBase, rename, Subst.lift_ofRenaming, actBase_ofRenaming]
      congr 1
      apply Bd.act_ofRenaming

/-- Filling the block `Ω` by `τ` and then acting on the base by `κ` is acting by
`Subst.lift κ Ω` and then filling `Ω` by the fillers of `τ` acted on by `κ`. -/
theorem actBase_instantiate
    {Γ Γ' Ω Ψ : C.Arity}
    (κ : Subst Γ Γ') (τ : Subst Ω Γ) (T : dTel (Γ ⋈ Ω) Ψ) :
  actBase κ (instantiate τ T)
    = instantiate (fun ⦃Λ⦄ i => Subst.act (Γ := 1) κ Λ (τ i))
        (actBase (Subst.lift κ Ω) T)
  := by
  rw [instantiate, instantiate, ← actBase_comp, ← actBase_comp]
  congr 1
  funext β x
  rcases C.cover Γ Ω x with ⟨w, rfl⟩ | ⟨i, rfl⟩
  · simp only [Subst.comp, Subst.copair_inl, Subst.lift_inl]
    apply Eq.trans (act_η κ β w)
    symm
    trans
    · apply act_rename_cancel _ (𝟙ʳ Γ')
      intro _ u
      apply Subst.copair_inl
    · rw [Renaming.extend_id, Renaming.act_id]
  · simp only [Subst.comp, Subst.copair_inr, Subst.lift_inr]
    symm
    apply Eq.trans (act_η _ β (C.inr i))
    apply Subst.copair_inr

/-- Renaming the base along the identity is the identity. -/
theorem rename_id :
  ∀ {Γ Ψ : C.Arity} (T : dTel Γ Ψ), rename (𝟙ʳ Γ) T = T
  | _, _, .nil => rfl
  | _, _, .cons bind boundary rest => by
      simp only [rename, Renaming.extend_id, Bd.rename_id, rename_id]

/-- If `κ (ρ x)` is the η-expansion of `ρ' x` for every slot `x`, then acting on the
base by `κ` after renaming it along `ρ` is renaming it along `ρ'`. -/
theorem actBase_rename_cancel
    {Γ Δ' Γ' : C.Arity}
    (ρ : Γ →ʳ Δ') (ρ' : Γ →ʳ Γ') (κ : Subst Δ' Γ')
    (h : ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α), κ (ρ x) = Expr.η (ρ' x)) :
  ∀ {Ψ : C.Arity} (T : dTel Γ Ψ), actBase κ (rename ρ T) = rename ρ' T
  := by
  intro Ψ T
  rw [actBase_square ρ ρ' κ (Subst.id Γ), actBase_id]
  intro α x
  simp only [h, Subst.id, Renaming.act_eta]

/-- Renaming the base along `Renaming.inl Δ Ω ⇑ʳ Ω` and then filling the second block
`Ω` by `Subst.instId Δ Ω` returns the telescope. -/
theorem instantiate_rename_inl {Δ Ω Ψ : C.Arity} (T : dTel (Δ ⋈ Ω) Ψ) :
  instantiate (Subst.instId Δ Ω) (rename (Renaming.inl Δ Ω ⇑ʳ Ω) T) = T
  := by
  rw [instantiate, actBase_rename_cancel (Renaming.inl Δ Ω ⇑ʳ Ω) (𝟙ʳ (Δ ⋈ Ω)), rename_id]
  intro γ x
  rcases C.cover Δ Ω x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · rw [Renaming.extend_inl, Subst.copair_inl]
    rfl
  · rw [Renaming.extend_inr, Subst.copair_inr]
    rfl

/-- The declaration of `z` in `rename (Renaming.inl Δ Ω) Θ`, with the slots `Ω` of
the telescope filled by `Subst.instId Δ Ω`, is the declaration of `z` in `Θ`. -/
theorem act_declaration_instId {Δ Ω Λ : C.Arity} (Θ : dTel Δ Ω) (z : Ω ∋ Λ) :
  Bd.act (Ξ := 1) (Subst.instId Δ Ω) Λ ((rename (Renaming.inl Δ Ω) Θ).declaration z)
    = Θ.declaration z
  := by
  rw [declaration_rename]
  apply Bd.act_instId_weaken

/-- The entries `z` binds in `rename (Renaming.inl Δ Ω) Θ`, with the slots `Ω` of the
telescope filled by `Subst.instId Δ Ω`, are the entries `z` binds in `Θ`. -/
theorem instantiate_binding_instId {Δ Ω Λ : C.Arity} (Θ : dTel Δ Ω) (z : Ω ∋ Λ) :
  instantiate (Subst.instId Δ Ω) ((rename (Renaming.inl Δ Ω) Θ).binding z) = Θ.binding z
  := by
  rw [binding_rename]
  apply instantiate_rename_inl

/-- Renaming the base along `Renaming.inr Γ' Γ` and then filling the block `Γ` by `s`
is acting on the base by `s`. -/
theorem instantiate_weaken {Γ Γ' Χ : C.Arity} (s : Subst Γ Γ') (T : dTel Γ Χ) :
  instantiate s (rename (Renaming.inr Γ' Γ) T) = actBase s T
  := by
  rw [instantiate, actBase_square (Renaming.inr Γ' Γ) (𝟙ʳ Γ') _ s, rename_id]
  intro α x
  rw [Renaming.inr, Subst.copair_inr, Renaming.extend_id, Renaming.act_id]

/-- Concatenating the empty telescope changes nothing. -/
theorem concatenate_nil {Ω : C.Arity} :
  ∀ {Δ : C.Arity} (Θ : dTel Ω Δ), concatenate Θ .nil = Θ
  | _, .nil => rfl
  | _, .cons bind boundary rest => congrArg (cons bind boundary) (concatenate_nil rest)

/-- Concatenation is associative. -/
theorem concatenate_assoc {Ω Δ Ξ Φ : C.Arity} :
  ∀ (Θ : dTel Ω Δ) (Ψ : dTel (Ω ⋈ Δ) Ξ) (Χ : dTel ((Ω ⋈ Δ) ⋈ Ξ) Φ),
    concatenate (concatenate Θ Ψ) Χ = concatenate Θ (concatenate Ψ Χ)
  | .nil, _, _ => rfl
  | .cons bind boundary rest, Ψ, Χ =>
      congrArg (cons bind boundary) (concatenate_assoc rest Ψ Χ)

/-- The boundary of `Expr.ap x args` over the ambient `Ξ`: the declaration of `x`
instantiated by `args`. -/
def boundaryOf {Δ : C.Arity} (Ξ : dTel 1 Δ) : Expr Δ → Bd Δ
  | .ap x args => Bd.instantiate args (Ξ.declaration x)

@[simp]
theorem boundaryOf_ap {Δ α : C.Arity} (Ξ : dTel 1 Δ) (x : Δ ∋ α) (args : Subst α Δ) :
  Ξ.boundaryOf (.ap x args) = Bd.instantiate args (Ξ.declaration x)
  := rfl

/-- Over `Ξ` extended by the entries `x` binds, the boundary of the η-expansion of
`x` is the declaration of `x`. -/
theorem boundaryOf_eta {Δ α : C.Arity} (Ξ : dTel 1 Δ) (x : Δ ∋ α) :
  (concatenate Ξ (Ξ.binding x)).boundaryOf (Expr.η x) = Ξ.declaration x
  := by
  rw [Expr.η.eq_1, boundaryOf_ap, declaration_concatenate_inl]
  apply Bd.instantiate_rename_inl

end dTel

/-- An ambient is a telescope over the unit base. -/
abbrev Ambient (Δ : C.Arity) : Type := dTel 1 Δ

@[inherit_doc dTel.concatenate] infixl:65 " ⋈ " => dTel.concatenate

/-- Fill the block `Ω` of an expression over `Δ ⋈ Ω ⋈ Φ` by `σ`. -/
abbrev Subst.fill {Δ Ω Φ : C.Arity} (σ : Subst Ω Δ) (g : Expr ((Δ ⋈ Ω) ⋈ Φ)) :
    Expr (Δ ⋈ Φ) :=
  Subst.act (Γ := Δ) (Δ := Ω) (Ξ := 1) σ Φ g

/-- Fill the block `Ω` of a boundary over `Δ ⋈ Ω ⋈ Φ` by `σ`. -/
abbrev Bd.fill {Δ Ω Φ : C.Arity} (σ : Subst Ω Δ) (β : Bd ((Δ ⋈ Ω) ⋈ Φ)) :
    Bd (Δ ⋈ Φ) :=
  Bd.act (Γ := Δ) (Δ := Ω) (Ξ := 1) σ Φ β

/-- Fill the block `Ω` of an expression over `Δ ⋈ Ω` by `σ`. -/
abbrev Subst.instantiate {Δ Ω : C.Arity} (σ : Subst Ω Δ) (g : Expr (Δ ⋈ Ω)) : Expr Δ :=
  Subst.act (Γ := Δ) (Δ := Ω) (Ξ := 1) σ 1 g

/-- Act by `s : Subst Γ Γ'` on an expression over `Γ`. -/
abbrev Subst.apply {Γ Γ' : C.Arity} (s : Subst Γ Γ') (g : Expr Γ) : Expr Γ' :=
  Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') s 1 g

/-- Act by `s : Subst Γ Γ'` on a boundary over `Γ`. -/
abbrev Bd.apply {Γ Γ' : C.Arity} (s : Subst Γ Γ') (β : Bd Γ) : Bd Γ' :=
  Bd.act (Γ := 1) (Δ := Γ) (Ξ := Γ') s 1 β

/-- Fill the block `Ω` of the base `Δ ⋈ Ω ⋈ Φ` of a telescope by `σ`. -/
abbrev dTel.fill {Δ Ω Φ Χ : C.Arity} (σ : Subst Ω Δ) (X : dTel ((Δ ⋈ Ω) ⋈ Φ) Χ) :
    dTel (Δ ⋈ Φ) Χ :=
  dTel.actBase (Subst.lift (Subst.copair (Subst.id Δ) σ) Φ) X

/-- Act by `s : Subst Γ Γ'` on every filler of `τ : Subst Χ Γ`. -/
abbrev Subst.applyEach {Γ Γ' Χ : C.Arity} (s : Subst Γ Γ') (τ : Subst Χ Γ) :
    Subst Χ Γ' :=
  fun ⦃Λ⦄ i => Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') s Λ (τ i)

/-- Acting by `s` on the filler of `single t` gives `single` of `t` acted on by `s`
at depth `α`. -/
theorem Subst.applyEach_single {Γ Γ' α : C.Arity} (s : Subst Γ Γ') (t : Expr (Γ ⋈ α)) :
  applyEach s (single t) = single (act (Γ := 1) s α t)
  := by
  rw [← single_eta (applyEach s (single t)), applyEach, single_head]
  rfl

/-- Acting by `s` on every filler of `copair σ τ` is the copair of acting by `s` on
every filler of `σ` and of `τ`. -/
theorem Subst.applyEach_copair
    {Γ Δ Ω Ω' : C.Arity}
    (s : Subst Ω Ω') (σ : Subst Γ Ω) (τ : Subst Δ Ω) :
  applyEach s (copair σ τ) = copair (applyEach s σ) (applyEach s τ)
  := by
  funext α x
  rcases C.cover Γ Δ x with ⟨u, rfl⟩ | ⟨v, rfl⟩
  · simp only [applyEach, copair_inl]
  · simp only [applyEach, copair_inr]

/-- Act by `s : Subst Γ Γ'` on a boundary over `Γ ⋈ Φ` at depth `Φ`. -/
abbrev Bd.applyAt {Γ Γ' : C.Arity} (s : Subst Γ Γ') (Φ : C.Arity) (β : Bd (Γ ⋈ Φ)) :
    Bd (Γ' ⋈ Φ) :=
  Bd.act (Γ := 1) (Δ := Γ) (Ξ := Γ') s Φ β

@[inherit_doc Subst.apply] infixr:70 " ⋆ " => Subst.apply
@[inherit_doc dTel.fill] infixr:70 " ⋆ " => dTel.fill
@[inherit_doc Subst.applyEach] infixr:70 " ⋆ " => Subst.applyEach
@[inherit_doc Bd.apply] infixr:70 " ⋆ " => Bd.apply
@[inherit_doc dTel.actBase] infixr:70 " ⋆ " => dTel.actBase
@[inherit_doc Subst.fill] infixr:70 " ⋆ " => Subst.fill
@[inherit_doc Subst.instantiate] infixr:70 " ⋆ " => Subst.instantiate
@[inherit_doc Bd.instantiate] infixr:70 " ⋆ " => Bd.instantiate
@[inherit_doc Bd.fill] infixr:70 " ⋆ " => Bd.fill
@[inherit_doc dTel.instantiate] infixr:70 " ⋆ " => dTel.instantiate

/-- Renaming an expression along `Renaming.inr Γ' Γ ⇑ʳ Φ` and then filling the block
`Γ` by `s` is acting on it by `s` at depth `Φ`. -/
theorem Subst.act_weaken {Γ Γ' Φ : C.Arity} (s : Subst Γ Γ') (e : Expr (Γ ⋈ Φ)) :
  act (Γ := Γ') (Δ := Γ) (Ξ := 1) s Φ (⟦ Renaming.inr Γ' Γ ⇑ʳ Φ ⟧ʳ e)
    = act (Γ := 1) (Δ := Γ) (Ξ := Γ') s Φ e
  := by
  rw [← act_copair_prefix]
  apply act_copair_inr

/-- Renaming a boundary along `Renaming.inr Γ' Γ ⇑ʳ Φ` and then filling the block `Γ`
by `s` is acting on it by `s` at depth `Φ`. -/
theorem Bd.act_weaken {Γ Γ' Φ : C.Arity} (s : Subst Γ Γ') (β : Bd (Γ ⋈ Φ)) :
  act (Γ := Γ') (Δ := Γ) (Ξ := 1) s Φ (rename (Renaming.inr Γ' Γ ⇑ʳ Φ) β)
    = applyAt s Φ β
  := by
  cases β with
  | sort => rfl
  | of S =>
      apply congrArg of
      apply Subst.act_weaken
  | eq l r => apply congrArg₂ eq <;> apply Subst.act_weaken

/-- Filling the block `Ω ⋈ Φ` by `σ` is the composite of filling `Ω` by the
restriction of `σ` to `Ω`, lifted past `Φ`, and then filling `Φ` by the
restriction of `σ` to `Φ`. -/
theorem Subst.copair_split {Δ Ω Φ : C.Arity} (σ : Subst (Ω ⋈ Φ) Δ) :
  (comp (Γ := 1) (Ξ := Δ)
      (lift (copair (Subst.id Δ) (fun ⦃β⦄ (i : Ω ∋ β) => σ (C.inl i))) Φ)
      (copair (Subst.id Δ) (fun ⦃β⦄ (j : Φ ∋ β) => σ (C.inr j))) :
    Subst (Δ ⋈ Ω ⋈ Φ) Δ)
    = copair (Subst.id Δ) σ
  := by
  funext β x
  rcases C.cover (Δ ⋈ Ω) Φ x with ⟨u, rfl⟩ | ⟨j, rfl⟩
  · rcases C.cover Δ Ω u with ⟨w, rfl⟩ | ⟨i, rfl⟩
    · simp only [comp, lift_copair_inl_inl]
      rw [← C.inl_inl, copair_inl]
      apply Eq.trans (act_η _ β (C.inl w))
      apply copair_inl
    · simp only [comp, lift_copair_inl_inr]
      rw [← C.inr_inl, copair_inr]
      trans
      · apply act_rename_cancel _ (𝟙ʳ Δ)
        intro _ w
        apply copair_inl
      · rw [Renaming.extend_id, Renaming.act_id]
  · simp only [comp, lift_inr]
    rw [← C.inr_inr, copair_inr]
    apply Eq.trans (act_η _ β (C.inr j))
    apply copair_inr

/-- For a slot `x : (Δ ⋈ Ω) ∋ α`, `copair (Subst.id Δ) κ` at `Renaming.inl (Δ ⋈ Ω) Φ x`
is `copair (Subst.id Δ)` of the restriction of `κ` to `Ω` at `x`, renamed along
`𝟙ʳ Δ ⇑ʳ α`. -/
theorem Subst.copair_weaken {Δ Ω Φ : C.Arity} (κ : Subst (Ω ⋈ Φ) Δ) :
  ∀ ⦃α : C.Arity⦄ (x : (Δ ⋈ Ω) ∋ α),
    copair (Subst.id Δ) κ (Renaming.inl (Δ ⋈ Ω) Φ x)
      = ⟦ 𝟙ʳ Δ ⇑ʳ α ⟧ʳ (copair (Subst.id Δ) (fun ⦃β⦄ (w : Ω ∋ β) => κ (C.inl w)) x)
  := by
  intro α x
  rw [Renaming.extend_id, Renaming.act_id]
  rcases C.cover Δ Ω x with ⟨u, rfl⟩ | ⟨v, rfl⟩
  · simp only [Renaming.inl, ← C.inl_inl, copair_inl]
  · simp only [Renaming.inl, ← C.inr_inl, copair_inr]

/-- Filling the block `Ω ⋈ Φ` by `κ` in a boundary renamed along
`Renaming.inl (Δ ⋈ Ω) Φ ⇑ʳ Λ` is filling `Ω` by the restriction of `κ` to `Ω`. -/
theorem Bd.fill_weaken_inl
    {Δ Ω Φ Λ : C.Arity}
    (κ : Subst (Ω ⋈ Φ) Δ) (β : Bd ((Δ ⋈ Ω) ⋈ Λ)) :
  fill κ (rename (Renaming.inl (Δ ⋈ Ω) Φ ⇑ʳ Λ) β)
    = fill (fun ⦃γ⦄ (w : Ω ∋ γ) => κ (C.inl w)) β
  := by
  rw [fill, fill, ← act_copair_prefix, ← act_copair_prefix]
  apply Eq.trans (act_square _ (𝟙ʳ Δ) _ _ (Subst.copair_weaken κ) Λ β)
  rw [Renaming.extend_id]
  apply rename_id

/-- Filling the block `Ω ⋈ Φ` by `κ` in a telescope renamed along
`Renaming.inl (Δ ⋈ Ω) Φ` is filling `Ω` by the restriction of `κ` to `Ω`. -/
theorem dTel.instantiate_weaken_inl
    {Δ Ω Φ Λ : C.Arity}
    (κ : Subst (Ω ⋈ Φ) Δ) (T : dTel (Δ ⋈ Ω) Λ) :
  instantiate κ (rename (Renaming.inl (Δ ⋈ Ω) Φ) T)
    = instantiate (fun ⦃γ⦄ (w : Ω ∋ γ) => κ (C.inl w)) T
  := by
  apply Eq.trans (actBase_square _ (𝟙ʳ Δ) _ _ (Subst.copair_weaken κ) T)
  apply rename_id

/-- Filling by `κ` the declaration of a slot of `Θ` in `concatenate Θ X` is filling
by the restriction of `κ` to `Ω` its declaration in `Θ`. -/
theorem dTel.declaration_left_instantiate
    {Δ Ω Φ Λ : C.Arity}
    (Θ : dTel Δ Ω) (X : dTel (Δ ⋈ Ω) Φ) (κ : Subst (Ω ⋈ Φ) Δ) (w : Ω ∋ Λ) :
  Bd.fill κ ((concatenate Θ X).declaration (C.inl w))
    = Bd.fill (fun ⦃γ⦄ (v : Ω ∋ γ) => κ (C.inl v)) (Θ.declaration w)
  := by
  rw [declaration_concatenate_inl]
  apply Bd.fill_weaken_inl

/-- Filling by `κ` the entries a slot of `Θ` binds in `concatenate Θ X` is filling
by the restriction of `κ` to `Ω` the entries it binds in `Θ`. -/
theorem dTel.binding_left_instantiate
    {Δ Ω Φ Λ : C.Arity}
    (Θ : dTel Δ Ω) (X : dTel (Δ ⋈ Ω) Φ) (κ : Subst (Ω ⋈ Φ) Δ) (w : Ω ∋ Λ) :
  instantiate κ ((concatenate Θ X).binding (C.inl w))
    = instantiate (fun ⦃γ⦄ (v : Ω ∋ γ) => κ (C.inl v)) (Θ.binding w)
  := by
  rw [binding_concatenate_inl]
  apply instantiate_weaken_inl

/-- Filling by the restriction of `κ` to `Φ` the declaration of `z` in `X` with `Ω`
filled by the restriction of `κ` to `Ω` is filling by `κ` the declaration of
`C.inr z` in `concatenate Θ X`. -/
theorem dTel.declaration_right_instantiate
    {Δ Ω Φ Λ : C.Arity}
    (Θ : dTel Δ Ω) (X : dTel (Δ ⋈ Ω) Φ) (κ : Subst (Ω ⋈ Φ) Δ) (z : Φ ∋ Λ) :
  Bd.fill (fun ⦃γ⦄ (j : Φ ∋ γ) => κ (C.inr j))
      ((instantiate (fun ⦃γ⦄ (i : Ω ∋ γ) => κ (C.inl i)) X).declaration z)
    = Bd.fill κ ((concatenate Θ X).declaration (C.inr z))
  := by
  rw [declaration_concatenate_inr, instantiate, declaration_actBase, Bd.fill, Bd.fill,
    ← Bd.act_copair_prefix, ← Bd.act_copair_prefix, ← Bd.act_comp, Subst.copair_split]
  rfl

/-- Filling by the restriction of `κ` to `Φ` the entries `z` binds in `X` with `Ω`
filled by the restriction of `κ` to `Ω` is filling by `κ` the entries `C.inr z`
binds in `concatenate Θ X`. -/
theorem dTel.binding_right_instantiate
    {Δ Ω Φ Λ : C.Arity}
    (Θ : dTel Δ Ω) (X : dTel (Δ ⋈ Ω) Φ) (κ : Subst (Ω ⋈ Φ) Δ) (z : Φ ∋ Λ) :
  instantiate (fun ⦃γ⦄ (j : Φ ∋ γ) => κ (C.inr j))
      ((instantiate (fun ⦃γ⦄ (i : Ω ∋ γ) => κ (C.inl i)) X).binding z)
    = instantiate κ ((concatenate Θ X).binding (C.inr z))
  := by
  rw [binding_concatenate_inr, instantiate, instantiate, instantiate, binding_actBase,
    ← actBase_comp, ← Subst.copair_split]
  rfl

/-- Filling by `Subst.copair σ τ` the declaration of a slot of `Θ` in
`concatenate Θ X` is filling by `σ` its declaration in `Θ`. -/
theorem dTel.declaration_left_copair
    {Δ Ω Φ Λ : C.Arity}
    (Θ : dTel Δ Ω) (X : dTel (Δ ⋈ Ω) Φ) (σ : Subst Ω Δ) (τ : Subst Φ Δ) (w : Ω ∋ Λ) :
  Bd.fill (Subst.copair σ τ) ((concatenate Θ X).declaration (C.inl w))
    = Bd.fill σ (Θ.declaration w)
  := by
  rw [declaration_left_instantiate, Subst.copair_left]

/-- Filling by `Subst.copair σ τ` the entries a slot of `Θ` binds in
`concatenate Θ X` is filling by `σ` the entries it binds in `Θ`. -/
theorem dTel.binding_left_copair
    {Δ Ω Φ Λ : C.Arity}
    (Θ : dTel Δ Ω) (X : dTel (Δ ⋈ Ω) Φ) (σ : Subst Ω Δ) (τ : Subst Φ Δ) (w : Ω ∋ Λ) :
  instantiate (Subst.copair σ τ) ((concatenate Θ X).binding (C.inl w))
    = instantiate σ (Θ.binding w)
  := by
  rw [binding_left_instantiate, Subst.copair_left]

/-- Filling by `Subst.copair σ τ` the declaration of a slot of `X` in
`concatenate Θ X` is filling by `τ` its declaration in `instantiate σ X`. -/
theorem dTel.declaration_right_copair
    {Δ Ω Φ Λ : C.Arity}
    (Θ : dTel Δ Ω) (X : dTel (Δ ⋈ Ω) Φ) (σ : Subst Ω Δ) (τ : Subst Φ Δ) (z : Φ ∋ Λ) :
  Bd.fill (Subst.copair σ τ) ((concatenate Θ X).declaration (C.inr z))
    = Bd.fill τ ((instantiate σ X).declaration z)
  := by
  rw [← declaration_right_instantiate Θ X, Subst.copair_left, Subst.copair_right]

/-- Filling by `Subst.copair σ τ` the entries a slot of `X` binds in
`concatenate Θ X` is filling by `τ` the entries it binds in `instantiate σ X`. -/
theorem dTel.binding_right_copair
    {Δ Ω Φ Λ : C.Arity}
    (Θ : dTel Δ Ω) (X : dTel (Δ ⋈ Ω) Φ) (σ : Subst Ω Δ) (τ : Subst Φ Δ) (z : Φ ∋ Λ) :
  instantiate (Subst.copair σ τ) ((concatenate Θ X).binding (C.inr z))
    = instantiate τ ((instantiate σ X).binding z)
  := by
  rw [← binding_right_instantiate Θ X, Subst.copair_left, Subst.copair_right]

/-- Filling by `σ` the entries the first slot of `cons bind boundary rest` binds
gives `bind`. -/
theorem dTel.binding_head_instantiate
    {Δ α Ω : C.Arity}
    (bind : dTel Δ α) (boundary : Bd (Δ ⋈ α)) (rest : dTel (Δ ⋈ C.single α) Ω)
    (σ : Subst (C.single α ⋈ Ω) Δ) :
  σ ⋆ (cons bind boundary rest).binding (C.inl (C.singleSlot α)) = bind
  := by
  rw [binding_head, instantiate, actBase_rename_cancel _ (𝟙ʳ Δ), rename_id]
  intro _ x
  apply Subst.copair_inl

/-- Filling by `σ` the declaration of the first slot of `cons bind boundary rest`
gives `boundary`. -/
theorem dTel.declaration_head_instantiate
    {Δ α Ω : C.Arity}
    (bind : dTel Δ α) (boundary : Bd (Δ ⋈ α)) (rest : dTel (Δ ⋈ C.single α) Ω)
    (σ : Subst (C.single α ⋈ Ω) Δ) :
  σ ⋆ (cons bind boundary rest).declaration (C.inl (C.singleSlot α)) = boundary
  := by
  rw [declaration_head, Bd.fill, ← Bd.act_copair_prefix]
  trans
  · apply Bd.act_rename_cancel _ (𝟙ʳ Δ)
    intro _ x
    apply Subst.copair_inl
  · rw [Renaming.extend_id, Bd.rename_id]

/-- Filling by `σ` the entries `C.inr y` binds in `cons bind boundary rest` is
filling by the restriction of `σ` to `Ω` the entries `y` binds in `rest` with
`C.single α` filled by the restriction of `σ` to `C.single α`. -/
theorem dTel.binding_tail_instantiate
    {Δ α Ω Λ : C.Arity}
    (bind : dTel Δ α) (boundary : Bd (Δ ⋈ α)) (rest : dTel (Δ ⋈ C.single α) Ω)
    (σ : Subst (C.single α ⋈ Ω) Δ) (y : Ω ∋ Λ) :
  σ ⋆ (cons bind boundary rest).binding (C.inr y)
    = (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j)) ⋆
        (instantiate (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) rest).binding y
  := by
  rw [binding_tail, instantiate, instantiate, instantiate, binding_actBase, ← actBase_comp,
    ← Subst.copair_split]
  rfl

/-- Filling by `σ` the declaration of `C.inr y` in `cons bind boundary rest` is
filling by the restriction of `σ` to `Ω` the declaration of `y` in `rest` with
`C.single α` filled by the restriction of `σ` to `C.single α`. -/
theorem dTel.declaration_tail_instantiate
    {Δ α Ω Λ : C.Arity}
    (bind : dTel Δ α) (boundary : Bd (Δ ⋈ α)) (rest : dTel (Δ ⋈ C.single α) Ω)
    (σ : Subst (C.single α ⋈ Ω) Δ) (y : Ω ∋ Λ) :
  σ ⋆ (cons bind boundary rest).declaration (C.inr y)
    = (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j)) ⋆
        (instantiate (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) rest).declaration y
  := by
  rw [declaration_tail, instantiate, declaration_actBase, Bd.fill, Bd.fill,
    ← Bd.act_copair_prefix, ← Bd.act_copair_prefix, ← Bd.act_comp, Subst.copair_split]
  rfl
