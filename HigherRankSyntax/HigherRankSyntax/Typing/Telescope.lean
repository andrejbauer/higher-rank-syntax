import HigherRankSyntax.Typing.Boundary

/-!
# Decorated telescopes

A telescope is a list of entries over a base.  Each entry carries the telescope
of entries it binds and its declaration; the entries after it are read over the
base extended by it.  A slot's declaration and the entries it binds are read off
by recursion, weakened into the whole telescope.
-/

/-- A telescope of entries over a base: each entry carries the entries it binds
and its declaration, and the entries after it are read over the base extended by
it. -/
inductive dTel : C.Arity → C.Arity → Type where
  | nil {Ω : C.Arity} : dTel Ω 1
  | cons {Ω α Δ : C.Arity} (binding : dTel Ω α) (boundary : Bd (Ω ⋈ α))
      (rest : dTel (Ω ⋈ C.single α) Δ) : dTel Ω (C.single α ⋈ Δ)

/-- A slot of a telescope with at least one entry is its first entry or a later
one. -/
theorem slotCases {α Δ : C.Arity} {motive : ∀ ⦃β : C.Arity⦄, (C.single α ⋈ Δ) ∋ β → Prop}
    (head : motive (C.inl (C.singleSlot α)))
    (tail : ∀ ⦃β : C.Arity⦄ (y : Δ ∋ β), motive (C.inr y))
    ⦃β : C.Arity⦄ (x : (C.single α ⋈ Δ) ∋ β) : motive x := by
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

/-- Reindexing along a composite is successive reindexing. -/
theorem rename_comp {Γ Δ Ξ : C.Arity} (ρ : Γ →ʳ Δ) (θ : Δ →ʳ Ξ) :
    ∀ {Ψ : C.Arity} (T : dTel Γ Ψ), rename (θ ∘ʳ ρ) T = rename θ (rename ρ T)
  | _, .nil => rfl
  | _, .cons (α := α) bind boundary rest => by
      simp only [rename]
      congr 1
      · exact rename_comp ρ θ bind
      · exact (congrArg (fun s => Bd.rename s boundary) (Renaming.extend_comp ρ θ α)).trans
          (Bd.rename_comp _ _ _)
      · refine Eq.trans ?_ (rename_comp (ρ ⇑ʳ C.single α) (θ ⇑ʳ C.single α) rest)
        exact congrArg (fun s => rename s rest) (Renaming.extend_comp ρ θ (C.single α))

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

/-- A telescope over a base extended by a block, with the block filled. -/
def instantiate {Γ Ω Ψ : C.Arity} (σ : Subst Ω Γ) (Θ : dTel (Γ ⋈ Ω) Ψ) : dTel Γ Ψ :=
  actBase (Subst.copair (Subst.id Γ) σ) Θ

/-- The declaration of a slot, over the whole telescope. -/
def declaration : {Ω Δ : C.Arity} → dTel Ω Δ → {β : C.Arity} → (Δ ∋ β) → Bd (Ω ⋈ Δ ⋈ β)
  | _, _, .nil, _, x => (C.unit_is_empty x).elim
  | Ω, _, .cons (α := α) (Δ := Δ) _ boundary rest, β, x =>
      match C.split (C.single α) Δ x with
      | .inl z =>
          cast (congrArg (fun γ => Bd (Ω ⋈ (C.single α ⋈ Δ) ⋈ γ)) (C.single_arity z).symm)
            (Bd.rename (Renaming.inl Ω (C.single α ⋈ Δ) ⇑ʳ α) boundary)
      | .inr y => declaration rest y

/-- The entries a slot binds, over the whole telescope. -/
def binding : {Ω Δ : C.Arity} → dTel Ω Δ → {β : C.Arity} → (Δ ∋ β) → dTel (Ω ⋈ Δ) β
  | _, _, .nil, _, x => (C.unit_is_empty x).elim
  | Ω, _, .cons (α := α) (Δ := Δ) bind _ rest, β, x =>
      match C.split (C.single α) Δ x with
      | .inl z =>
          cast (congrArg (fun γ => dTel (Ω ⋈ (C.single α ⋈ Δ)) γ) (C.single_arity z).symm)
            (rename (Renaming.inl Ω (C.single α ⋈ Δ)) bind)
      | .inr y => binding rest y

@[simp] theorem declaration_head {Ω α Δ : C.Arity} (bind : dTel Ω α)
    (boundary : Bd (Ω ⋈ α)) (rest : dTel (Ω ⋈ C.single α) Δ) :
    declaration (.cons bind boundary rest) (C.inl (C.singleSlot α))
      = Bd.rename (Renaming.inl Ω (C.single α ⋈ Δ) ⇑ʳ α) boundary := by
  simp only [declaration, C.split_inl]
  rfl

@[simp] theorem declaration_tail {Ω α Δ β : C.Arity} (bind : dTel Ω α)
    (boundary : Bd (Ω ⋈ α)) (rest : dTel (Ω ⋈ C.single α) Δ) (y : Δ ∋ β) :
    declaration (.cons bind boundary rest) (C.inr y) = declaration rest y := by
  simp only [declaration, C.split_inr]

@[simp] theorem binding_head {Ω α Δ : C.Arity} (bind : dTel Ω α)
    (boundary : Bd (Ω ⋈ α)) (rest : dTel (Ω ⋈ C.single α) Δ) :
    binding (.cons bind boundary rest) (C.inl (C.singleSlot α))
      = rename (Renaming.inl Ω (C.single α ⋈ Δ)) bind := by
  simp only [binding, C.split_inl]
  rfl

@[simp] theorem binding_tail {Ω α Δ β : C.Arity} (bind : dTel Ω α)
    (boundary : Bd (Ω ⋈ α)) (rest : dTel (Ω ⋈ C.single α) Δ) (y : Δ ∋ β) :
    binding (.cons bind boundary rest) (C.inr y) = binding rest y := by
  simp only [binding, C.split_inr]

/-- The declaration of a slot in the appended part. -/
theorem declaration_concatenate_inr {Ω Δ Ξ : C.Arity} :
    ∀ (Θ : dTel Ω Δ) (Ψ : dTel (Ω ⋈ Δ) Ξ) {β : C.Arity} (z : Ξ ∋ β),
      (concatenate Θ Ψ).declaration (C.inr z) = Ψ.declaration z
  | .nil, Ψ, β, z => by
      refine Eq.trans (congrArg (fun w => (concatenate .nil Ψ).declaration w) ?_) rfl
      exact C.unit_left Ξ z
  | .cons (α := α) (Δ := Δ') bind boundary rest, Ψ, β, z => by
      refine Eq.trans (congrArg (fun w => declaration (.cons bind boundary
        (concatenate rest Ψ)) w) (C.inr_inr (C.single α) Δ' Ξ z).symm) ?_
      refine Eq.trans (declaration_tail _ _ _ _) ?_
      exact declaration_concatenate_inr rest Ψ z

/-- The declaration of a slot in the original part. -/
theorem declaration_concatenate_inl {Ω Δ Ξ : C.Arity} :
    ∀ (Θ : dTel Ω Δ) (Ψ : dTel (Ω ⋈ Δ) Ξ) {β : C.Arity} (y : Δ ∋ β),
      (concatenate Θ Ψ).declaration (C.inl y)
        = Bd.rename (Renaming.inl (Ω ⋈ Δ) Ξ ⇑ʳ β) (Θ.declaration y)
  | .nil, _, _, y => (C.unit_is_empty y).elim
  | .cons (α := α) (Δ := Δ') bind boundary rest, Ψ, β, y => by
      refine slotCases (α := α) (Δ := Δ')
        (motive := fun ⦃β⦄ y =>
          (concatenate (.cons bind boundary rest) Ψ).declaration (C.inl y)
            = Bd.rename (Renaming.inl (Ω ⋈ (C.single α ⋈ Δ')) Ξ ⇑ʳ β)
                ((dTel.cons bind boundary rest).declaration y)) ?head ?tail y
      case head =>
        refine Eq.trans (congrArg (fun w => declaration (.cons bind boundary
          (concatenate rest Ψ)) w) (C.inl_inl (C.single α) Δ' Ξ (C.singleSlot α)).symm) ?_
        refine Eq.trans (declaration_head _ _ _) ?_
        refine Eq.trans ?_ (congrArg (Bd.rename (Renaming.inl (Ω ⋈ (C.single α ⋈ Δ')) Ξ ⇑ʳ α))
          (declaration_head bind boundary rest)).symm
        refine Eq.trans ?_ (Bd.rename_comp _ _ _)
        exact congrArg (fun ρ => Bd.rename ρ boundary)
          (((congrArg (fun ρ => ρ ⇑ʳ α) (Renaming.inl_inl Ω (C.single α ⋈ Δ') Ξ)).symm).trans
            (Renaming.extend_comp _ _ α))
      case tail =>
        intro γ w
        refine Eq.trans (congrArg (fun v => declaration (.cons bind boundary
          (concatenate rest Ψ)) v) (C.inr_inl (C.single α) Δ' Ξ w).symm) ?_
        refine Eq.trans (declaration_tail _ _ _ _) ?_
        refine Eq.trans (declaration_concatenate_inl rest Ψ w) ?_
        exact congrArg (Bd.rename (Renaming.inl ((Ω ⋈ C.single α) ⋈ Δ') Ξ ⇑ʳ γ))
          (declaration_tail bind boundary rest w).symm

/-- The entries bound by a slot in the appended part. -/
theorem binding_concatenate_inr {Ω Δ Ξ : C.Arity} :
    ∀ (Θ : dTel Ω Δ) (Ψ : dTel (Ω ⋈ Δ) Ξ) {β : C.Arity} (z : Ξ ∋ β),
      (concatenate Θ Ψ).binding (C.inr z) = Ψ.binding z
  | .nil, Ψ, β, z => by
      refine Eq.trans (congrArg (fun w => (concatenate .nil Ψ).binding w) ?_) rfl
      exact C.unit_left Ξ z
  | .cons (α := α) (Δ := Δ') bind boundary rest, Ψ, β, z => by
      refine Eq.trans (congrArg (fun w => binding (.cons bind boundary
        (concatenate rest Ψ)) w) (C.inr_inr (C.single α) Δ' Ξ z).symm) ?_
      refine Eq.trans (binding_tail _ _ _ _) ?_
      exact binding_concatenate_inr rest Ψ z

/-- The entries bound by a slot in the original part. -/
theorem binding_concatenate_inl {Ω Δ Ξ : C.Arity} :
    ∀ (Θ : dTel Ω Δ) (Ψ : dTel (Ω ⋈ Δ) Ξ) {β : C.Arity} (y : Δ ∋ β),
      (concatenate Θ Ψ).binding (C.inl y)
        = dTel.rename (Renaming.inl (Ω ⋈ Δ) Ξ) (Θ.binding y)
  | .nil, _, _, y => (C.unit_is_empty y).elim
  | .cons (α := α) (Δ := Δ') bind boundary rest, Ψ, β, y => by
      refine slotCases (α := α) (Δ := Δ')
        (motive := fun ⦃β⦄ y =>
          (concatenate (.cons bind boundary rest) Ψ).binding (C.inl y)
            = dTel.rename (Renaming.inl (Ω ⋈ (C.single α ⋈ Δ')) Ξ)
                ((dTel.cons bind boundary rest).binding y)) ?head ?tail y
      case head =>
        refine Eq.trans (congrArg (fun w => binding (.cons bind boundary
          (concatenate rest Ψ)) w) (C.inl_inl (C.single α) Δ' Ξ (C.singleSlot α)).symm) ?_
        refine Eq.trans (binding_head _ _ _) ?_
        refine Eq.trans ?_ (congrArg (dTel.rename (Renaming.inl (Ω ⋈ (C.single α ⋈ Δ')) Ξ))
          (binding_head bind boundary rest)).symm
        refine Eq.trans ?_ (rename_comp _ _ _)
        exact congrArg (fun ρ => dTel.rename ρ bind)
          (Renaming.inl_inl Ω (C.single α ⋈ Δ') Ξ).symm
      case tail =>
        intro γ w
        refine Eq.trans (congrArg (fun v => binding (.cons bind boundary
          (concatenate rest Ψ)) v) (C.inr_inl (C.single α) Δ' Ξ w).symm) ?_
        refine Eq.trans (binding_tail _ _ _ _) ?_
        refine Eq.trans (binding_concatenate_inl rest Ψ w) ?_
        exact congrArg (dTel.rename (Renaming.inl ((Ω ⋈ C.single α) ⋈ Δ') Ξ))
          (binding_tail bind boundary rest w).symm

/-- The declaration of a slot, after reindexing the base. -/
theorem declaration_rename {Ω Ω' : C.Arity} (ρ : Ω →ʳ Ω') :
    ∀ {Δ : C.Arity} (T : dTel Ω Δ) {β : C.Arity} (z : Δ ∋ β),
      (rename ρ T).declaration z = Bd.rename ((ρ ⇑ʳ Δ) ⇑ʳ β) (T.declaration z)
  | _, .nil, _, z => (C.unit_is_empty z).elim
  | _, .cons (α := α) (Δ := Δ') bind boundary rest, β, z => by
      refine slotCases (α := α) (Δ := Δ')
        (motive := fun ⦃β⦄ z =>
          (rename ρ (.cons bind boundary rest)).declaration z
            = Bd.rename ((ρ ⇑ʳ (C.single α ⋈ Δ')) ⇑ʳ β)
                ((dTel.cons bind boundary rest).declaration z)) ?head ?tail z
      case head =>
        refine Eq.trans (declaration_head _ _ _) ?_
        refine Eq.trans ?_ (congrArg (Bd.rename ((ρ ⇑ʳ (C.single α ⋈ Δ')) ⇑ʳ α))
          (declaration_head bind boundary rest)).symm
        refine Eq.trans (Bd.rename_comp _ _ _).symm ?_
        refine Eq.trans ?_ (Bd.rename_comp _ _ _)
        exact congrArg (fun s => Bd.rename s boundary)
          (((Renaming.extend_comp _ _ α).symm.trans
            (congrArg (fun s => s ⇑ʳ α) (Renaming.inl_comp ρ))).trans
              (Renaming.extend_comp _ _ α))
      case tail =>
        intro γ w
        refine Eq.trans (declaration_tail _ _ _ _) ?_
        refine Eq.trans (declaration_rename (ρ ⇑ʳ C.single α) rest w) ?_
        refine Eq.trans ?_ (congrArg (Bd.rename ((ρ ⇑ʳ (C.single α ⋈ Δ')) ⇑ʳ γ))
          (declaration_tail bind boundary rest w)).symm
        exact congrArg (fun s => Bd.rename s (rest.declaration w))
          (congrArg (fun s => s ⇑ʳ γ) (Renaming.extend_assoc ρ (C.single α) Δ').symm)

/-- The entries a slot binds, after reindexing the base. -/
theorem binding_rename {Ω Ω' : C.Arity} (ρ : Ω →ʳ Ω') :
    ∀ {Δ : C.Arity} (T : dTel Ω Δ) {β : C.Arity} (z : Δ ∋ β),
      (rename ρ T).binding z = rename (ρ ⇑ʳ Δ) (T.binding z)
  | _, .nil, _, z => (C.unit_is_empty z).elim
  | _, .cons (α := α) (Δ := Δ') bind boundary rest, β, z => by
      refine slotCases (α := α) (Δ := Δ')
        (motive := fun ⦃β⦄ z =>
          (rename ρ (.cons bind boundary rest)).binding z
            = rename (ρ ⇑ʳ (C.single α ⋈ Δ'))
                ((dTel.cons bind boundary rest).binding z)) ?head ?tail z
      case head =>
        refine Eq.trans (binding_head _ _ _) ?_
        refine Eq.trans ?_ (congrArg (rename (ρ ⇑ʳ (C.single α ⋈ Δ')))
          (binding_head bind boundary rest)).symm
        refine Eq.trans (rename_comp _ _ _).symm ?_
        refine Eq.trans ?_ (rename_comp _ _ _)
        exact congrArg (fun s => rename s bind) (Renaming.inl_comp ρ)
      case tail =>
        intro γ w
        refine Eq.trans (binding_tail _ _ _ _) ?_
        refine Eq.trans (binding_rename (ρ ⇑ʳ C.single α) rest w) ?_
        refine Eq.trans ?_ (congrArg (rename (ρ ⇑ʳ (C.single α ⋈ Δ')))
          (binding_tail bind boundary rest w)).symm
        exact congrArg (fun s => rename s (rest.binding w))
          (Renaming.extend_assoc ρ (C.single α) Δ').symm

/-- The declaration of a slot, after a block is inserted before the suffix. -/
theorem declaration_weaken {Δ Ω Φ : C.Arity} (Ξ : dTel 1 Δ) (Θ : dTel Δ Ω)
    (Ψ : dTel Δ Φ) {α : C.Arity} (x : (Δ ⋈ Φ) ∋ α) :
    (concatenate (concatenate Ξ Θ) (rename (Renaming.inl Δ Ω) Ψ)).declaration
        ((Renaming.inl Δ Ω ⇑ʳ Φ) x)
      = Bd.rename ((Renaming.inl Δ Ω ⇑ʳ Φ) ⇑ʳ α) ((concatenate Ξ Ψ).declaration x) := by
  rcases C.cover Δ Φ x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · refine Eq.trans (congrArg (fun w => (concatenate (concatenate Ξ Θ)
      (rename (Renaming.inl Δ Ω) Ψ)).declaration w)
        (Renaming.extend_inl (Renaming.inl Δ Ω) y)) ?_
    refine Eq.trans (declaration_concatenate_inl _ _ _) ?_
    refine Eq.trans (congrArg (Bd.rename (Renaming.inl (Δ ⋈ Ω) Φ ⇑ʳ α))
      (declaration_concatenate_inl Ξ Θ y)) ?_
    refine Eq.trans (Bd.rename_comp _ _ _).symm ?_
    refine Eq.trans ?_ (congrArg (Bd.rename ((Renaming.inl Δ Ω ⇑ʳ Φ) ⇑ʳ α))
      (declaration_concatenate_inl Ξ Ψ y)).symm
    refine Eq.trans ?_ (Bd.rename_comp _ _ _)
    exact congrArg (fun ρ => Bd.rename ρ (Ξ.declaration y))
      (((Renaming.extend_comp _ _ α).symm.trans
        (congrArg (fun s => s ⇑ʳ α) (Renaming.inl_inl_extend Δ Ω Φ))).trans
          (Renaming.extend_comp _ _ α))
  · refine Eq.trans (congrArg (fun w => (concatenate (concatenate Ξ Θ)
      (rename (Renaming.inl Δ Ω) Ψ)).declaration w)
        (Renaming.extend_inr (Renaming.inl Δ Ω) z)) ?_
    refine Eq.trans (declaration_concatenate_inr _ _ _) ?_
    refine Eq.trans (declaration_rename _ _ _) ?_
    exact congrArg (Bd.rename ((Renaming.inl Δ Ω ⇑ʳ Φ) ⇑ʳ α))
      (declaration_concatenate_inr Ξ Ψ z).symm

/-- The entries a slot binds, after a block is inserted before the suffix. -/
theorem binding_weaken {Δ Ω Φ : C.Arity} (Ξ : dTel 1 Δ) (Θ : dTel Δ Ω)
    (Ψ : dTel Δ Φ) {α : C.Arity} (x : (Δ ⋈ Φ) ∋ α) :
    (concatenate (concatenate Ξ Θ) (rename (Renaming.inl Δ Ω) Ψ)).binding
        ((Renaming.inl Δ Ω ⇑ʳ Φ) x)
      = rename (Renaming.inl Δ Ω ⇑ʳ Φ) ((concatenate Ξ Ψ).binding x) := by
  rcases C.cover Δ Φ x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · refine Eq.trans (congrArg (fun w => (concatenate (concatenate Ξ Θ)
      (rename (Renaming.inl Δ Ω) Ψ)).binding w)
        (Renaming.extend_inl (Renaming.inl Δ Ω) y)) ?_
    refine Eq.trans (binding_concatenate_inl _ _ _) ?_
    refine Eq.trans (congrArg (rename (Renaming.inl (Δ ⋈ Ω) Φ))
      (binding_concatenate_inl Ξ Θ y)) ?_
    refine Eq.trans (rename_comp _ _ _).symm ?_
    refine Eq.trans ?_ (congrArg (rename (Renaming.inl Δ Ω ⇑ʳ Φ))
      (binding_concatenate_inl Ξ Ψ y)).symm
    refine Eq.trans ?_ (rename_comp _ _ _)
    exact congrArg (fun ρ => rename ρ (Ξ.binding y)) (Renaming.inl_inl_extend Δ Ω Φ)
  · refine Eq.trans (congrArg (fun w => (concatenate (concatenate Ξ Θ)
      (rename (Renaming.inl Δ Ω) Ψ)).binding w)
        (Renaming.extend_inr (Renaming.inl Δ Ω) z)) ?_
    refine Eq.trans (binding_concatenate_inr _ _ _) ?_
    refine Eq.trans (binding_rename _ _ _) ?_
    exact congrArg (rename (Renaming.inl Δ Ω ⇑ʳ Φ)) (binding_concatenate_inr Ξ Ψ z).symm

/-- A square of substitutions and renamings, on telescopes. -/
theorem actBase_square {Γ Γ' Δ Δ' : C.Arity} (ρ : Γ →ʳ Γ') (ρ' : Δ →ʳ Δ')
    (κ : Subst Γ' Δ') (κ' : Subst Γ Δ)
    (h : ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α), κ (ρ x) = ⟦ ρ' ⇑ʳ α ⟧ʳ (κ' x)) :
    ∀ {Ψ : C.Arity} (T : dTel Γ Ψ), actBase κ (rename ρ T) = rename ρ' (actBase κ' T)
  | _, .nil => rfl
  | _, .cons (α := α) bind boundary rest => by
      simp only [rename, actBase]
      congr 1
      · exact actBase_square ρ ρ' κ κ' h bind
      · exact Bd.act_square ρ ρ' κ κ' h α boundary
      · exact actBase_square (ρ ⇑ʳ C.single α) (ρ' ⇑ʳ C.single α)
          (Subst.lift κ (C.single α)) (Subst.lift κ' (C.single α))
          (lift_square ρ ρ' κ κ' h (C.single α)) rest

/-- Filling a telescope commutes with a renaming of the base. -/
theorem instantiate_rename {Γ Γ' Ω Ψ : C.Arity} (ρ : Γ →ʳ Γ') (σ : Subst Ω Γ)
    (T : dTel (Γ ⋈ Ω) Ψ) :
    instantiate (fun ⦃Λ⦄ i => ⟦ ρ ⇑ʳ Λ ⟧ʳ (σ i)) (rename (ρ ⇑ʳ Ω) T)
      = rename ρ (instantiate σ T) := by
  refine actBase_square (ρ ⇑ʳ Ω) ρ _ _ ?_ T
  intro α x
  rcases C.cover Γ Ω x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · refine Eq.trans (congrArg (fun (w : (Γ' ⋈ Ω) ∋ α) => Subst.copair (Subst.id Γ')
      (fun ⦃Λ⦄ i => ⟦ ρ ⇑ʳ Λ ⟧ʳ (σ i)) w) (Renaming.extend_inl (Ξ := Ω) ρ y)) ?_
    refine Eq.trans (Subst.copair_inl _ _ (ρ y)) ?_
    exact ((congrArg (Renaming.act (ρ ⇑ʳ α)) (Subst.copair_inl (Subst.id Γ) σ y)).trans
      (Renaming.act_eta ρ y)).symm
  · refine Eq.trans (congrArg (fun (w : (Γ' ⋈ Ω) ∋ α) => Subst.copair (Subst.id Γ')
      (fun ⦃Λ⦄ i => ⟦ ρ ⇑ʳ Λ ⟧ʳ (σ i)) w) (Renaming.extend_inr (Γ := Γ) ρ z)) ?_
    refine Eq.trans (Subst.copair_inr _ _ z) ?_
    exact congrArg (Renaming.act (ρ ⇑ʳ α)) (Subst.copair_inr (Subst.id Γ) σ z).symm

/-- The filled declaration of a slot, after a renaming of the base. -/
theorem act_declaration_rename {Γ Γ' Ω Λ : C.Arity} (ρ : Γ →ʳ Γ') (σ : Subst Ω Γ)
    (Θ : dTel Γ Ω) (z : Ω ∋ Λ) :
    Bd.act (Ξ := 1) (fun ⦃Λ'⦄ i => ⟦ ρ ⇑ʳ Λ' ⟧ʳ (σ i)) Λ ((rename ρ Θ).declaration z)
      = Bd.rename (ρ ⇑ʳ Λ) (Bd.act (Ξ := 1) σ Λ (Θ.declaration z)) := by
  refine Eq.trans (congrArg (Bd.act (Ξ := 1) (fun ⦃Λ'⦄ i => ⟦ ρ ⇑ʳ Λ' ⟧ʳ (σ i)) Λ)
    (declaration_rename ρ Θ z)) ?_
  exact Bd.act_rename ρ σ (Θ.declaration z)

/-- The filled binding telescope of a slot, after a renaming of the base. -/
theorem instantiate_binding_rename {Γ Γ' Ω Λ : C.Arity} (ρ : Γ →ʳ Γ') (σ : Subst Ω Γ)
    (Θ : dTel Γ Ω) (z : Ω ∋ Λ) :
    instantiate (fun ⦃Λ'⦄ i => ⟦ ρ ⇑ʳ Λ' ⟧ʳ (σ i)) ((rename ρ Θ).binding z)
      = rename ρ (instantiate σ (Θ.binding z)) := by
  refine Eq.trans (congrArg (instantiate (fun ⦃Λ'⦄ i => ⟦ ρ ⇑ʳ Λ' ⟧ʳ (σ i)))
    (binding_rename ρ Θ z)) ?_
  exact instantiate_rename ρ σ (Θ.binding z)

/-- Concatenation is associative. -/
theorem concatenate_assoc {Ω Δ Ξ Φ : C.Arity} :
    ∀ (Θ : dTel Ω Δ) (Ψ : dTel (Ω ⋈ Δ) Ξ) (Χ : dTel ((Ω ⋈ Δ) ⋈ Ξ) Φ),
      concatenate (concatenate Θ Ψ) Χ = concatenate Θ (concatenate Ψ Χ)
  | .nil, _, _ => rfl
  | .cons bind boundary rest, Ψ, Χ =>
      congrArg (dTel.cons bind boundary) (concatenate_assoc rest Ψ Χ)

/-- The boundary of an expression over an ambient. -/
def boundaryOf {Δ : C.Arity} (Ξ : dTel 1 Δ) : Expr Δ → Bd Δ
  | .ap x args => Bd.instantiate args (Ξ.declaration x)

@[simp] theorem boundaryOf_ap {Δ α : C.Arity} (Ξ : dTel 1 Δ) (x : Δ ∋ α)
    (args : Subst α Δ) :
    Ξ.boundaryOf (.ap x args) = Bd.instantiate args (Ξ.declaration x) := rfl

/-- 8(1): weakening an expression weakens its boundary, on the nose. -/
theorem boundaryOf_weaken {Δ Ω : C.Arity} (Ξ : dTel 1 Δ) (Θ : dTel Δ Ω) :
    ∀ e : Expr Δ,
      (concatenate Ξ Θ).boundaryOf (⟦ Renaming.inl Δ Ω ⟧ʳ e)
        = Bd.rename (Renaming.inl Δ Ω) (Ξ.boundaryOf e)
  | .ap (α := α) x args => by
      refine Eq.trans (boundaryOf_ap _ _ _) ?_
      refine Eq.trans (congrArg (Bd.instantiate _)
        (declaration_concatenate_inl Ξ Θ x)) ?_
      exact Bd.instantiate_weaken Δ Ω α args (Ξ.declaration x)

/-- The boundary computed for a fully applied slot is the slot's declaration. -/
theorem boundaryOf_eta {Δ α : C.Arity} (Ξ : dTel 1 Δ) (x : Δ ∋ α) :
    (concatenate Ξ (Ξ.binding x)).boundaryOf (Expr.η x) = Ξ.declaration x := by
  rw [Expr.η.eq_1]
  refine Eq.trans (boundaryOf_ap _ _ _) ?_
  refine Eq.trans (congrArg (Bd.instantiate _)
    (declaration_concatenate_inl Ξ (Ξ.binding x) x)) ?_
  exact Bd.instantiate_rename_inl Δ α (Ξ.declaration x)

end dTel

/-- An ambient is a telescope over the unit base. -/
abbrev Ambient (Δ : C.Arity) : Type := dTel 1 Δ

/-- Extend an ambient by a telescope over it. -/
abbrev Ambient.extend {Δ : C.Arity} (Ξ : Ambient Δ) {Ω : C.Arity}
    (Θ : dTel Δ Ω) : Ambient (Δ ⋈ Ω) :=
  dTel.concatenate Ξ Θ

