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

/-- The declaration of a slot, after a substitution in the base. -/
theorem declaration_actBase {Ω Ω' : C.Arity} (κ : Subst Ω Ω') :
    ∀ {Δ : C.Arity} (T : dTel Ω Δ) {β : C.Arity} (z : Δ ∋ β),
      (actBase κ T).declaration z
        = Bd.act (Γ := 1) (Ξ := Ω' ⋈ Δ) (Subst.lift κ Δ) β (T.declaration z)
  | _, .nil, _, z => (C.unit_is_empty z).elim
  | _, .cons (α := α) (Δ := Δ') bind boundary rest, β, z => by
      refine slotCases (α := α) (Δ := Δ')
        (motive := fun ⦃β⦄ z =>
          (actBase κ (.cons bind boundary rest)).declaration z
            = Bd.act (Γ := 1) (Ξ := Ω' ⋈ (C.single α ⋈ Δ'))
                (Subst.lift κ (C.single α ⋈ Δ')) β
                ((dTel.cons bind boundary rest).declaration z)) ?head ?tail z
      case head =>
        refine Eq.trans (declaration_head _ _ _) ?_
        refine Eq.trans ?_ (congrArg
          (Bd.act (Γ := 1) (Ξ := Ω' ⋈ (C.single α ⋈ Δ'))
            (Subst.lift κ (C.single α ⋈ Δ')) α)
          (declaration_head bind boundary rest)).symm
        exact (Bd.act_square (Renaming.inl Ω (C.single α ⋈ Δ'))
          (Renaming.inl Ω' (C.single α ⋈ Δ')) (Subst.lift κ (C.single α ⋈ Δ')) κ
          (fun ⦃_⦄ x => Subst.lift_inl κ x) α boundary).symm
      case tail =>
        intro γ w
        refine Eq.trans (declaration_tail _ _ _ _) ?_
        refine Eq.trans (declaration_actBase (Subst.lift κ (C.single α)) rest w) ?_
        refine Eq.trans ?_ (congrArg
          (Bd.act (Γ := 1) (Ξ := Ω' ⋈ (C.single α ⋈ Δ'))
            (Subst.lift κ (C.single α ⋈ Δ')) γ)
          (declaration_tail bind boundary rest w)).symm
        exact congrArg (fun s => Bd.act (Γ := 1) (Ξ := Ω' ⋈ (C.single α ⋈ Δ'))
            s γ (rest.declaration w))
          (Subst.lift_assoc κ (C.single α) Δ').symm

/-- The entries a slot binds, after a substitution in the base. -/
theorem binding_actBase {Ω Ω' : C.Arity} (κ : Subst Ω Ω') :
    ∀ {Δ : C.Arity} (T : dTel Ω Δ) {β : C.Arity} (z : Δ ∋ β),
      (actBase κ T).binding z = actBase (Subst.lift κ Δ) (T.binding z)
  | _, .nil, _, z => (C.unit_is_empty z).elim
  | _, .cons (α := α) (Δ := Δ') bind boundary rest, β, z => by
      refine slotCases (α := α) (Δ := Δ')
        (motive := fun ⦃β⦄ z =>
          (actBase κ (.cons bind boundary rest)).binding z
            = actBase (Subst.lift κ (C.single α ⋈ Δ'))
                ((dTel.cons bind boundary rest).binding z)) ?head ?tail z
      case head =>
        refine Eq.trans (binding_head _ _ _) ?_
        refine Eq.trans ?_ (congrArg (actBase (Subst.lift κ (C.single α ⋈ Δ')))
          (binding_head bind boundary rest)).symm
        exact (actBase_square (Renaming.inl Ω (C.single α ⋈ Δ'))
          (Renaming.inl Ω' (C.single α ⋈ Δ')) (Subst.lift κ (C.single α ⋈ Δ')) κ
          (fun ⦃_⦄ x => Subst.lift_inl κ x) bind).symm
      case tail =>
        intro γ w
        refine Eq.trans (binding_tail _ _ _ _) ?_
        refine Eq.trans (binding_actBase (Subst.lift κ (C.single α)) rest w) ?_
        refine Eq.trans ?_ (congrArg (actBase (Subst.lift κ (C.single α ⋈ Δ')))
          (binding_tail bind boundary rest w)).symm
        exact congrArg (fun s => actBase s (rest.binding w))
          (Subst.lift_assoc κ (C.single α) Δ').symm

/-- The identity substitution acts trivially. -/
theorem actBase_id : ∀ {Γ Ψ : C.Arity} (T : dTel Γ Ψ), actBase (Subst.id Γ) T = T
  | _, _, .nil => rfl
  | _, _, .cons (α := α) bind boundary rest => by
      simp only [actBase]
      congr 1
      · exact actBase_id bind
      · exact Bd.act_id _ α boundary
      · refine Eq.trans (congrArg (fun s => actBase s rest) (Subst.lift_id _ (C.single α))) ?_
        exact actBase_id rest

/-- Acting by a composite is successive action. -/
theorem actBase_comp {Γ Δ Ξ : C.Arity} (κ : Subst Γ Δ) (θ : Subst Δ Ξ) :
    ∀ {Ψ : C.Arity} (T : dTel Γ Ψ),
      actBase (Subst.comp (Γ := 1) κ θ) T = actBase θ (actBase κ T)
  | _, .nil => rfl
  | _, .cons (α := α) bind boundary rest => by
      simp only [actBase]
      congr 1
      · exact actBase_comp κ θ bind
      · exact Bd.act_comp (Γ := 1) κ θ α boundary
      · refine Eq.trans (congrArg (fun s => actBase s rest)
          (Subst.lift_comp κ θ (C.single α))) ?_
        exact actBase_comp _ _ rest

/-- Reindexing the base distributes over concatenation. -/
theorem rename_concatenate {Γ Γ' Φ Ψ : C.Arity} (ρ : Γ →ʳ Γ') :
    ∀ (T : dTel Γ Φ) (U : dTel (Γ ⋈ Φ) Ψ),
      rename ρ (concatenate T U)
        = concatenate (rename ρ T) (rename (ρ ⇑ʳ Φ) U)
  | .nil, U => (congrArg (fun s => rename s U) (Renaming.extend_unit ρ)).symm
  | .cons (α := α) (Δ := Δ') bind boundary rest, U => by
      simp only [concatenate, rename]
      congr 1
      refine Eq.trans (rename_concatenate (ρ ⇑ʳ C.single α) rest U) ?_
      exact congrArg (fun s => concatenate (rename (ρ ⇑ʳ C.single α) rest)
          (rename s U))
        (Renaming.extend_assoc ρ (C.single α) Δ').symm

/-- Acting by the eta-substitution of a renaming is renaming, on a telescope. -/
theorem actBase_ofRenaming {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) :
    ∀ {Ψ : C.Arity} (T : dTel Γ Ψ),
      dTel.actBase (Subst.ofRenaming ρ) T = dTel.rename ρ T
  | _, .nil => rfl
  | _, .cons (α := α) bind boundary rest => by
      simp only [dTel.actBase, dTel.rename]
      congr 1
      · exact actBase_ofRenaming ρ bind
      · exact Bd.act_ofRenaming ρ boundary
      · refine Eq.trans (congrArg (fun s => dTel.actBase s rest)
          (Subst.lift_ofRenaming ρ (C.single α))) ?_
        exact actBase_ofRenaming (ρ ⇑ʳ C.single α) rest

/-- A substitution in the base distributes over concatenation. -/
theorem actBase_concatenate {Γ Γ' Φ Ψ : C.Arity} (κ : Subst Γ Γ') :
    ∀ (T : dTel Γ Φ) (U : dTel (Γ ⋈ Φ) Ψ),
      actBase κ (concatenate T U)
        = concatenate (actBase κ T) (actBase (Subst.lift κ Φ) U)
  | .nil, U => (congrArg (fun s => actBase s U) (Subst.lift_one κ)).symm
  | .cons (α := α) (Δ := Δ') bind boundary rest, U => by
      simp only [concatenate, actBase]
      congr 1
      refine Eq.trans (actBase_concatenate (Subst.lift κ (C.single α)) rest U) ?_
      exact congrArg (fun s => concatenate (actBase (Subst.lift κ (C.single α)) rest)
          (actBase s U))
        (Subst.lift_assoc κ (C.single α) Δ').symm

/-- Filling commutes with a substitution in the base. -/
theorem actBase_instantiate {Γ Γ' Ω Ψ : C.Arity} (κ : Subst Γ Γ') (τ : Subst Ω Γ)
    (T : dTel (Γ ⋈ Ω) Ψ) :
    actBase κ (instantiate τ T)
      = instantiate (fun ⦃Λ⦄ i => Subst.act (Γ := 1) κ Λ (τ i))
          (actBase (Subst.lift κ Ω) T) := by
  refine Eq.trans (actBase_comp (Subst.copair (Subst.id Γ) τ) κ T).symm ?_
  refine Eq.trans (congrArg (fun s => actBase s T) ?_)
    (actBase_comp (Subst.lift κ Ω)
      (Subst.copair (Subst.id Γ') (fun ⦃Λ⦄ i => Subst.act (Γ := 1) κ Λ (τ i))) T)
  funext β x
  rcases C.cover Γ Ω x with ⟨w, rfl⟩ | ⟨i, rfl⟩
  · refine Eq.trans (congrArg (Subst.act (Γ := 1) κ β)
      (Subst.copair_inl (Subst.id Γ) τ w)) ?_
    refine Eq.trans (act_η κ β w) ?_
    refine Eq.trans ?_ (congrArg (Subst.act (Γ := 1) (Subst.copair (Subst.id Γ')
      (fun ⦃Λ⦄ i => Subst.act (Γ := 1) κ Λ (τ i))) β) (Subst.lift_inl κ w)).symm
    refine Eq.symm (Eq.trans (act_rename_cancel (Renaming.inl Γ' Ω) (𝟙ʳ Γ')
      (Subst.copair (Subst.id Γ') (fun ⦃Λ⦄ i => Subst.act (Γ := 1) κ Λ (τ i)))
      (fun ⦃_⦄ u => Subst.copair_inl _ _ u) β (κ w))
      (Eq.trans (congrArg (fun ρ => Renaming.act ρ (κ w)) (Renaming.extend_id Γ' β))
        (Renaming.act_id _)))
  · refine Eq.trans (congrArg (Subst.act (Γ := 1) κ β)
      (Subst.copair_inr (Subst.id Γ) τ i)) ?_
    refine Eq.trans ?_ (congrArg (Subst.act (Γ := 1) (Subst.copair (Subst.id Γ')
      (fun ⦃Λ⦄ i => Subst.act (Γ := 1) κ Λ (τ i))) β) (Subst.lift_inr κ i)).symm
    refine Eq.trans ?_ (act_η _ β (C.inr i)).symm
    exact (Subst.copair_inr (Subst.id Γ')
      (fun ⦃Λ⦄ j => Subst.act (Γ := 1) κ Λ (τ j)) i).symm

/-- The identity renaming acts trivially. -/
theorem rename_id : ∀ {Γ Ψ : C.Arity} (T : dTel Γ Ψ), rename (𝟙ʳ Γ) T = T
  | _, _, .nil => rfl
  | _, _, .cons (α := α) bind boundary rest => by
      simp only [rename]
      congr 1
      · exact rename_id bind
      · exact (congrArg (fun s => Bd.rename s boundary) (Renaming.extend_id _ _)).trans
          (Bd.rename_id boundary)
      · refine Eq.trans (congrArg (fun s => rename s rest)
          (Renaming.extend_id _ _)) ?_
        exact rename_id rest

/-- Filling the fresh block of a weakened telescope by its own slots returns it. -/
theorem instantiate_rename_inl {Δ Ω Ψ : C.Arity} (T : dTel (Δ ⋈ Ω) Ψ) :
    instantiate (Subst.instId Δ Ω) (rename (Renaming.inl Δ Ω ⇑ʳ Ω) T) = T := by
  refine Eq.trans (actBase_square (Renaming.inl Δ Ω ⇑ʳ Ω) (𝟙ʳ (Δ ⋈ Ω))
    (Subst.copair (Subst.id (Δ ⋈ Ω)) (Subst.instId Δ Ω)) (Subst.id (Δ ⋈ Ω)) ?_ T) ?_
  · intro γ x
    refine Eq.trans ?_ ((congrArg (fun s => Renaming.act s (Subst.id (Δ ⋈ Ω) x))
      (Renaming.extend_id _ _)).trans (Renaming.act_id _)).symm
    rcases C.cover Δ Ω x with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · refine Eq.trans (congrArg (fun (w : ((Δ ⋈ Ω) ⋈ Ω) ∋ γ) =>
        Subst.copair (Subst.id (Δ ⋈ Ω)) (Subst.instId Δ Ω) w)
        (Renaming.extend_inl (Ξ := Ω) (Renaming.inl Δ Ω) y)) ?_
      exact Subst.copair_inl _ _ (C.inl y)
    · refine Eq.trans (congrArg (fun (w : ((Δ ⋈ Ω) ⋈ Ω) ∋ γ) =>
        Subst.copair (Subst.id (Δ ⋈ Ω)) (Subst.instId Δ Ω) w)
        (Renaming.extend_inr (Renaming.inl Δ Ω) z)) ?_
      exact Subst.copair_inr _ _ z
  · exact (congrArg (rename (𝟙ʳ (Δ ⋈ Ω))) (actBase_id T)).trans (rename_id T)

/-- The declaration of a slot of a weakened telescope, filled by its own slots. -/
theorem act_declaration_instId {Δ Ω Λ : C.Arity} (Θ : dTel Δ Ω) (z : Ω ∋ Λ) :
    Bd.act (Ξ := 1) (Subst.instId Δ Ω) Λ
        ((rename (Renaming.inl Δ Ω) Θ).declaration z) = Θ.declaration z := by
  refine Eq.trans (congrArg (Bd.act (Ξ := 1) (Subst.instId Δ Ω) Λ)
    (declaration_rename (Renaming.inl Δ Ω) Θ z)) ?_
  exact Bd.act_instId_weaken Δ Ω Λ (Θ.declaration z)

/-- The entries bound by a slot of a weakened telescope, filled by its own slots. -/
theorem instantiate_binding_instId {Δ Ω Λ : C.Arity} (Θ : dTel Δ Ω) (z : Ω ∋ Λ) :
    instantiate (Subst.instId Δ Ω) ((rename (Renaming.inl Δ Ω) Θ).binding z)
      = Θ.binding z := by
  refine Eq.trans (congrArg (instantiate (Subst.instId Δ Ω))
    (binding_rename (Renaming.inl Δ Ω) Θ z)) ?_
  exact instantiate_rename_inl (Θ.binding z)

/-- Substituting into a renamed telescope whose slots the substitution merely
relabels is that relabelling. -/
theorem actBase_rename_cancel {Γ Δ' Γ' : C.Arity} (ρ : Γ →ʳ Δ') (ρ' : Γ →ʳ Γ')
    (κ : Subst Δ' Γ') (h : ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α), κ (ρ x) = Expr.η (ρ' x)) :
    ∀ {Ψ : C.Arity} (T : dTel Γ Ψ), actBase κ (rename ρ T) = rename ρ' T := by
  intro Ψ T
  refine Eq.trans (actBase_square ρ ρ' κ (Subst.id Γ) ?_ T) ?_
  · intro α x
    exact (h x).trans (Renaming.act_eta ρ' x).symm
  · exact congrArg (rename ρ') (actBase_id T)

/-- Instantiating the weakening of a telescope into the prefix is reindexing. -/
theorem instantiate_weaken {Γ Γ' Χ : C.Arity} (s : Subst Γ Γ') (T : dTel Γ Χ) :
    dTel.instantiate s (dTel.rename (Renaming.inr Γ' Γ) T) = dTel.actBase s T := by
  refine Eq.trans (actBase_square (Renaming.inr Γ' Γ) (𝟙ʳ Γ')
    (Subst.copair (Subst.id Γ') s) s ?_ T) ?_
  · intro α x
    refine (Subst.copair_inr _ _ x).trans ?_
    exact ((congrArg (fun ρ => Renaming.act ρ (s x)) (Renaming.extend_id Γ' α)).trans
      (Renaming.act_id _)).symm
  · exact rename_id _

/-- Concatenating the empty telescope changes nothing. -/
theorem concatenate_nil {Ω : C.Arity} :
    ∀ {Δ : C.Arity} (Θ : dTel Ω Δ), concatenate Θ .nil = Θ
  | _, .nil => rfl
  | _, .cons bind boundary rest =>
      congrArg (dTel.cons bind boundary) (concatenate_nil rest)

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

@[inherit_doc dTel.concatenate] infixl:65 " ⋈ " => dTel.concatenate

/-- Fill the block `Ω` of an expression over `Δ ⋈ Ω ⋈ Φ`. -/
abbrev Subst.fill {Δ Ω Φ : C.Arity} (σ : Subst Ω Δ) (g : Expr ((Δ ⋈ Ω) ⋈ Φ)) :
    Expr (Δ ⋈ Φ) :=
  Subst.act (Γ := Δ) (Δ := Ω) (Ξ := 1) σ Φ g

/-- Fill the block `Ω` of a boundary over `Δ ⋈ Ω ⋈ Φ`. -/
abbrev Bd.fill {Δ Ω Φ : C.Arity} (σ : Subst Ω Δ) (β : Bd ((Δ ⋈ Ω) ⋈ Φ)) :
    Bd (Δ ⋈ Φ) :=
  Bd.act (Γ := Δ) (Δ := Ω) (Ξ := 1) σ Φ β

/-- Fill the block `Ω` of an expression over `Δ ⋈ Ω`. -/
abbrev Subst.instantiate {Δ Ω : C.Arity} (σ : Subst Ω Δ) (g : Expr (Δ ⋈ Ω)) : Expr Δ :=
  Subst.act (Γ := Δ) (Δ := Ω) (Ξ := 1) σ 1 g

/-- Apply a substitution of one base by another to an expression. -/
abbrev Subst.apply {Γ Γ' : C.Arity} (s : Subst Γ Γ') (g : Expr Γ) : Expr Γ' :=
  Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') s 1 g

/-- Apply a substitution of one base by another to a boundary. -/
abbrev Bd.apply {Γ Γ' : C.Arity} (s : Subst Γ Γ') (β : Bd Γ) : Bd Γ' :=
  Bd.act (Γ := 1) (Δ := Γ) (Ξ := Γ') s 1 β

/-- Fill the block `Ω` of a telescope over `Δ ⋈ Ω ⋈ Φ`. -/
abbrev dTel.fill {Δ Ω Φ Χ : C.Arity} (σ : Subst Ω Δ) (X : dTel ((Δ ⋈ Ω) ⋈ Φ) Χ) :
    dTel (Δ ⋈ Φ) Χ :=
  dTel.actBase (Subst.lift (Subst.copair (Subst.id Δ) σ) Φ) X

/-- Fill the block `Ω` in every filler of a substitution into `Δ ⋈ Ω ⋈ Φ`. -/
abbrev Subst.fillEach {Δ Ω Φ Χ : C.Arity} (σ : Subst Ω Δ)
    (τ : Subst Χ ((Δ ⋈ Ω) ⋈ Φ)) : Subst Χ (Δ ⋈ Φ) :=
  fun ⦃Λ⦄ i => Subst.act (Γ := Δ) (Δ := Ω) (Ξ := 1) σ (Φ ⋈ Λ) (τ i)

/-- Apply a substitution of one base by another in every filler of a
substitution. -/
abbrev Subst.applyEach {Γ Γ' Χ : C.Arity} (s : Subst Γ Γ') (τ : Subst Χ Γ) :
    Subst Χ Γ' :=
  fun ⦃Λ⦄ i => Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') s Λ (τ i)

/-- Applying a substitution in every filler distributes over pairing. -/
theorem Subst.applyEach_copair {Γ Δ Ω Ω' : C.Arity} (s : Subst Ω Ω')
    (σ : Subst Γ Ω) (τ : Subst Δ Ω) :
    Subst.applyEach s (Subst.copair σ τ)
      = Subst.copair (Subst.applyEach s σ) (Subst.applyEach s τ) := by
  funext α x
  rcases C.cover Γ Δ x with ⟨u, rfl⟩ | ⟨v, rfl⟩
  · refine Eq.trans (congrArg (fun e => Subst.act (Γ := 1) s α e)
      (Subst.copair_inl σ τ u)) ?_
    exact (Subst.copair_inl (Subst.applyEach s σ) (Subst.applyEach s τ) u).symm
  · refine Eq.trans (congrArg (fun e => Subst.act (Γ := 1) s α e)
      (Subst.copair_inr σ τ v)) ?_
    exact (Subst.copair_inr (Subst.applyEach s σ) (Subst.applyEach s τ) v).symm

/-- Apply a substitution of one base by another to a boundary at depth `Φ`. -/
abbrev Bd.applyAt {Γ Γ' : C.Arity} (s : Subst Γ Γ') (Φ : C.Arity) (β : Bd (Γ ⋈ Φ)) :
    Bd (Γ' ⋈ Φ) :=
  Bd.act (Γ := 1) (Δ := Γ) (Ξ := Γ') s Φ β

@[inherit_doc Subst.apply] infixr:70 " ⋆ " => Subst.apply
@[inherit_doc dTel.fill] infixr:70 " ⋆ " => dTel.fill
@[inherit_doc Subst.fillEach] infixr:70 " ⋆ " => Subst.fillEach
@[inherit_doc Subst.applyEach] infixr:70 " ⋆ " => Subst.applyEach
@[inherit_doc Bd.apply] infixr:70 " ⋆ " => Bd.apply
@[inherit_doc dTel.actBase] infixr:70 " ⋆ " => dTel.actBase
@[inherit_doc Subst.fill] infixr:70 " ⋆ " => Subst.fill
@[inherit_doc Subst.instantiate] infixr:70 " ⋆ " => Subst.instantiate
@[inherit_doc Bd.instantiate] infixr:70 " ⋆ " => Bd.instantiate
@[inherit_doc Bd.fill] infixr:70 " ⋆ " => Bd.fill
@[inherit_doc dTel.instantiate] infixr:70 " ⋆ " => dTel.instantiate

/-- Filling the weakening of an expression into the prefix is applying. -/
theorem Subst.act_weaken {Γ Γ' Φ : C.Arity} (s : Subst Γ Γ') (e : Expr (Γ ⋈ Φ)) :
    Subst.act (Γ := Γ') (Δ := Γ) (Ξ := 1) s Φ
        (⟦ Renaming.inr Γ' Γ ⇑ʳ Φ ⟧ʳ e)
      = Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') s Φ e :=
  (act_copair_prefix s Φ (⟦ Renaming.inr Γ' Γ ⇑ʳ Φ ⟧ʳ e)).symm.trans
    (act_copair_inr s Φ e)

/-- Filling the weakening of a boundary into the prefix is applying. -/
theorem Bd.act_weaken {Γ Γ' Φ : C.Arity} (s : Subst Γ Γ') (β : Bd (Γ ⋈ Φ)) :
    Bd.act (Γ := Γ') (Δ := Γ) (Ξ := 1) s Φ (Bd.rename (Renaming.inr Γ' Γ ⇑ʳ Φ) β)
      = Bd.applyAt s Φ β := by
  cases β with
  | sort => rfl
  | of S => exact congrArg Bd.of (Subst.act_weaken s S)
  | eq l r => exact congrArg₂ Bd.eq (Subst.act_weaken s l) (Subst.act_weaken s r)

/-- Instantiating the weakening of an expression into the prefix is applying. -/
theorem Subst.instantiate_weaken {Γ Γ' : C.Arity} (s : Subst Γ Γ') (e : Expr Γ) :
    Subst.instantiate s (⟦ Renaming.inr Γ' Γ ⟧ʳ e) = Subst.apply s e := by
  refine Eq.trans (act_copair_prefix s 1 (⟦ Renaming.inr Γ' Γ ⟧ʳ e)).symm ?_
  refine Eq.trans (congrArg (fun ρ =>
    Subst.act (Γ := 1) (Δ := Γ' ⋈ Γ) (Ξ := Γ') (Subst.copair (Subst.id Γ') s) 1
      (Renaming.act ρ e)) (Renaming.extend_unit (Renaming.inr Γ' Γ)).symm) ?_
  exact act_copair_inr s 1 e


/-- Filling a two-block arity is filling the first block and then the second. -/
theorem Subst.copair_split {Δ Ω Φ : C.Arity} (σ : Subst (Ω ⋈ Φ) Δ) :
    (Subst.comp (Γ := 1) (Ξ := Δ) (Subst.lift (Subst.copair (Subst.id Δ)
          (fun ⦃β⦄ (i : Ω ∋ β) => σ (C.inl i))) Φ)
        (Subst.copair (Subst.id Δ) (fun ⦃β⦄ (j : Φ ∋ β) => σ (C.inr j))) :
      Subst (Δ ⋈ Ω ⋈ Φ) Δ)
      = Subst.copair (Subst.id Δ) σ := by
  have hbase : ∀ ⦃γ : C.Arity⦄ (w : Δ ∋ γ),
      Subst.copair (Subst.id Δ) (fun ⦃β⦄ (j : Φ ∋ β) => σ (C.inr j)) (C.inl w)
        = Expr.η w := fun ⦃_⦄ w => Subst.copair_inl _ _ w
  funext β x
  rcases C.cover (Δ ⋈ Ω) Φ x with ⟨u, rfl⟩ | ⟨j, rfl⟩
  · rcases C.cover Δ (Ω) u with ⟨w, rfl⟩ | ⟨i, rfl⟩
    · refine Eq.trans (congrArg (Subst.act (Γ := 1) _ β)
        (Subst.lift_copair_inl_inl _ w)) ?_
      refine Eq.trans (act_η _ β (C.inl w)) ?_
      refine Eq.trans (hbase w) ?_
      refine Eq.trans ?_ (congrArg (fun (z : (Δ ⋈ Ω ⋈ Φ) ∋ β) =>
        Subst.copair (Subst.id Δ) σ z) (C.inl_inl Δ (Ω) Φ w))
      exact (Subst.copair_inl _ _ w).symm
    · refine Eq.trans (congrArg (Subst.act (Γ := 1) _ β)
        (Subst.lift_copair_inl_inr _ i)) ?_
      refine Eq.trans (act_rename_cancel (Renaming.inl Δ Φ) (𝟙ʳ Δ) _ hbase β
        (σ (C.inl i))) ?_
      refine Eq.trans ((congrArg (fun ρ => Renaming.act ρ (σ (C.inl i)))
        (Renaming.extend_id Δ β)).trans (Renaming.act_id _)) ?_
      refine Eq.trans ?_ (congrArg (fun (z : (Δ ⋈ Ω ⋈ Φ) ∋ β) =>
        Subst.copair (Subst.id Δ) σ z) (C.inr_inl Δ (Ω) Φ i))
      exact (Subst.copair_inr _ _ (C.inl i)).symm
  · refine Eq.trans (congrArg (Subst.act (Γ := 1) _ β) (Subst.lift_inr _ j)) ?_
    refine Eq.trans (act_η _ β (C.inr j)) ?_
    refine Eq.trans (Subst.copair_inr _ _ j) ?_
    refine Eq.trans ?_ (congrArg (fun (z : (Δ ⋈ Ω ⋈ Φ) ∋ β) =>
      Subst.copair (Subst.id Δ) σ z) (C.inr_inr Δ (Ω) Φ j))
    exact (Subst.copair_inr _ _ (C.inr j)).symm

/-- Filling a two-block arity agrees with filling the first block, on the slots
weakened into the first block. -/
theorem Subst.copair_weaken {Δ Ω Φ : C.Arity} (κ : Subst (Ω ⋈ Φ) Δ) :
    ∀ ⦃α : C.Arity⦄ (x : (Δ ⋈ Ω) ∋ α),
      Subst.copair (Subst.id Δ) κ (Renaming.inl (Δ ⋈ Ω) Φ x)
        = ⟦ 𝟙ʳ Δ ⇑ʳ α ⟧ʳ (Subst.copair (Subst.id Δ)
            (fun ⦃β⦄ (w : Ω ∋ β) => κ (C.inl w)) x) := by
  intro α x
  have hid : ∀ e : Expr (Δ ⋈ α), (⟦ 𝟙ʳ Δ ⇑ʳ α ⟧ʳ e : Expr (Δ ⋈ α)) = e := by
    intro e
    exact (congrArg (fun ρ => Renaming.act ρ e) (Renaming.extend_id Δ α)).trans
      (Renaming.act_id e)
  refine Eq.trans ?_ (hid _).symm
  rcases C.cover Δ Ω x with ⟨u, rfl⟩ | ⟨v, rfl⟩
  · refine Eq.trans (congrArg (fun w : (Δ ⋈ Ω ⋈ Φ) ∋ α =>
      Subst.copair (Subst.id Δ) κ w) (C.inl_inl Δ Ω Φ u).symm) ?_
    exact (Subst.copair_inl _ _ u).trans (Subst.copair_inl _ _ u).symm
  · refine Eq.trans (congrArg (fun w : (Δ ⋈ Ω ⋈ Φ) ∋ α =>
      Subst.copair (Subst.id Δ) κ w) (C.inr_inl Δ Ω Φ v).symm) ?_
    refine (Subst.copair_inr _ _ (C.inl v)).trans ?_
    exact (Subst.copair_inr (Subst.id Δ)
      (fun ⦃β⦄ (w : Ω ∋ β) => κ (C.inl w)) v).symm

/-- Filling a two-block arity in a boundary weakened into the first block is
filling the first block. -/
theorem Bd.fill_weaken_inl {Δ Ω Φ Λ : C.Arity} (κ : Subst (Ω ⋈ Φ) Δ)
    (β : Bd ((Δ ⋈ Ω) ⋈ Λ)) :
    Bd.fill κ (Bd.rename (Renaming.inl (Δ ⋈ Ω) Φ ⇑ʳ Λ) β)
      = Bd.fill (fun ⦃γ⦄ (w : Ω ∋ γ) => κ (C.inl w)) β := by
  refine Eq.trans (Bd.act_copair_prefix κ Λ _).symm ?_
  refine Eq.trans (Bd.act_square (Renaming.inl (Δ ⋈ Ω) Φ) (𝟙ʳ Δ)
    (Subst.copair (Subst.id Δ) κ : Subst (Δ ⋈ (Ω ⋈ Φ)) Δ)
    (Subst.copair (Subst.id Δ) (fun ⦃γ⦄ (w : Ω ∋ γ) => κ (C.inl w)))
    (Subst.copair_weaken κ) Λ β) ?_
  refine Eq.trans (congrArg (fun ρ => Bd.rename ρ
    (Bd.act (Γ := 1) (Subst.copair (Subst.id Δ)
      (fun ⦃γ⦄ (w : Ω ∋ γ) => κ (C.inl w))) Λ β)) (Renaming.extend_id Δ Λ)) ?_
  refine Eq.trans (Bd.rename_id _) ?_
  exact Bd.act_copair_prefix (fun ⦃γ⦄ (w : Ω ∋ γ) => κ (C.inl w)) Λ β

/-- Filling a two-block arity in a telescope weakened into the first block is
filling the first block. -/
theorem dTel.instantiate_weaken_inl {Δ Ω Φ Λ : C.Arity} (κ : Subst (Ω ⋈ Φ) Δ)
    (T : dTel (Δ ⋈ Ω) Λ) :
    dTel.instantiate κ (dTel.rename (Renaming.inl (Δ ⋈ Ω) Φ) T)
      = dTel.instantiate (fun ⦃γ⦄ (w : Ω ∋ γ) => κ (C.inl w)) T := by
  refine Eq.trans (dTel.actBase_square (Renaming.inl (Δ ⋈ Ω) Φ) (𝟙ʳ Δ)
    (Subst.copair (Subst.id Δ) κ : Subst (Δ ⋈ (Ω ⋈ Φ)) Δ)
    (Subst.copair (Subst.id Δ) (fun ⦃γ⦄ (w : Ω ∋ γ) => κ (C.inl w)))
    (Subst.copair_weaken κ) T) ?_
  exact dTel.rename_id _

/-- The declaration of a slot of the first block of a concatenation, filled. -/
theorem dTel.declaration_left_instantiate {Δ Ω Φ Λ : C.Arity} (Θ : dTel Δ Ω)
    (X : dTel (Δ ⋈ Ω) Φ) (κ : Subst (Ω ⋈ Φ) Δ) (w : Ω ∋ Λ) :
    Bd.fill κ ((dTel.concatenate Θ X).declaration (C.inl w))
      = Bd.fill (fun ⦃γ⦄ (v : Ω ∋ γ) => κ (C.inl v)) (Θ.declaration w) :=
  (congrArg (Bd.fill κ) (dTel.declaration_concatenate_inl Θ X w)).trans
    (Bd.fill_weaken_inl κ (Θ.declaration w))

/-- The entries bound by a slot of the first block of a concatenation, filled. -/
theorem dTel.binding_left_instantiate {Δ Ω Φ Λ : C.Arity} (Θ : dTel Δ Ω)
    (X : dTel (Δ ⋈ Ω) Φ) (κ : Subst (Ω ⋈ Φ) Δ) (w : Ω ∋ Λ) :
    dTel.instantiate κ ((dTel.concatenate Θ X).binding (C.inl w))
      = dTel.instantiate (fun ⦃γ⦄ (v : Ω ∋ γ) => κ (C.inl v)) (Θ.binding w) :=
  (congrArg (dTel.instantiate κ) (dTel.binding_concatenate_inl Θ X w)).trans
    (dTel.instantiate_weaken_inl κ (Θ.binding w))

/-- The declaration of a slot of the second block of a concatenation, filled. -/
theorem dTel.declaration_right_instantiate {Δ Ω Φ Λ : C.Arity} (Θ : dTel Δ Ω)
    (X : dTel (Δ ⋈ Ω) Φ) (κ : Subst (Ω ⋈ Φ) Δ) (z : Φ ∋ Λ) :
    Bd.fill (fun ⦃γ⦄ (j : Φ ∋ γ) => κ (C.inr j))
        ((dTel.instantiate (fun ⦃γ⦄ (i : Ω ∋ γ) => κ (C.inl i)) X).declaration z)
      = Bd.fill κ ((dTel.concatenate Θ X).declaration (C.inr z)) := by
  refine Eq.trans (congrArg (Bd.fill (fun ⦃γ⦄ (j : Φ ∋ γ) => κ (C.inr j)))
    (dTel.declaration_actBase _ X z)) ?_
  refine Eq.trans (Bd.act_copair_prefix
    (fun ⦃γ⦄ (j : Φ ∋ γ) => κ (C.inr j)) Λ _).symm ?_
  refine Eq.trans (Bd.act_comp (Γ := 1)
    (Subst.lift (Subst.copair (Subst.id Δ)
      (fun ⦃γ⦄ (i : Ω ∋ γ) => κ (C.inl i))) Φ)
    (Subst.copair (Subst.id Δ) (fun ⦃γ⦄ (j : Φ ∋ γ) => κ (C.inr j)))
    Λ (X.declaration z)).symm ?_
  refine Eq.trans (congrArg (fun t => Bd.act (Γ := 1) t Λ (X.declaration z))
    (Subst.copair_split κ)) ?_
  refine Eq.trans (Bd.act_copair_prefix κ Λ (X.declaration z)) ?_
  exact congrArg (Bd.fill κ) (dTel.declaration_concatenate_inr Θ X z).symm

/-- The entries bound by a slot of the second block of a concatenation, filled. -/
theorem dTel.binding_right_instantiate {Δ Ω Φ Λ : C.Arity} (Θ : dTel Δ Ω)
    (X : dTel (Δ ⋈ Ω) Φ) (κ : Subst (Ω ⋈ Φ) Δ) (z : Φ ∋ Λ) :
    dTel.instantiate (fun ⦃γ⦄ (j : Φ ∋ γ) => κ (C.inr j))
        ((dTel.instantiate (fun ⦃γ⦄ (i : Ω ∋ γ) => κ (C.inl i)) X).binding z)
      = dTel.instantiate κ ((dTel.concatenate Θ X).binding (C.inr z)) := by
  refine Eq.trans (congrArg (dTel.instantiate
    (fun ⦃γ⦄ (j : Φ ∋ γ) => κ (C.inr j))) (dTel.binding_actBase _ X z)) ?_
  refine Eq.trans (dTel.actBase_comp
    (Subst.lift (Subst.copair (Subst.id Δ)
      (fun ⦃γ⦄ (i : Ω ∋ γ) => κ (C.inl i))) Φ)
    (Subst.copair (Subst.id Δ) (fun ⦃γ⦄ (j : Φ ∋ γ) => κ (C.inr j)))
    (X.binding z)).symm ?_
  refine Eq.trans (congrArg (fun t => dTel.actBase t (X.binding z))
    (Subst.copair_split κ)) ?_
  exact congrArg (dTel.instantiate κ) (dTel.binding_concatenate_inr Θ X z).symm

/-- The declaration of a slot of the first block, filled by a pair. -/
theorem dTel.declaration_left_copair {Δ Ω Φ Λ : C.Arity} (Θ : dTel Δ Ω)
    (X : dTel (Δ ⋈ Ω) Φ) (σ : Subst Ω Δ) (τ : Subst Φ Δ) (w : Ω ∋ Λ) :
    Bd.fill (Subst.copair σ τ) ((dTel.concatenate Θ X).declaration (C.inl w))
      = Bd.fill σ (Θ.declaration w) := by
  refine (dTel.declaration_left_instantiate Θ X (Subst.copair σ τ) w).trans ?_
  exact congrArg (fun s => Bd.fill s (Θ.declaration w)) (Subst.copair_left σ τ)

/-- The entries bound by a slot of the first block, filled by a pair. -/
theorem dTel.binding_left_copair {Δ Ω Φ Λ : C.Arity} (Θ : dTel Δ Ω)
    (X : dTel (Δ ⋈ Ω) Φ) (σ : Subst Ω Δ) (τ : Subst Φ Δ) (w : Ω ∋ Λ) :
    dTel.instantiate (Subst.copair σ τ)
        ((dTel.concatenate Θ X).binding (C.inl w))
      = dTel.instantiate σ (Θ.binding w) := by
  refine (dTel.binding_left_instantiate Θ X (Subst.copair σ τ) w).trans ?_
  exact congrArg (fun s => dTel.instantiate s (Θ.binding w))
    (Subst.copair_left σ τ)

/-- The declaration of a slot of the second block, filled by a pair. -/
theorem dTel.declaration_right_copair {Δ Ω Φ Λ : C.Arity} (Θ : dTel Δ Ω)
    (X : dTel (Δ ⋈ Ω) Φ) (σ : Subst Ω Δ) (τ : Subst Φ Δ) (z : Φ ∋ Λ) :
    Bd.fill (Subst.copair σ τ) ((dTel.concatenate Θ X).declaration (C.inr z))
      = Bd.fill τ ((dTel.instantiate σ X).declaration z) := by
  refine (dTel.declaration_right_instantiate Θ X (Subst.copair σ τ) z).symm.trans ?_
  rw [Subst.copair_left σ τ, Subst.copair_right σ τ]

/-- The entries bound by a slot of the second block, filled by a pair. -/
theorem dTel.binding_right_copair {Δ Ω Φ Λ : C.Arity} (Θ : dTel Δ Ω)
    (X : dTel (Δ ⋈ Ω) Φ) (σ : Subst Ω Δ) (τ : Subst Φ Δ) (z : Φ ∋ Λ) :
    dTel.instantiate (Subst.copair σ τ)
        ((dTel.concatenate Θ X).binding (C.inr z))
      = dTel.instantiate τ ((dTel.instantiate σ X).binding z) := by
  refine (dTel.binding_right_instantiate Θ X (Subst.copair σ τ) z).symm.trans ?_
  rw [Subst.copair_left σ τ, Subst.copair_right σ τ]

/-- The entries bound by the first slot, filled, are the entries it binds. -/
theorem dTel.binding_head_instantiate {Δ α Ω : C.Arity} (bind : dTel Δ α)
    (boundary : Bd (Δ ⋈ α)) (rest : dTel (Δ ⋈ C.single α) Ω)
    (σ : Subst (C.single α ⋈ Ω) Δ) :
    σ ⋆ (dTel.cons bind boundary rest).binding (C.inl (C.singleSlot α)) = bind := by
  refine Eq.trans (congrArg (dTel.instantiate σ)
    (dTel.binding_head bind boundary rest)) ?_
  refine Eq.trans (dTel.actBase_rename_cancel (Renaming.inl Δ (C.single α ⋈ Ω))
    (𝟙ʳ Δ) (Subst.copair (Subst.id Δ) σ)
    (fun ⦃_⦄ x => Subst.copair_inl _ _ x) bind) ?_
  exact dTel.rename_id bind

/-- The declaration of the first slot, filled, is the boundary it declares. -/
theorem dTel.declaration_head_instantiate {Δ α Ω : C.Arity} (bind : dTel Δ α)
    (boundary : Bd (Δ ⋈ α)) (rest : dTel (Δ ⋈ C.single α) Ω)
    (σ : Subst (C.single α ⋈ Ω) Δ) :
    σ ⋆ (dTel.cons bind boundary rest).declaration (C.inl (C.singleSlot α))
      = boundary := by
  refine Eq.trans (congrArg (Bd.act (Γ := Δ) (Δ := C.single α ⋈ Ω) (Ξ := 1) σ α)
    (dTel.declaration_head bind boundary rest)) ?_
  refine Eq.trans (Bd.act_copair_prefix σ α _).symm ?_
  refine Eq.trans (Bd.act_rename_cancel (Renaming.inl Δ (C.single α ⋈ Ω)) (𝟙ʳ Δ)
    (Subst.copair (Subst.id Δ) σ) (fun ⦃_⦄ x => Subst.copair_inl _ _ x) α
    boundary) ?_
  exact (congrArg (fun ρ => Bd.rename ρ boundary)
    (Renaming.extend_id Δ α)).trans (Bd.rename_id boundary)

/-- The entries bound by a later slot, filled, are those entries after the first
slot is filled, filled by the remaining fillers. -/
theorem dTel.binding_tail_instantiate {Δ α Ω Λ : C.Arity} (bind : dTel Δ α)
    (boundary : Bd (Δ ⋈ α)) (rest : dTel (Δ ⋈ C.single α) Ω)
    (σ : Subst (C.single α ⋈ Ω) Δ) (y : Ω ∋ Λ) :
    σ ⋆ (dTel.cons bind boundary rest).binding (C.inr y)
      = (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j)) ⋆
          (dTel.instantiate (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i))
            rest).binding y := by
  refine Eq.trans (congrArg (dTel.instantiate σ)
    (dTel.binding_tail bind boundary rest y)) ?_
  refine Eq.trans (congrArg (fun s => dTel.actBase s (rest.binding y))
    (Subst.copair_split σ).symm) ?_
  refine Eq.trans (dTel.actBase_comp _ _ (rest.binding y)) ?_
  exact congrArg (dTel.actBase (Subst.copair (Subst.id Δ)
      (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j))))
    (dTel.binding_actBase (Subst.copair (Subst.id Δ)
      (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i))) rest y).symm

/-- The declaration of a later slot, filled, is that declaration after the first
slot is filled, filled by the remaining fillers. -/
theorem dTel.declaration_tail_instantiate {Δ α Ω Λ : C.Arity} (bind : dTel Δ α)
    (boundary : Bd (Δ ⋈ α)) (rest : dTel (Δ ⋈ C.single α) Ω)
    (σ : Subst (C.single α ⋈ Ω) Δ) (y : Ω ∋ Λ) :
    σ ⋆ (dTel.cons bind boundary rest).declaration (C.inr y)
      = (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j)) ⋆
          (dTel.instantiate (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i))
            rest).declaration y := by
  refine Eq.trans (congrArg (Bd.act (Γ := Δ) (Δ := C.single α ⋈ Ω) (Ξ := 1) σ Λ)
    (dTel.declaration_tail bind boundary rest y)) ?_
  refine Eq.trans (Bd.act_copair_prefix σ Λ (rest.declaration y)).symm ?_
  refine Eq.trans (congrArg (fun (s : Subst (Δ ⋈ C.single α ⋈ Ω) Δ) =>
    Bd.act (Γ := 1) s Λ (rest.declaration y)) (Subst.copair_split σ).symm) ?_
  refine Eq.trans (Bd.act_comp (Γ := 1)
    (Subst.lift (Subst.copair (Subst.id Δ)
      (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i))) Ω)
    (Subst.copair (Subst.id Δ) (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j)))
    Λ (rest.declaration y)) ?_
  refine Eq.trans (Bd.act_copair_prefix
    (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j)) Λ _) ?_
  exact congrArg (Bd.act (Γ := Δ) (Δ := Ω) (Ξ := 1)
      (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j)) Λ)
    (dTel.declaration_actBase (Subst.copair (Subst.id Δ)
      (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i))) rest y).symm
