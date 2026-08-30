import HigherRankSyntax.ListCarrier

/-!
# Renamings of arities

A *renaming* `Γ →ʳ Δ` is an arity-preserving slot map.

## Notations

  - `Γ →ʳ Δ` is the type of renamings from `Γ` to `Δ`.
  - `𝟙ʳ` is the identity renaming.
  - `g ∘ʳ f` is composition "g after f".
  - `ρ ⇑ʳ α` extends a renaming through a fresh position.
-/

/-- A renaming of arities from `Γ` to `Δ`: an arity-preserving slot map. -/
abbrev Renaming (Γ Δ : C.Arity) :=
  ∀ ⦃α : C.Arity⦄, Γ ∋ α → Δ ∋ α

@[inherit_doc Renaming]
infixr:25 " →ʳ " => Renaming

/-- The identity renaming on `Γ`. -/
def Renaming.id (Γ : C.Arity) : Γ →ʳ Γ :=
  fun ⦃_⦄ x => x

@[inherit_doc Renaming.id]
notation "𝟙ʳ" => Renaming.id

/-- Composition of renamings: `comp f g` sends a slot through `f`, then through `g`. -/
def Renaming.comp
    {Γ Δ Ξ : C.Arity}
    (f : Γ →ʳ Δ) (g : Δ →ʳ Ξ)
  : Γ →ʳ Ξ :=
  fun ⦃_⦄ x => g (f x)

@[inherit_doc Renaming.comp]
notation:90 g:90 " ∘ʳ " f:91 => Renaming.comp f g

/-- Extend a renaming through a fresh position of arity `β`. -/
@[reducible]
def Renaming.extend
    {Γ Δ : C.Arity}
    (f : Γ →ʳ Δ) (Ξ : C.Arity) :
  Γ ⋈ Ξ →ʳ Δ ⋈ Ξ :=
  fun ⦃α⦄ x => C.copair Γ Ξ ((Δ ⋈ Ξ) ∋ α)
    (fun y => C.inl (f y)) (fun z => C.inr z)
      x

@[inherit_doc Renaming.extend]
infixl:95 " ⇑ʳ " => Renaming.extend

/-- Keep a prefix fixed and apply a renaming after it. -/
def Renaming.prefixed (S : C.Arity) {Γ Δ : C.Arity}
    (ρ : Γ →ʳ Δ) : S ⋈ Γ →ʳ S ⋈ Δ :=
  fun ⦃Λ⦄ x => C.copair S Γ (S ⋈ Δ ∋ Λ)
    (fun y => C.inl y) (fun y => C.inr (ρ y)) x

@[simp]
theorem Renaming.prefixed_inl (S : C.Arity) {Γ Δ Λ : C.Arity}
    (ρ : Γ →ʳ Δ) (x : S ∋ Λ) :
    prefixed S ρ (C.inl x) = C.inl x := by
  apply C.copair_apply_inl

@[simp]
theorem Renaming.prefixed_inr (S : C.Arity) {Γ Δ Λ : C.Arity}
    (ρ : Γ →ʳ Δ) (x : Γ ∋ Λ) :
    prefixed S ρ (C.inr x) = C.inr (ρ x) := by
  apply C.copair_apply_inr

@[simp]
theorem Renaming.extend_inl
    {Γ Δ Ξ : C.Arity}
    (f : Γ →ʳ Δ) {α : C.Arity} (i : Γ ∋ α) :
  (f ⇑ʳ Ξ) (C.inl i) = C.inl (f i)
  := by
  simp [Renaming.extend]

@[simp]
theorem Renaming.extend_inr
    {Γ Δ Ξ : C.Arity}
    (f : Γ →ʳ Δ) {α : C.Arity} (i : Ξ ∋ α) :
  (f ⇑ʳ Ξ) (C.inr i) = C.inr i
  := by
  simp [Renaming.extend]

@[simp]
theorem Renaming.extend_id
    (Γ Δ : C.Arity) :
  𝟙ʳ Γ ⇑ʳ Δ = 𝟙ʳ (Γ ⋈ Δ)
  := by
  funext α x
  rcases C.cover Γ Δ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    <;> simp [Renaming.id]

/-- The left injection as a renaming. -/
def Renaming.inl (Γ Δ : C.Arity) : Γ →ʳ Γ ⋈ Δ := fun ⦃_⦄ x => C.inl x

/-- The right injection as a renaming. -/
def Renaming.inr (Γ Δ : C.Arity) : Δ →ʳ Γ ⋈ Δ := fun ⦃_⦄ x => C.inr x

/-- The unique renaming out of the unit arity. -/
def Renaming.fromUnit (Γ : C.Arity) : (1 : C.Arity) →ʳ Γ :=
  fun ⦃_⦄ x => (C.unit_is_empty x).elim

/-- Prefixing by the unit arity changes nothing. -/
theorem Renaming.prefixed_unit {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) :
  Renaming.prefixed 1 ρ = ρ := by
  funext β x
  rcases C.cover 1 Γ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact (C.unit_is_empty y).elim
  · rw [Renaming.prefixed_inr, C.unit_left, C.unit_left]

/-- Extending a renaming by the unit arity changes nothing. -/
theorem Renaming.extend_unit
    {Γ Δ : C.Arity} (f : Γ →ʳ Δ) :
  f ⇑ʳ 1 = f
  := by
  funext α x
  rcases C.cover Γ 1 x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · rw [Renaming.extend_inl, C.unit_right Δ (f y), C.unit_right Γ y]
  · exact (C.unit_is_empty y).elim

@[simp]
theorem Renaming.extend_comp
    {Γ Δ Ξ : C.Arity}
    (f : Γ →ʳ Δ) (g : Δ →ʳ Ξ) (Ω : C.Arity) :
  (g ∘ʳ f) ⇑ʳ Ω = (g ⇑ʳ Ω) ∘ʳ (f ⇑ʳ Ω)
  := by
  funext α x
  rcases C.cover Γ Ω x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    <;> simp [Renaming.comp]

/-- Extension commutes with the left injection. -/
theorem Renaming.inl_comp {Γ Δ Φ : C.Arity} (ρ : Γ →ʳ Δ) :
  (Renaming.inl Δ Φ) ∘ʳ ρ = (ρ ⇑ʳ Φ) ∘ʳ (Renaming.inl Γ Φ)
  := by
  funext α x
  exact (Renaming.extend_inl ρ x).symm

/-- Weakening on the right commutes with weakening past a suffix. -/
theorem Renaming.inl_inl_extend (Δ Ω Φ : C.Arity) :
    (Renaming.inl (Δ ⋈ Ω) Φ) ∘ʳ (Renaming.inl Δ Ω)
      = (Renaming.inl Δ Ω ⇑ʳ Φ) ∘ʳ (Renaming.inl Δ Φ) := by
  funext α y
  exact (Renaming.extend_inl (Renaming.inl Δ Ω) y).symm

/-- Weakening on the right, twice, is weakening by the product. -/
theorem Renaming.inl_inl (Γ Δ Ξ : C.Arity) :
    (Renaming.inl (Γ ⋈ Δ) Ξ) ∘ʳ (Renaming.inl Γ Δ) = Renaming.inl Γ (Δ ⋈ Ξ) := by
  funext α x
  exact (C.inl_inl Γ Δ Ξ x).symm

@[simp]
theorem Renaming.extend_assoc
    {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) (Ξ Ω : C.Arity) :
    ρ ⇑ʳ (Ξ ⋈ Ω) = (ρ ⇑ʳ Ξ) ⇑ʳ Ω := by
  funext α x
  rcases C.cover (Γ ⋈ Ξ) Ω x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · rcases C.cover Γ Ξ y with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · calc
        _ = (ρ ⇑ʳ (Ξ ⋈ Ω)) (C.inl z) :=
          by
            apply congrArg (fun w : Γ ⋈ (Ξ ⋈ Ω) ∋ α => (ρ ⇑ʳ (Ξ ⋈ Ω)) w)
            exact (C.inl_inl Γ Ξ Ω z).symm
        _ = C.inl (ρ z) := Renaming.extend_inl ρ z
        _ = C.inl (C.inl (ρ z)) := C.inl_inl Δ Ξ Ω (ρ z)
        _ = _ := by simp
    · calc
        _ = (ρ ⇑ʳ (Ξ ⋈ Ω)) (C.inr (C.inl z)) :=
          by
            apply congrArg (fun w : Γ ⋈ (Ξ ⋈ Ω) ∋ α => (ρ ⇑ʳ (Ξ ⋈ Ω)) w)
            exact (C.inr_inl Γ Ξ Ω z).symm
        _ = C.inr (C.inl z) := Renaming.extend_inr ρ (C.inl z)
        _ = C.inl (C.inr z) := C.inr_inl Δ Ξ Ω z
        _ = _ := by simp
  · calc
      _ = (ρ ⇑ʳ (Ξ ⋈ Ω)) (C.inr (C.inr z)) :=
        by
          apply congrArg (fun w : Γ ⋈ (Ξ ⋈ Ω) ∋ α => (ρ ⇑ʳ (Ξ ⋈ Ω)) w)
          exact (C.inr_inr Γ Ξ Ω z).symm
      _ = C.inr (C.inr z) := Renaming.extend_inr ρ (C.inr z)
      _ = (C.inr z : (Δ ⋈ Ξ) ⋈ Ω ∋ α) := C.inr_inr Δ Ξ Ω z
      _ = _ := by simp
