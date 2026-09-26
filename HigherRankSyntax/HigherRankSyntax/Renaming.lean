import HigherRankSyntax.ListCarrier

/-!
# Renamings of arities

A *renaming* `Γ →ʳ Δ` is an arity-preserving slot map.

## Notations

  - `Γ →ʳ Δ` is the type of renamings from `Γ` to `Δ`.
  - `𝟙ʳ` is the identity renaming.
  - `g ∘ʳ f` is composition "g after f".
  - `ρ ⇑ʳ Ξ` extends a renaming `Γ →ʳ Δ` to `Γ ⋈ Ξ →ʳ Δ ⋈ Ξ`, fixing the slots
    of `Ξ`.
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
    {Γ Δ Ξ : C.Arity} (f : Γ →ʳ Δ) (g : Δ →ʳ Ξ) :
  Γ →ʳ Ξ :=
  fun ⦃_⦄ x => g (f x)

@[inherit_doc Renaming.comp]
notation:90 g:90 " ∘ʳ " f:91 => Renaming.comp f g

/-- The renaming `Γ ⋈ Ξ →ʳ Δ ⋈ Ξ` acting as `f` on the slots of `Γ` and fixing the
slots of `Ξ`. -/
@[reducible]
def Renaming.extend
    {Γ Δ : C.Arity} (f : Γ →ʳ Δ) (Ξ : C.Arity) :
  Γ ⋈ Ξ →ʳ Δ ⋈ Ξ :=
  fun ⦃α⦄ x => C.copair Γ Ξ ((Δ ⋈ Ξ) ∋ α)
    (fun y => C.inl (f y)) (fun z => C.inr z) x

@[inherit_doc Renaming.extend]
infixl:95 " ⇑ʳ " => Renaming.extend

/-- The renaming `S ⋈ Γ →ʳ S ⋈ Δ` fixing the slots of `S` and acting as `ρ` on the
slots of `Γ`. -/
def Renaming.prefixed (S : C.Arity) {Γ Δ : C.Arity}
    (ρ : Γ →ʳ Δ) : S ⋈ Γ →ʳ S ⋈ Δ :=
  fun ⦃Λ⦄ x => C.copair S Γ (S ⋈ Δ ∋ Λ)
    (fun y => C.inl y) (fun y => C.inr (ρ y)) x

@[simp]
theorem Renaming.prefixed_inl
    (S : C.Arity) {Γ Δ Λ : C.Arity} (ρ : Γ →ʳ Δ) (x : S ∋ Λ) :
  prefixed S ρ (C.inl x) = C.inl x
  := by
  apply C.copair_apply_inl

@[simp]
theorem Renaming.prefixed_inr
    (S : C.Arity) {Γ Δ Λ : C.Arity} (ρ : Γ →ʳ Δ) (x : Γ ∋ Λ) :
  prefixed S ρ (C.inr x) = C.inr (ρ x)
  := by
  apply C.copair_apply_inr

@[simp]
theorem Renaming.extend_inl
    {Γ Δ Ξ : C.Arity} (f : Γ →ʳ Δ) {α : C.Arity} (i : Γ ∋ α) :
  (f ⇑ʳ Ξ) (C.inl i) = C.inl (f i)
  := by
  apply C.copair_apply_inl

@[simp]
theorem Renaming.extend_inr
    {Γ Δ Ξ : C.Arity} (f : Γ →ʳ Δ) {α : C.Arity} (i : Ξ ∋ α) :
  (f ⇑ʳ Ξ) (C.inr i) = C.inr i
  := by
  apply C.copair_apply_inr

@[simp]
theorem Renaming.extend_id (Γ Δ : C.Arity) :
  𝟙ʳ Γ ⇑ʳ Δ = 𝟙ʳ (Γ ⋈ Δ)
  := by
  funext α x
  rcases C.cover Γ Δ x with ⟨y, rfl⟩ | ⟨y, rfl⟩ <;> simp [Renaming.id]

/-- The left injection as a renaming. -/
def Renaming.inl (Γ Δ : C.Arity) : Γ →ʳ Γ ⋈ Δ := fun ⦃_⦄ x => C.inl x

/-- The right injection as a renaming. -/
def Renaming.inr (Γ Δ : C.Arity) : Δ →ʳ Γ ⋈ Δ := fun ⦃_⦄ x => C.inr x

/-- The unique renaming out of the unit arity. -/
def Renaming.fromUnit (Γ : C.Arity) : (1 : C.Arity) →ʳ Γ :=
  fun ⦃_⦄ x => (C.unit_is_empty x).elim

/-- The renaming out of the unit arity is unique. -/
theorem Renaming.eq_fromUnit {Γ : C.Arity} (ρ : (1 : C.Arity) →ʳ Γ) :
  ρ = fromUnit Γ
  := by
  funext α x
  apply (C.unit_is_empty x).elim

/-- Extending the renaming out of the unit arity by `Γ` gives the right injection
`Γ →ʳ Δ ⋈ Γ`. -/
theorem Renaming.fromUnit_extend (Δ Γ : C.Arity) :
  fromUnit Δ ⇑ʳ Γ = inr Δ Γ
  := by
  funext α x
  rcases C.cover 1 Γ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · apply (C.unit_is_empty y).elim
  · rw [extend_inr, inr, C.unit_left]

/-- Extending a renaming by the unit arity changes nothing. -/
theorem Renaming.extend_unit {Γ Δ : C.Arity} (f : Γ →ʳ Δ) :
  f ⇑ʳ 1 = f
  := by
  funext α x
  rcases C.cover Γ 1 x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · rw [extend_inl, C.unit_right Δ (f y), C.unit_right Γ y]
  · apply (C.unit_is_empty y).elim

@[simp]
theorem Renaming.extend_comp
    {Γ Δ Ξ : C.Arity} (f : Γ →ʳ Δ) (g : Δ →ʳ Ξ) (Ω : C.Arity) :
  (g ∘ʳ f) ⇑ʳ Ω = (g ⇑ʳ Ω) ∘ʳ (f ⇑ʳ Ω)
  := by
  funext α x
  rcases C.cover Γ Ω x with ⟨y, rfl⟩ | ⟨y, rfl⟩ <;> simp [comp]

/-- `ρ ⇑ʳ Φ` acts as `ρ` on the left-injected slots: `inl ∘ʳ ρ = (ρ ⇑ʳ Φ) ∘ʳ inl`. -/
theorem Renaming.inl_comp {Γ Δ Φ : C.Arity} (ρ : Γ →ʳ Δ) :
  inl Δ Φ ∘ʳ ρ = (ρ ⇑ʳ Φ) ∘ʳ inl Γ Φ
  := by
  funext α x
  symm
  apply extend_inl

/-- Composing the left injections of `Γ` into `Γ ⋈ Δ` and of `Γ ⋈ Δ` into
`Γ ⋈ Δ ⋈ Ξ` gives the left injection of `Γ` into `Γ ⋈ (Δ ⋈ Ξ)`. -/
theorem Renaming.inl_inl (Γ Δ Ξ : C.Arity) :
  inl (Γ ⋈ Δ) Ξ ∘ʳ inl Γ Δ = inl Γ (Δ ⋈ Ξ)
  := by
  funext α x
  symm
  apply C.inl_inl

@[simp]
theorem Renaming.extend_assoc
    {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) (Ξ Ω : C.Arity) :
  ρ ⇑ʳ (Ξ ⋈ Ω) = (ρ ⇑ʳ Ξ) ⇑ʳ Ω
  := by
  funext α x
  rcases C.cover (Γ ⋈ Ξ) Ω x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · rcases C.cover Γ Ξ y with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · calc
        _ = (ρ ⇑ʳ (Ξ ⋈ Ω)) (C.inl z) := by rw [C.inl_inl]
        _ = C.inl (C.inl (ρ z)) := by rw [extend_inl, C.inl_inl]
        _ = _ := by simp
    · calc
        _ = (ρ ⇑ʳ (Ξ ⋈ Ω)) (C.inr (C.inl z)) := by rw [C.inr_inl]
        _ = C.inl (C.inr z) := by rw [extend_inr, C.inr_inl]
        _ = _ := by simp
  · calc
      _ = (ρ ⇑ʳ (Ξ ⋈ Ω)) (C.inr (C.inr z)) := by rw [C.inr_inr]
      _ = (C.inr z : (Δ ⋈ Ξ) ⋈ Ω ∋ α) := by rw [extend_inr, C.inr_inr]
      _ = _ := by simp
