import HigherRankSyntax.Carrier

/-!
# Renamings of arities

A *renaming* `Γ →ʳ Δ` is an arity-preserving slot map.

## Notations

  - `Γ →ʳ Δ` is the type of renamings from `Γ` to `Δ`.
  - `𝟙ʳ` is the identity renaming.
  - `g ∘ʳ f` is composition "g after f".
  - `ρ ⇑ʳ α` extends a renaming through a fresh position.
-/

variable {A : Type} {C : Carrier A}

/-- A renaming of arities from `Γ` to `Δ`: an arity-preserving slot map. -/
abbrev Renaming (Γ Δ : C.Arity) :=
  ∀ ⦃α : C.Arity⦄ ⦃τ : C.Ty⦄, Γ ∋[τ] α → Δ ∋[τ] α

@[inherit_doc Renaming]
infixr:25 " →ʳ " => Renaming

/-- The identity renaming on `Γ`. -/
def Renaming.id (Γ : C.Arity) : Γ →ʳ Γ :=
  fun ⦃_⦄ ⦃_⦄ x => x

@[inherit_doc Renaming.id]
notation "𝟙ʳ" => Renaming.id

/-- Composition of renamings: `comp f g` sends a slot through `f`, then through `g`. -/
def Renaming.comp
    {Γ Δ Ξ : C.Arity}
    (f : Γ →ʳ Δ) (g : Δ →ʳ Ξ)
  : Γ →ʳ Ξ :=
  fun ⦃_⦄ ⦃_⦄ x => g (f x)

@[inherit_doc Renaming.comp]
notation:90 g:90 " ∘ʳ " f:91 => Renaming.comp f g

/-- Extend a renaming through a fresh position of arity `β`. -/
@[reducible]
def Renaming.extend
    {Γ Δ : C.Arity}
    (f : Γ →ʳ Δ) (Ξ : C.Arity) :
  Γ ⋈ Ξ →ʳ Δ ⋈ Ξ :=
  fun ⦃α⦄ ⦃τ⦄ x => C.copair Γ Ξ ((Δ ⋈ Ξ) ∋[τ] α)
    (fun y => C.inl (f y)) (fun z => C.inr z)
      x

@[inherit_doc Renaming.extend]
infixl:95 " ⇑ʳ " => Renaming.extend

/-- Keep a prefix fixed and apply a renaming after it. -/
def Renaming.prefixed (S : C.Arity) {Γ Δ : C.Arity}
    (ρ : Γ →ʳ Δ) : S ⋈ Γ →ʳ S ⋈ Δ :=
  fun ⦃Λ⦄ ⦃τ⦄ x => C.copair S Γ (S ⋈ Δ ∋[τ] Λ)
    (fun y => C.inl y) (fun y => C.inr (ρ y)) x

@[simp]
theorem Renaming.prefixed_inl (S : C.Arity) {Γ Δ Λ : C.Arity}
    {τ : C.Ty} (ρ : Γ →ʳ Δ) (x : S ∋[τ] Λ) :
    prefixed S ρ (C.inl x) = C.inl x := by
  apply C.copair_apply_inl

@[simp]
theorem Renaming.prefixed_inr (S : C.Arity) {Γ Δ Λ : C.Arity}
    {τ : C.Ty} (ρ : Γ →ʳ Δ) (x : Γ ∋[τ] Λ) :
    prefixed S ρ (C.inr x) = C.inr (ρ x) := by
  apply C.copair_apply_inr

@[simp]
theorem Renaming.extend_inl
    {Γ Δ Ξ : C.Arity}
    (f : Γ →ʳ Δ) {α : C.Arity} {τ : C.Ty} (i : Γ ∋[τ] α) :
  (f ⇑ʳ Ξ) (C.inl i) = C.inl (f i)
  := by
  simp [Renaming.extend]

@[simp]
theorem Renaming.extend_inr
    {Γ Δ Ξ : C.Arity}
    (f : Γ →ʳ Δ) {α : C.Arity} {τ : C.Ty} (i : Ξ ∋[τ] α) :
  (f ⇑ʳ Ξ) (C.inr i) = C.inr i
  := by
  simp [Renaming.extend]

@[simp]
theorem Renaming.extend_id
    (Γ Δ : C.Arity) :
  𝟙ʳ Γ ⇑ʳ Δ = 𝟙ʳ (Γ ⋈ Δ)
  := by
  funext α τ x
  rcases C.cover Γ Δ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    <;> simp [Renaming.id]

@[simp]
theorem Renaming.extend_comp
    {Γ Δ Ξ : C.Arity}
    (f : Γ →ʳ Δ) (g : Δ →ʳ Ξ) (Ω : C.Arity) :
  (g ∘ʳ f) ⇑ʳ Ω = (g ⇑ʳ Ω) ∘ʳ (f ⇑ʳ Ω)
  := by
  funext α τ x
  rcases C.cover Γ Ω x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    <;> simp [Renaming.comp]

@[simp]
theorem Renaming.extend_assoc
    {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) (Ξ Ω : C.Arity) :
    ρ ⇑ʳ (Ξ ⋈ Ω) = (ρ ⇑ʳ Ξ) ⇑ʳ Ω := by
  funext α τ x
  rcases C.cover (Γ ⋈ Ξ) Ω x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · rcases C.cover Γ Ξ y with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · calc
        _ = (ρ ⇑ʳ (Ξ ⋈ Ω)) (C.inl z) :=
          by
            apply congrArg (fun w : Γ ⋈ (Ξ ⋈ Ω) ∋[τ] α => (ρ ⇑ʳ (Ξ ⋈ Ω)) w)
            exact (C.inl_inl Γ Ξ Ω z).symm
        _ = C.inl (ρ z) := Renaming.extend_inl ρ z
        _ = C.inl (C.inl (ρ z)) := C.inl_inl Δ Ξ Ω (ρ z)
        _ = _ := by simp
    · calc
        _ = (ρ ⇑ʳ (Ξ ⋈ Ω)) (C.inr (C.inl z)) :=
          by
            apply congrArg (fun w : Γ ⋈ (Ξ ⋈ Ω) ∋[τ] α => (ρ ⇑ʳ (Ξ ⋈ Ω)) w)
            exact (C.inr_inl Γ Ξ Ω z).symm
        _ = C.inr (C.inl z) := Renaming.extend_inr ρ (C.inl z)
        _ = C.inl (C.inr z) := C.inr_inl Δ Ξ Ω z
        _ = _ := by simp
  · calc
      _ = (ρ ⇑ʳ (Ξ ⋈ Ω)) (C.inr (C.inr z)) :=
        by
          apply congrArg (fun w : Γ ⋈ (Ξ ⋈ Ω) ∋[τ] α => (ρ ⇑ʳ (Ξ ⋈ Ω)) w)
          exact (C.inr_inr Γ Ξ Ω z).symm
      _ = C.inr (C.inr z) := Renaming.extend_inr ρ (C.inr z)
      _ = (C.inr z : (Δ ⋈ Ξ) ⋈ Ω ∋[τ] α) := C.inr_inr Δ Ξ Ω z
      _ = _ := by simp
