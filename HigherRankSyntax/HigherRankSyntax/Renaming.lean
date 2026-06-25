import HigherRankSyntax.Carrier
-- import HigherRankSyntax.ProperTele

/-!
# Renamings of shapes

A *renaming* `Γ →ʳ Δ` is an arity-preserving slot map.

## Notations

  - `Γ →ʳ Δ` is the type of renamings from `Γ` to `Δ`.
  - `𝟙ʳ` is the identity renaming.
  - `g ∘ʳ f` is composition "g after f".
  - `ρ ⇑ʳ α` extends a renaming through a fresh position.
-/

/-- A renaming of shapes from `Γ` to `Δ`: an arity-preserving slot map. -/
abbrev Renaming {A : Type} {C : Carrier A} (Γ Δ : C.Arity) :=
  ∀ ⦃ α ⦄, Γ ∋ α → Δ ∋ α

@[inherit_doc Renaming]
infixr:25 " →ʳ " => Renaming

/-- The identity renaming on `Γ`. -/
def Renaming.id {A : Type} {C : Carrier A} (Γ : C.Arity) : Γ →ʳ Γ :=
  fun ⦃_⦄ x => x

@[inherit_doc Renaming.id]
notation "𝟙ʳ" => Renaming.id

/-- Composition of renamings: `comp f g` sends a slot through `f`, then through `g`. -/
def Renaming.comp
    {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
    (f : Γ →ʳ Δ) (g : Δ →ʳ Ξ)
  : Γ →ʳ Ξ :=
  fun ⦃_⦄ x => g (f x)

@[inherit_doc Renaming.comp]
notation:90 g:90 " ∘ʳ " f:91 => Renaming.comp f g

/-- Extend a renaming through a fresh position of arity `β`. -/
@[reducible]
def Renaming.extend
    {A : Type} {C : Carrier A} {Γ Δ : C.Arity}
    (f : Γ →ʳ Δ) (Ξ : C.Arity) :
  Γ ⋈ Ξ →ʳ Δ ⋈ Ξ :=
  fun ⦃ α ⦄ x => C.copair Ξ Γ (Δ ⋈ Ξ ∋ α)
    (fun z => C.inl z) (fun y => C.inr (f y))
      x

@[inherit_doc Renaming.extend]
infixl:95 " ⇑ʳ " => Renaming.extend

@[simp]
theorem Renaming.extend_inl
    {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
    (f : Γ →ʳ Δ) {α : C.Arity} (i : Ξ ∋ α) :
  (f ⇑ʳ Ξ) (C.inl i) = C.inl i
  := by
  let eq := C.copair_inl Ξ Γ (Δ ⋈ Ξ ∋ α)
    (fun z => C.inl z) (fun y => C.inr (f y))
  simpa [Renaming.extend] using congrFun eq i

@[simp]
theorem Renaming.extend_inr
    {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
    (f : Γ →ʳ Δ) {α : C.Arity} (i : Γ ∋ α) :
  (f ⇑ʳ Ξ) (C.inr i) = C.inr (f i)
  := by
  let eq := C.copair_inr Ξ Γ (Δ ⋈ Ξ ∋ α)
    (fun z => C.inl z) (fun y => C.inr (f y))
  simpa [Renaming.extend] using congrFun (C.copair_inr Ξ Γ (Δ ⋈ Ξ ∋ α)
    (fun z => C.inl z) (fun y => C.inr (f y))) i

@[simp]
theorem Renaming.extend_id
    {A : Type} {C : Carrier A} (Γ Δ : C.Arity) :
  𝟙ʳ Γ ⇑ʳ Δ = 𝟙ʳ (Γ ⋈ Δ)
  := by
  funext α x
  rcases C.cover Δ Γ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    <;> simp [Renaming.id]

@[simp]
theorem Renaming.extend_comp
    {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
    (f : Γ →ʳ Δ) (g : Δ →ʳ Ξ) (Ω : C.Arity) :
  (g ∘ʳ f) ⇑ʳ Ω = (g ⇑ʳ Ω) ∘ʳ (f ⇑ʳ Ω)
  := by
  funext α x
  rcases C.cover Ω Γ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    <;> simp [Renaming.comp]
