import HigherRankSyntax.Shape

/-!
# Renamings of shapes

A *renaming* `Γ →ʳ Δ` is an arity-preserving slot map.

## Notations

  - `Γ →ʳ Δ` is the type of renamings from `Γ` to `Δ`.
  - `𝟙ʳ` is the identity renaming.
  - `g ∘ʳʳ f` is composition "g after f".
  - `ρ ⇑ʳ α` extends a renaming through a fresh binder.
-/

/-- A renaming of shapes from `Γ` to `Δ`: an arity-preserving slot map. -/
abbrev Renaming {C : Carrier} (Γ Δ : Shape C) := ∀ {α}, Γ ∋ α → Δ ∋ α

@[inherit_doc Renaming]
infixr:25 " →ʳ " => Renaming

/-- The identity renaming on `Γ`. -/
def Renaming.id {C : Carrier} (Γ : Shape C) : Γ →ʳ Γ :=
  fun {_} x => x

@[inherit_doc Renaming.id]
notation "𝟙ʳ" => Renaming.id

/-- Composition of renamings: `comp f g` sends a slot through `f`, then through `g`. -/
def Renaming.comp
    {C : Carrier} {Γ Δ Ξ : Shape C}
    (f : Γ →ʳ Δ) (g : Δ →ʳ Ξ)
  : Γ →ʳ Ξ :=
  fun x => g (f x)

@[inherit_doc Renaming.comp]
notation:90 g:90 " ∘ʳʳ " f:91 => Renaming.comp f g

@[ext]
theorem Renaming.ext
    {C : Carrier} {Γ Δ : Shape C}
    {f g : Γ →ʳ Δ}
    (h : ∀ α (x : Γ ∋ α), f x = g x) :
  @f = @g
  := by
  congr
  funext α x
  exact h α x

/-- Extend a renaming through a fresh binder of arity `β`. -/
def Renaming.extend
    {C : Carrier} {Γ Δ : Shape C}
    (f : Γ →ʳ Δ) (β : C.Arity) :
  Γ ∷ β →ʳ Δ ∷ β
  | _, .here i  => .here i
  | _, .there x => .there (f x)

@[inherit_doc Renaming.extend]
infixl:95 " ⇑ʳ " => Renaming.extend

@[simp]
theorem Renaming.extend_here
  {C : Carrier} {Γ Δ : Shape C} (f : Γ →ʳ Δ)
    {β : C.Arity} (i : C.Binder β) :
  (f ⇑ʳ β) (.here i) = .here i
  := rfl

@[simp]
theorem Renaming.extend_there
    {C : Carrier} {Γ Δ : Shape C}
    (f : Γ →ʳ Δ)
    {β α : C.Arity} (x : Γ ∋ α) :
  (f ⇑ʳ β) (.there x) = .there (f x)
  := rfl

@[simp]
theorem Renaming.id_apply
    {C : Carrier} {Γ : Shape C} {α : C.Arity}
    (x : Γ ∋ α) :
  𝟙ʳ Γ x = x
  := rfl

@[simp]
theorem Renaming.extend_id
    {C : Carrier} (Γ : Shape C) (β : C.Arity) :
  (𝟙ʳ Γ ⇑ʳ β : Γ ∷ β →ʳ Γ ∷ β) = (𝟙ʳ (Γ ∷ β) : Γ ∷ β →ʳ Γ ∷ β)
  := by
  ext α p
  cases p with
  | here _  => rfl
  | there _ => rfl

@[simp]
theorem Renaming.extend_comp
    {C : Carrier} {Γ Δ Ξ : Shape C}
    (f : Γ →ʳ Δ) (g : Δ →ʳ Ξ) (β : C.Arity) :
  ((g ∘ʳʳ f) ⇑ʳ β : Γ ∷ β →ʳ Ξ ∷ β) = ((g ⇑ʳ β) ∘ʳʳ (f ⇑ʳ β) : Γ ∷ β →ʳ Ξ ∷ β)
  := by
  ext α p
  cases p with
  | here _  => rfl
  | there _ => rfl
