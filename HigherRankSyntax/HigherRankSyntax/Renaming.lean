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
structure Renaming {C : Carrier} (Γ Δ : Shape C) : Type where
  /-- The underlying slot map. -/
  apply : ∀ {α : C.Arity}, Γ ∋ α → Δ ∋ α

@[inherit_doc Renaming]
infixr:25 " →ʳ " => Renaming

instance {C : Carrier} {Γ Δ : Shape C} :
    CoeFun (Γ →ʳ Δ) (fun _ => ∀ {α : C.Arity}, Γ ∋ α → Δ ∋ α) :=
  ⟨Renaming.apply⟩

/-- The identity renaming on `Γ`. -/
def Renaming.id {C : Carrier} (Γ : Shape C) : Γ →ʳ Γ :=
  ⟨fun {_} p => p⟩

@[inherit_doc Renaming.id]
notation "𝟙ʳ" => Renaming.id _

/-- Composition of renamings: `comp f g` sends a slot through `f`, then through `g`. -/
def Renaming.comp {C : Carrier} {Γ Δ Ξ : Shape C} (f : Γ →ʳ Δ) (g : Δ →ʳ Ξ) : Γ →ʳ Ξ :=
  ⟨fun {_} p => g (f p)⟩

@[inherit_doc Renaming.comp]
notation:90 g:90 " ∘ʳʳ " f:91 => Renaming.comp f g

@[ext]
theorem Renaming.ext {C : Carrier} {Γ Δ : Shape C} {f g : Γ →ʳ Δ}
    (h : ∀ {α : C.Arity} (p : Γ ∋ α), f p = g p) : f = g := by
  cases f
  cases g
  congr
  funext α p
  exact h p

theorem Renaming.id_comp {C : Carrier} {Γ Δ : Shape C} (f : Γ →ʳ Δ) : f ∘ʳʳ 𝟙ʳ = f := rfl

theorem Renaming.comp_id {C : Carrier} {Γ Δ : Shape C} (f : Γ →ʳ Δ) : 𝟙ʳ ∘ʳʳ f = f := rfl

theorem Renaming.comp_assoc {C : Carrier} {Γ Δ Ξ Θ : Shape C}
    (f : Γ →ʳ Δ) (g : Δ →ʳ Ξ) (h : Ξ →ʳ Θ) : h ∘ʳʳ (g ∘ʳʳ f) = (h ∘ʳʳ g) ∘ʳʳ f := rfl

/-- Extend a renaming through a fresh binder of arity `β`. -/
def Renaming.extend {C : Carrier} {Γ Δ : Shape C} (f : Γ →ʳ Δ) (β : C.Arity) :
    Γ ∷ β →ʳ Δ ∷ β :=
  ⟨fun
    | .here i  => .here i
    | .there p => .there (f p)⟩

@[inherit_doc Renaming.extend]
infixl:95 " ⇑ʳ " => Renaming.extend

@[simp] theorem Renaming.extend_here {C : Carrier} {Γ Δ : Shape C} (f : Γ →ʳ Δ)
    {β : C.Arity} (i : C.Binder β) :
    (f ⇑ʳ β) (.here i) = .here i := rfl

@[simp] theorem Renaming.extend_there {C : Carrier} {Γ Δ : Shape C} (f : Γ →ʳ Δ)
    {β α : C.Arity} (p : Γ ∋ α) :
    (f ⇑ʳ β) (.there p) = .there (f p) := rfl

@[simp] theorem Renaming.id_apply {C : Carrier} {Γ : Shape C} {α : C.Arity} (p : Γ ∋ α) :
    (𝟙ʳ : Γ →ʳ Γ) p = p := rfl

@[simp]
theorem Renaming.extend_id {C : Carrier} (Γ : Shape C) (β : C.Arity) :
    (𝟙ʳ : Γ →ʳ Γ) ⇑ʳ β = 𝟙ʳ := by
  ext α p
  cases p with
  | here _  => rfl
  | there _ => rfl

@[simp]
theorem Renaming.extend_comp {C : Carrier} {Γ Δ Ξ : Shape C}
    (f : Γ →ʳ Δ) (g : Δ →ʳ Ξ) (β : C.Arity) : (g ∘ʳʳ f) ⇑ʳ β = (g ⇑ʳ β) ∘ʳʳ (f ⇑ʳ β) := by
  ext α p
  cases p with
  | here _  => rfl
  | there _ => rfl
