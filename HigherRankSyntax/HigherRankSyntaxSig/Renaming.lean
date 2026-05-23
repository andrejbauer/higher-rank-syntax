import HigherRankSyntaxSig.Shape

/-!
# Renamings of shapes

A *renaming* `Γ →ʳ Δ` is an arity-preserving slot map.

## Notations

  - `Γ →ʳ Δ` is the type of renamings from `Γ` to `Δ`.
  - `𝟙ʳ` is the identity renaming.
  - `g ∘ʳʳ f` is composition "g after f".
  - `Γ ↪ʳ α` and `Γ ↪ʳ* τ` are the canonical weakenings.
  - `ρ ⇑ʳ α` and `ρ ⇑ʳ* τ` extend a renaming through a fresh binder / list of binders.
-/


/-- A renaming of shapes from `Γ` to `Δ`: an arity-preserving slot map. -/
structure Renaming {C : Carrier} (Γ Δ : Shape C) : Type where
  /-- The underlying slot map. -/
  apply : ∀ {α : C.Arity}, (Γ ∋ α) → (Δ ∋ α)

@[inherit_doc Renaming]
infixr:25 " →ʳ " => Renaming

instance {C : Carrier} {Γ Δ : Shape C} :
    CoeFun (Γ →ʳ Δ) (fun _ => ∀ {α : C.Arity}, (Γ ∋ α) → (Δ ∋ α)) :=
  ⟨Renaming.apply⟩

/-- The identity renaming on `Γ`. -/
def Renaming.id {C : Carrier} (Γ : Shape C) : Γ →ʳ Γ :=
  ⟨fun {_} p => p⟩

@[inherit_doc Renaming.id]
notation "𝟙ʳ" => Renaming.id _

/-- Composition of renamings: `comp f g` sends a slot through `f`, then through `g`. -/
def Renaming.comp {C : Carrier} {Γ Δ Ε : Shape C} (f : Γ →ʳ Δ) (g : Δ →ʳ Ε) : Γ →ʳ Ε :=
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

theorem Renaming.comp_assoc {C : Carrier} {Γ Δ Ε Ζ : Shape C}
    (f : Γ →ʳ Δ) (g : Δ →ʳ Ε) (h : Ε →ʳ Ζ) : h ∘ʳʳ (g ∘ʳʳ f) = (h ∘ʳʳ g) ∘ʳʳ f := rfl

/-- The canonical weakening renaming `Γ →ʳ Γ ⋈ α`. -/
def Renaming.weaken {C : Carrier} (Γ : Shape C) (α : C.Arity) : Γ →ʳ Γ ⋈ α :=
  ⟨fun {_} p => .there p⟩

@[inherit_doc Renaming.weaken]
notation:65 Γ " ↪ʳ " α => Renaming.weaken Γ α

/-- Extend a renaming through a fresh binder of arity `β`. -/
def Renaming.extend {C : Carrier} {Γ Δ : Shape C} (f : Γ →ʳ Δ) (β : C.Arity) :
    Γ ⋈ β →ʳ Δ ⋈ β :=
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
theorem Renaming.extend_comp {C : Carrier} {Γ Δ Ε : Shape C}
    (f : Γ →ʳ Δ) (g : Δ →ʳ Ε) (β : C.Arity) : (g ∘ʳʳ f) ⇑ʳ β = (g ⇑ʳ β) ∘ʳʳ (f ⇑ʳ β) := by
  ext α p
  cases p with
  | here _  => rfl
  | there _ => rfl

/-- Iterated weakening: the canonical inclusion `Γ →ʳ Γ ⋈* (Tele.ofList τ)`. -/
def Renaming.weakenList {C : Carrier} (Γ : Shape C) :
    (τ : List C.Arity) → Γ →ʳ Γ ⋈* (Tele.ofList τ)
  | []        => 𝟙ʳ
  | β :: rest => Renaming.weaken (Γ ⋈* (Tele.ofList rest)) β ∘ʳʳ Renaming.weakenList Γ rest

@[inherit_doc Renaming.weakenList]
notation:65 Γ " ↪ʳ* " τ => Renaming.weakenList Γ τ

/-- Iterated extension of a renaming through a list of binders. -/
def Renaming.extendList {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ) :
    (τ : List C.Arity) → Γ ⋈* (Tele.ofList τ) →ʳ Δ ⋈* (Tele.ofList τ)
  | []        => ρ
  | β :: rest => ρ.extendList rest ⇑ʳ β

@[inherit_doc Renaming.extendList]
infixl:95 " ⇑ʳ* " => Renaming.extendList

@[simp] theorem Renaming.extendList_nil {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ) :
    ρ ⇑ʳ* [] = ρ := rfl

@[simp] theorem Renaming.extendList_cons {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ)
    (β : C.Arity) (rest : List C.Arity) :
    ρ ⇑ʳ* (β :: rest) = ρ ⇑ʳ* rest ⇑ʳ β := rfl

@[simp] theorem Renaming.extendList_id {C : Carrier} (Γ : Shape C) :
    ∀ (τ : List C.Arity), (𝟙ʳ : Γ →ʳ Γ) ⇑ʳ* τ = 𝟙ʳ
  | []        => rfl
  | β :: rest => by
    show (𝟙ʳ : Γ →ʳ Γ) ⇑ʳ* rest ⇑ʳ β = 𝟙ʳ
    rw [Renaming.extendList_id Γ rest, Renaming.extend_id]

@[simp] theorem Renaming.extendList_weakenList {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ) :
    ∀ (τ : List C.Arity) {α : C.Arity} (p : Γ ∋ α),
      (ρ ⇑ʳ* τ) ((Γ ↪ʳ* τ) p) = (Δ ↪ʳ* τ) (ρ p)
  | [], _, _ => rfl
  | β :: rest, _, p => by
    show ListSlotAt.there ((ρ ⇑ʳ* rest) ((Γ ↪ʳ* rest) p))
       = ListSlotAt.there ((Δ ↪ʳ* rest) (ρ p))
    rw [Renaming.extendList_weakenList ρ rest p]

theorem Renaming.weakenList_naturality {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ)
    (τ : List C.Arity) :
    ρ ⇑ʳ* τ ∘ʳʳ (Γ ↪ʳ* τ) = (Δ ↪ʳ* τ) ∘ʳʳ ρ := by
  ext α p
  exact Renaming.extendList_weakenList ρ τ p
