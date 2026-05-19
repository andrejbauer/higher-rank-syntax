import HigherRankSyntax.Action.Shape

/-!
# Renamings of shapes

A *renaming* `Γ →ʳ Δ` is an arity-respecting slot map: a function `Slot Γ → Slot Δ` that
sends each slot to a slot of the same arity.  Renamings are the morphisms of the Shape
category in the relative-monad picture.

Arities form a discrete category, so no separate notion of renaming on arities is needed.

## Notations

  - `Γ →ʳ Δ` is the type of renamings from `Γ` to `Δ`.
  - `𝟙ʳ` is the identity renaming.
  - `g ∘ʳ f` is the composition; the textual order reverses `Renaming.comp` so it reads
    "g after f", matching the mathematical `g ∘ f`.

The `ʳ` suffix is consistently on the right.
-/

namespace Action

/-- A renaming of shapes from `Γ` to `Δ`: an arity-respecting slot map. -/
structure Renaming {C : Carrier} (Γ Δ : Shape C) : Type where
  /-- The underlying slot map. -/
  toFun : Slot Γ → Slot Δ
  /-- Each slot's image has the same arity as the slot itself. -/
  arity : ∀ (p : Slot Γ), (toFun p).arity = p.arity

/-- Notation `Γ →ʳ Δ` for renamings from `Γ` to `Δ`. -/
scoped infixr:25 " →ʳ " => Renaming

instance {C : Carrier} {Γ Δ : Shape C} :
    CoeFun (Γ →ʳ Δ) (fun _ => Slot Γ → Slot Δ) :=
  ⟨Renaming.toFun⟩

/-- The identity renaming on `Γ`. -/
def Renaming.id {C : Carrier} (Γ : Shape C) : Γ →ʳ Γ where
  toFun p := p
  arity _ := rfl

/-- The identity renaming on a shape. -/
scoped notation "𝟙ʳ" => Renaming.id _

/-- Composition of renamings: `comp f g` sends a slot through `f`, then through `g`. -/
def Renaming.comp {C : Carrier} {Γ Δ Ε : Shape C} (f : Γ →ʳ Δ) (g : Δ →ʳ Ε) : Γ →ʳ Ε where
  toFun p := g (f p)
  arity p := (g.arity (f p)).trans (f.arity p)

/-- `g ∘ʳ f` is the composition "g after f" (= `Renaming.comp f g`). -/
scoped notation:90 g:90 " ∘ʳ " f:91 => Renaming.comp f g

/-- Two renamings are equal when their underlying slot maps agree pointwise.  Their
arity-preservation proofs are propositions and agree by proof irrelevance. -/
@[ext]
theorem Renaming.ext {C : Carrier} {Γ Δ : Shape C} {f g : Γ →ʳ Δ}
    (h : ∀ (p : Slot Γ), f p = g p) : f = g := by
  cases f
  cases g
  congr
  funext p
  exact h p

/-! ## Category laws -/

theorem Renaming.id_comp {C : Carrier} {Γ Δ : Shape C} (f : Γ →ʳ Δ) : f ∘ʳ 𝟙ʳ = f := by
  ext; rfl

theorem Renaming.comp_id {C : Carrier} {Γ Δ : Shape C} (f : Γ →ʳ Δ) : 𝟙ʳ ∘ʳ f = f := by
  ext; rfl

theorem Renaming.comp_assoc {C : Carrier} {Γ Δ Ε Ζ : Shape C}
    (f : Γ →ʳ Δ) (g : Δ →ʳ Ε) (h : Ε →ʳ Ζ) : h ∘ʳ (g ∘ʳ f) = (h ∘ʳ g) ∘ʳ f := by
  ext; rfl

/-! ## Weakening and extension -/

/-- The canonical weakening renaming `Γ →ʳ Γ ⋈ α`: every slot of `Γ` is sent to its image
under `.there`. -/
def Renaming.weaken {C : Carrier} (Γ : Shape C) (α : C.Arity) : Γ →ʳ Γ ⋈ α where
  toFun p := .there p
  arity _ := rfl

/-- Extend a renaming through a fresh binder of arity `β`.  `f.extend β : Γ ⋈ β →ʳ Δ ⋈ β`
acts as the identity on the `.here` binders and as `f` on the `.there` slots. -/
def Renaming.extend {C : Carrier} {Γ Δ : Shape C} (f : Γ →ʳ Δ) (β : C.Arity) :
    Γ ⋈ β →ʳ Δ ⋈ β where
  toFun := fun
    | .here i  => .here i
    | .there p => .there (f p)
  arity := fun
    | .here _  => rfl
    | .there p => f.arity p

/-- `f ⇑ʳ β` is `f` extended through a fresh binder of arity `β`. -/
scoped infixl:95 " ⇑ʳ " => Renaming.extend

@[simp]
theorem Renaming.extend_id {C : Carrier} (Γ : Shape C) (β : C.Arity) :
    (𝟙ʳ : Γ →ʳ Γ) ⇑ʳ β = 𝟙ʳ := by
  ext p
  cases p with
  | here _  => rfl
  | there _ => rfl

@[simp]
theorem Renaming.extend_comp {C : Carrier} {Γ Δ Ε : Shape C}
    (f : Γ →ʳ Δ) (g : Δ →ʳ Ε) (β : C.Arity) : (g ∘ʳ f) ⇑ʳ β = (g ⇑ʳ β) ∘ʳ (f ⇑ʳ β) := by
  ext p
  cases p with
  | here _  => rfl
  | there _ => rfl

/-- Iterated weakening: the canonical inclusion `Γ →ʳ Γ ⋈* τ`, built by recursion on `τ`.
Empty `τ` gives the identity; cons extends the previous weakening through one more binder. -/
def Renaming.weakenList {C : Carrier} (Γ : Shape C) :
    (τ : List C.Arity) → Γ →ʳ Γ ⋈* τ
  | []        => 𝟙ʳ
  | β :: rest => Renaming.weaken (Γ ⋈* rest) β ∘ʳ Renaming.weakenList Γ rest

@[inherit_doc Renaming.weakenList]
scoped notation:65 Γ " ↪ʳ " τ => Renaming.weakenList Γ τ

/-- Iterated extension of a renaming through a list of binders. -/
def Renaming.extendList {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ) :
    (τ : List C.Arity) → Γ ⋈* τ →ʳ Δ ⋈* τ
  | []        => ρ
  | β :: rest => ρ.extendList rest ⇑ʳ β

@[simp] theorem Renaming.extendList_nil {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ) :
    ρ.extendList [] = ρ := rfl

@[simp] theorem Renaming.extendList_cons {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ)
    (β : C.Arity) (rest : List C.Arity) :
    ρ.extendList (β :: rest) = ρ.extendList rest ⇑ʳ β := rfl

@[simp] theorem Renaming.extendList_id {C : Carrier} (Γ : Shape C) :
    ∀ (τ : List C.Arity), (𝟙ʳ : Γ →ʳ Γ).extendList τ = 𝟙ʳ
  | []        => rfl
  | β :: rest => by
    show (𝟙ʳ : Γ →ʳ Γ).extendList rest ⇑ʳ β = 𝟙ʳ
    rw [Renaming.extendList_id Γ rest, Renaming.extend_id]

/-- Naturality of `extendList` w.r.t. `weakenList`: extending a renaming and then
weakening through `τ` equals weakening first then applying the renaming. -/
@[simp] theorem Renaming.extendList_weakenList {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ) :
    ∀ (τ : List C.Arity) (p : Slot Γ),
      ρ.extendList τ ((Γ ↪ʳ τ) p) = (Δ ↪ʳ τ) (ρ p)
  | [], _ => rfl
  | β :: rest, p => by
    show Slot.there (ρ.extendList rest ((Γ ↪ʳ rest) p))
       = Slot.there ((Δ ↪ʳ rest) (ρ p))
    rw [Renaming.extendList_weakenList ρ rest p]

end Action
