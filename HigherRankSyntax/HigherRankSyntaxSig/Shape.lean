import HigherRankSyntaxSig.Carrier
import HigherRankSyntaxSig.Tele

/-!
# Shapes and slots — telescope representation

`Shape C` is the type of telescopes over `C.Arity`.  The monoid operations
(`⋈*`, with `Shape.nil` as unit) are **strictly associative with a strict
unit at the definitional level** — function composition + `id` give us
`Γ ⋈* Shape.nil ≡ Γ` and `Shape.nil ⋈* Γ ≡ Γ` definitionally.

`SlotAt` is the inductive of slots indexed by Shape; constructors reference
the telescope's structure (`Γ ∘ᵗ Tele.snoc α`).
-/


/-- A shape over a carrier `C`: a telescope. -/
abbrev Shape (C : Carrier) : Type := Tele C.Arity

namespace Shape

/-- The empty shape. -/
@[match_pattern] abbrev nil {C : Carrier} : Shape C := Tele.id

/-- Extension of a shape by an arity. -/
@[match_pattern] abbrev ext {C : Carrier} (Γ : Shape C) (α : C.Arity) : Shape C :=
  Γ ∘ᵗ Tele.snoc α

end Shape

/-- Action of an arity on a shape: extends `Γ` by `α`. -/
infixl:65 " ⋈ " => Shape.ext

/-- Iterated extension of a shape by another shape (telescope composition). -/
abbrev Shape.extList {C : Carrier} (Γ Δ : Shape C) : Shape C := Γ ∘ᵗ Δ

@[inherit_doc Shape.extList]
infixl:67 " ⋈* " => Shape.extList

/-- A slot of a shape with its arity tracked as a type index. -/
inductive SlotAt {C : Carrier} : Shape C → C.Arity → Type where
  /-- A binder introduced by the topmost extension. -/
  | here  : {Γ : Shape C} → {α : C.Arity} → (i : C.Binder α) →
            SlotAt (Γ ⋈ α) i.arity
  /-- A slot inherited from the shape below the topmost extension. -/
  | there : {Γ : Shape C} → {β α : C.Arity} → SlotAt Γ α →
            SlotAt (Γ ⋈ β) α

/-- `Γ ∋ α` is the type of slots of `Γ` at arity `α`. -/
notation:35 Γ " ∋ " α => SlotAt Γ α

/-- Extract the arity index from a slot. -/
@[reducible]
def SlotAt.arity {C : Carrier} {Γ : Shape C} {α : C.Arity} (_ : Γ ∋ α) : C.Arity := α

/-! ### Strict monoid laws (all `rfl`) -/

@[simp] theorem Shape.extList_nil {C : Carrier} (Γ : Shape C) : Γ ⋈* Shape.nil = Γ := rfl

@[simp] theorem Shape.nil_extList {C : Carrier} (Γ : Shape C) : Shape.nil ⋈* Γ = Γ := rfl

@[simp] theorem Shape.extList_assoc {C : Carrier} (Γ Δ Ε : Shape C) :
    (Γ ⋈* Δ) ⋈* Ε = Γ ⋈* (Δ ⋈* Ε) := rfl
