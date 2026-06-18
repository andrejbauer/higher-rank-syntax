import HigherRankSyntax.Carrier
import HigherRankSyntax.Tele

/-!
# Shapes and slots — telescope representation

`Shape C` is `Tele C.Arity` — cons-style telescopes over arities.  The monoid
operations `⋈` (composition) and `Shape.nil` (identity) are **strictly
associative with strict unit at the level of definitional equality**.

Slots are inductive on the underlying list (`Γ.toList`).  Because
`(Tele.cons α ∘ᵗ Γ).toList = α :: Γ.toList` *definitionally*, pattern matching
on slots at shapes of the form `Γ ∷ α` works exactly as if Shape were a List.
-/

/-- A shape over a carrier `C`: a telescope of arities. -/
abbrev Shape (C : Carrier) : Type := Tele C.Arity

namespace Shape

/-- The empty shape. -/
@[match_pattern] abbrev nil {C : Carrier} : Shape C := Tele.id

/-- Extension of a shape by an arity at the topmost layer. -/
@[match_pattern] abbrev ext {C : Carrier} (Γ : Shape C) (α : C.Arity) : Shape C :=
  Tele.cons α ∘ᵗ Γ

end Shape

/-- Action of an arity on a shape: extends `Γ` by `α` at the topmost layer. -/
infixl:65 " ∷ " => Shape.ext

/-- The singleton telescope `⌊α⌋`: the shape consisting of a single
binder of arity `α`. -/
abbrev Shape.singleton {C : Carrier} (α : C.Arity) : Shape C := Shape.nil ∷ α

@[inherit_doc Shape.singleton]
notation:max "⌊" α "⌋" => Shape.singleton α

/-- Iterated extension of a shape by another shape (telescope composition). -/
abbrev Shape.extList {C : Carrier} (Γ Δ : Shape C) : Shape C := Δ ∘ᵗ Γ

@[inherit_doc Shape.extList]
infixl:65 " ⋈ " => Shape.extList

/-- A slot of a list of arities with its arity tracked as a type index.  The
inductive lives on `List`; `SlotAt` on `Shape` is `abbrev`'d to this via the
underlying-list. -/
inductive ListSlotAt {C : Carrier} : List C.Arity → C.Arity → Type where
  /-- A binder introduced by the topmost extension at its binder's arity. -/
  | here  : {β : C.Arity} → {rest : List C.Arity} → (i : C.Binder β) →
            ListSlotAt (β :: rest) i.arity
  /-- A slot inherited from below the topmost extension, at the same arity. -/
  | there : {β α : C.Arity} → {rest : List C.Arity} →
            ListSlotAt rest α → ListSlotAt (β :: rest) α

/-- Slots of a shape are slots of its underlying list. -/
abbrev SlotAt {C : Carrier} (Γ : Shape C) (α : C.Arity) : Type :=
  ListSlotAt Γ.toList α

/-- `Γ ∋ α` is the type of slots of `Γ` at arity `α`. -/
infix:35 " ∋ " => SlotAt

/-- Extract the arity index from a slot. -/
@[reducible]
def SlotAt.arity {C : Carrier} {Γ : Shape C} {α : C.Arity}
    (_ : Γ ∋ α) : C.Arity := α

/-! ### Strict monoid laws (all `rfl`) -/

@[simp] theorem Shape.extList_nil {C : Carrier} (Γ : Shape C) :
    (Γ ⋈ Shape.nil) = Γ := rfl

@[simp] theorem Shape.nil_extList {C : Carrier} (Γ : Shape C) :
    (Shape.nil ⋈ Γ) = Γ := rfl

@[simp] theorem Shape.extList_assoc {C : Carrier} (Γ Δ Ξ : Shape C) :
    ((Γ ⋈ Δ) ⋈ Ξ) = (Γ ⋈ (Δ ⋈ Ξ)) := rfl

/-! ### Underlying-list reduction: `(Γ ∷ α).toList = α :: Γ.toList` -/

@[simp] theorem Shape.ext_toList {C : Carrier} (Γ : Shape C) (α : C.Arity) :
    (Γ ∷ α).toList = α :: Γ.toList := rfl
