import HigherRankSyntaxSig.Carrier

/-!
# Shapes and slots

A `Shape C` is a list of arities.  The empty shape is `Shape.nil = []`; one-step
extension `Shape.ext Γ α = α :: Γ` puts the newest arity at the head of the list.

* `SlotAt Γ α` is the slots of `Γ` at arity `α`: `.here i` for a binder introduced at
  this `ext` layer, `.there p` for a slot inherited from the shape below.
-/


/-- A shape over a carrier `C`: a list of arities. -/
abbrev Shape (C : Carrier) : Type := List C.Arity

namespace Shape

/-- The empty shape. -/
@[match_pattern] abbrev nil {C : Carrier} : Shape C := []

/-- Extension of a shape by an arity at the topmost layer. -/
@[match_pattern] abbrev ext {C : Carrier} (Γ : Shape C) (α : C.Arity) : Shape C := α :: Γ

end Shape

/-- Action of an arity on a shape: extends `Γ` by `α` at the topmost layer. -/
infixl:65 " ⋈ " => Shape.ext

/-- Iterated extension of a shape by a list of arities, cons-as-snoc: the head of the
list is the outermost extension.  `Γ ⋈* (β :: rest) = (Γ ⋈* rest) ⋈ β` and
`Γ ⋈* [] = Γ`. -/
abbrev Shape.extList {C : Carrier} (Γ : Shape C) (τ : List C.Arity) : Shape C := τ ++ Γ

/-- Iterated extension of a shape by a list of arities. -/
infixl:67 " ⋈* " => Shape.extList

/-- A slot of a shape with its arity tracked as a type index: a fresh binder of the
topmost extension (`.here i` at `i.arity`), or a slot inherited from the shape below
the topmost extension (`.there p` at the same arity as `p`). -/
inductive SlotAt {C : Carrier} : Shape C → C.Arity → Type where
  /-- A binder introduced by the topmost extension at its binder's arity. -/
  | here  : {Γ : Shape C} → {α : C.Arity} → (i : C.Binder α) → SlotAt (Γ ⋈ α) i.arity
  /-- A slot inherited from the shape below the topmost extension, at the same arity. -/
  | there : {Γ : Shape C} → {β α : C.Arity} → SlotAt Γ α → SlotAt (Γ ⋈ β) α

/-- `Γ ∋ α` is the type of slots of `Γ` at arity `α`. -/
notation:35 Γ " ∋ " α => SlotAt Γ α

/-- Extract the arity index from a slot. -/
@[reducible]
def SlotAt.arity {C : Carrier} {Γ : Shape C} {α : C.Arity} (_ : Γ ∋ α) : C.Arity := α

@[simp] theorem Shape.extList_nil {C : Carrier} (Γ : Shape C) : Γ ⋈* [] = Γ := rfl

@[simp] theorem Shape.extList_cons {C : Carrier} (Γ : Shape C) (β : C.Arity)
    (rest : List C.Arity) : Γ ⋈* (β :: rest) = (Γ ⋈* rest) ⋈ β := rfl

/-- Associativity of iterated extension w.r.t. list append. -/
theorem Shape.extList_append {C : Carrier} (Γ : Shape C) (xs ys : List C.Arity) :
    (Γ ⋈* ys) ⋈* xs = Γ ⋈* (xs ++ ys) :=
  (List.append_assoc xs ys Γ).symm

/-- Embed a slot of `dom` into `pre ⋈* dom` by viewing `pre` as the shape below `dom`.
Structural: same `.here`/`.there` constructors at the same depths. -/
def SlotAt.appendRight {C : Carrier} (pre : Shape C) :
    {dom : Shape C} → {α : C.Arity} → (dom ∋ α) → (pre ⋈* dom) ∋ α
  | _, _, SlotAt.here i  => SlotAt.here i
  | _, _, SlotAt.there p => SlotAt.there (SlotAt.appendRight pre p)
