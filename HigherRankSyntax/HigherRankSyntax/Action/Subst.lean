import HigherRankSyntax.Action.Expr

/-!
# Substitution

The substitution data structure is the Kleisli morphism of the
relative monad of `Expr`, specialised to a "γ extended by one
binder α" source: a dependent function assigning, to every slot of
the input shape `γ ⋈ α`, an expression of matching arity in the
output shape `γ ⋈* δ`.

This file collects:

* `Substitution C γ α δ` — the Kleisli-morphism type.
* `shiftThrough` — lift a slot of a base shape through a list of
  extensions, via the iterated left-injection of the slot
  equivalence.  The lemma `shiftThrough_shapeArity` records that
  the lift preserves the slot's arity.

The substitution algorithm `subst` and its supporting `classify`
walk are added on top.
-/

namespace Action

open scoped Carrier

/-- A substitution from `γ ⋈ α` to `γ ⋈* δ`: for every slot of the
input shape, an expression of matching arity in the output shape.

This is precisely a Kleisli morphism for the relative monad of
`Expr`, specialised so the source shape has the form `γ ⋈ α`.  The
γ-side slots typically map to themselves (η-expanded as variables
of the output shape), while the α-side slots carry the actual
substitution data — the expressions that replace each binder's
slot. -/
def Substitution (C : Carrier) (γ : C.Shape) (α : C.Arity)
    (δ : List C.Arity) : Type :=
  (s : C.ShapeSlots (γ ⋈ α)) →
    Expr C (γ ⋈* δ) (C.shapeArity (γ ⋈ α) s)

/-- Lift a slot of `base` to a slot of `base ⋈* δ` via the iterated
left-injection of the slot equivalence: each cons of `δ` adds one
layer that the slot passes through on its `γ`-side. -/
def shiftThrough (C : Carrier) (base : C.Shape) :
    (δ : List C.Arity) → C.ShapeSlots base →
    C.ShapeSlots (base ⋈* δ)
  | [], p => p
  | _ :: rest, p =>
    (C.slotsExt _ _).symm (.inl (shiftThrough C base rest p))

/-- `shiftThrough` preserves the slot's arity: lifting through the
δ-extensions does not change `shapeArity`.

Container view: the slot equivalence is a morphism of decorated
containers, so its left-injection is naturality of the
decoration. -/
theorem shiftThrough_shapeArity (C : Carrier) (base : C.Shape) :
    ∀ (δ : List C.Arity) (p : C.ShapeSlots base),
      C.shapeArity (base ⋈* δ) (shiftThrough C base δ p) =
        C.shapeArity base p
  | [], p => rfl
  | β :: rest, p => by
    show C.shapeArity (C.ext (Carrier.extList C base rest) β)
           ((C.slotsExt (Carrier.extList C base rest) β).symm
              (.inl (shiftThrough C base rest p)))
         = C.shapeArity base p
    rw [C.slotsExtCompat]
    simp
    exact shiftThrough_shapeArity C base rest p

end Action
