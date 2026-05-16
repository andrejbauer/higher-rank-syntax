import HigherRankSyntax.Action.Expr

/-!
# Substitution scaffolding

This file currently holds only the lifting helper `shiftThrough`,
which lifts a slot of a base shape through a list of extensions via
the iterated left-injection of the slot equivalence.

The substitution data structure and the `subst` algorithm are
designed in terms of the relative monad of `Expr` and will be
introduced once the relative-monad lift is set up.
-/

namespace Action

/-- Lift a slot of `base` to a slot of `base ⋈* δ` via the iterated
left-injection of the slot equivalence: each cons of `δ` adds one
layer that the slot passes through on its `γ`-side. -/
def shiftThrough {C : Carrier} (base : C.Shape) :
    (δ : List C.Arity) → C.ShapeSlots base →
    C.ShapeSlots (base ⋈* δ)
  | [], p => p
  | β :: rest, p => Carrier.inlSlot (base ⋈* rest) β (shiftThrough base rest p)

/-- `shiftThrough` preserves the slot's arity: lifting through the
δ-extensions does not change `shapeArity`.

Container view: the slot equivalence is a morphism of decorated
containers, so its left-injection is naturality of the
decoration. -/
theorem shiftThrough_shapeArity {C : Carrier} (base : C.Shape) :
    ∀ (δ : List C.Arity) (p : C.ShapeSlots base),
      C.shapeArity (base ⋈* δ) (shiftThrough base δ p) =
        C.shapeArity base p
  | [], _ => rfl
  | β :: rest, p => by
    show C.shapeArity (Carrier.extList base rest ⋈ β)
           (Carrier.inlSlot (Carrier.extList base rest) β
              (shiftThrough base rest p))
         = C.shapeArity base p
    rw [Carrier.shapeArity_inlSlot]
    exact shiftThrough_shapeArity base rest p

end Action
