import HigherRankSyntax.Action.Carrier

/-!
# Expressions of a higher-rank binding signature

Given a `Carrier`, `Expr γ α` is the type of expressions of arity `α`
in shape `γ`.  Every expression has the form `apply x args` where:

* `x : ShapeSlots γ` is the head — a slot of the ambient shape — and
  fixes the arity of the whole expression to `shapeArity γ x = α`;

* `args` is a dependent family of children, one per binder position
  `y : AritySlots (shapeArity γ x)` of the head's arity.  The child at
  position `y` is itself an expression, living in the shape extended
  by that position's binder (`γ ⋈ arityArity _ y`) and of arity
  `arityArity _ y`.

Container view: `Expr` is the free relative monad of the shape
container `Shape ◅ ShapeSlots` (with `shapeArity` decoration), with
binding handled by the action `⋈`.  The inductive is the W-type of
that decorated container, with each recursive call's shape index
shifted by the action.

Every value of `Expr γ α` is well-formed by construction: an
ill-formed expression cannot be written.  No separate validation
predicate is needed.

Termination of operations on `Expr` (substitution, η-expansion) uses
two well-founded relations:

* The **sub-expression relation** on `Expr` — automatic from the
  inductive structure (`args y` is a structural subterm of
  `apply _ _ args`).
* The **sub-arity relation** on `Arity` — provided by the carrier via
  `Action.Carrier.aritySubWf`, packaged as a `WellFoundedRelation`
  instance.
-/

namespace Action

open scoped Carrier

/-- Expressions of arity `α` in shape `γ`. -/
inductive Expr [Carrier] : Carrier.Shape → Carrier.Arity → Type where
  /-- An application of a head slot `x` of `γ` to a dependent family
      of children, one per binder position of `x`'s arity. -/
  | apply (γ : Carrier.Shape) (x : Carrier.ShapeSlots γ)
      (args : (y : Carrier.AritySlots (Carrier.shapeArity γ x)) →
              Expr (γ ⋈ Carrier.arityArity (Carrier.shapeArity γ x) y)
                   (Carrier.arityArity (Carrier.shapeArity γ x) y)) :
      Expr γ (Carrier.shapeArity γ x)

end Action
