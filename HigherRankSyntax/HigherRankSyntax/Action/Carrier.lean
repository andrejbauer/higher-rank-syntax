/-!
# Carrier of a higher-rank binding signature

A `Carrier` packages the signature-level base data of a higher-rank binding syntax: base
context shapes (with their variables and decorations), arities (with their binder positions
and sub-arities), and a well-foundedness assumption on the sub-arity relation.

* **Base shapes.**  `BaseShape`, with variables `BaseShapeSlot γ` and each variable's arity
  given by `baseSlotArity`.

* **Arities.**  `Arity`, with binder positions `AritySlot α` and each binder's sub-arity
  given by `arityArity`.

* **Termination data.**  `aritySubWf` asserts the sub-arity relation
  `arityArity α y = α'` is well-founded.

Shapes, slots, expressions, renamings, and the relative-monad structure are built on top of
this data; see `Action/Shape.lean` and downstream.
-/

namespace Action

/-- A carrier of a higher-rank binding signature: the base data from which the framework
builds shapes, slots, and expressions. -/
structure Carrier where
  /-- Base context shapes. -/
  BaseShape : Type
  /-- Arities: the binder shape carried by each variable. -/
  Arity : Type
  /-- The variables of a base shape. -/
  BaseShapeSlot : BaseShape → Type
  /-- The binder positions of an arity. -/
  AritySlot : Arity → Type
  /-- The arity of each base-shape variable. -/
  baseSlotArity (γ : BaseShape) : BaseShapeSlot γ → Arity
  /-- The arity of each binder position of an arity. -/
  arityArity (α : Arity) : AritySlot α → Arity
  /-- The sub-arity relation `arityArity α y = α'` is well-founded; this is the termination
      data for the recursion that walks under binders. -/
  aritySubWf : WellFounded
    (fun α' α : Arity => ∃ y : AritySlot α, arityArity α y = α')

/-- One-step sub-arity relation: `α' ≺ α` when `α'` is the sub-arity of some binder position
of `α`.  Well-founded by `aritySubWf`. -/
abbrev Carrier.AritySub {C : Carrier} (α' α : C.Arity) : Prop :=
  ∃ y : C.AritySlot α, C.arityArity α y = α'

/-- The carrier's sub-arity well-founded relation, packaged as a `WellFoundedRelation`
instance for use in `termination_by`. -/
instance (C : Carrier) : WellFoundedRelation C.Arity where
  rel := Carrier.AritySub (C := C)
  wf := C.aritySubWf

end Action
