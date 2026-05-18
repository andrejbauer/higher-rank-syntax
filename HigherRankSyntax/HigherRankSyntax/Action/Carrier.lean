/-!
# Carrier of a higher-rank binding signature

A `Carrier` packages the signature-level base data of a higher-rank binding syntax: base
context shapes (with their variables and decorations), arities (with their binders and
sub-arities), and a well-foundedness assumption on the sub-arity relation.

* **Base shapes.**  `BaseShape`, with variables `Var γ` and each variable's arity given
  by `varArity` (accessible as `x.arity` via `Carrier.Var.arity`).

* **Arities.**  `Arity`, with binders `Binder α` and each binder's sub-arity given by
  `binderArity` (accessible as `i.arity` via `Carrier.Binder.arity`).

* **Termination data.**  `subWf` asserts the sub-arity relation is well-founded.

Shapes, slots, expressions, renamings, and the relative-monad structure are built on top
of this data; see `Action/Shape.lean` and downstream.
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
  Var : BaseShape → Type
  /-- The binders of an arity. -/
  Binder : Arity → Type
  /-- The arity of each base-shape variable. -/
  varArity (γ : BaseShape) : Var γ → Arity
  /-- The sub-arity of each binder of an arity. -/
  binderArity (α : Arity) : Binder α → Arity
  /-- The sub-arity relation `i.arity = α'` is well-founded; this is the termination
      data for the recursion that walks under binders. -/
  subWf : WellFounded
    (fun α' α : Arity => ∃ i : Binder α, binderArity α i = α')

/-- Dot-notation alias: `x.arity` for a base-shape variable. -/
def Carrier.Var.arity {C : Carrier} {γ : C.BaseShape} (x : C.Var γ) : C.Arity :=
  C.varArity γ x

/-- Dot-notation alias: `i.arity` for a binder. -/
def Carrier.Binder.arity {C : Carrier} {α : C.Arity} (i : C.Binder α) : C.Arity :=
  C.binderArity α i

/-- One-step sub-arity relation: `α' ≺ α` when `α'` is the sub-arity of some binder of
`α`.  Well-founded by `subWf`. -/
abbrev Carrier.Sub {C : Carrier} (α' α : C.Arity) : Prop :=
  ∃ i : C.Binder α, i.arity = α'

/-- The carrier's sub-arity well-founded relation, packaged as a `WellFoundedRelation`
instance for use in `termination_by`. -/
instance (C : Carrier) : WellFoundedRelation C.Arity where
  rel := Carrier.Sub (C := C)
  wf := C.subWf

end Action
