/-!
# Carrier of a higher-rank binding syntax

A `Carrier` packages the signature-level base data of a higher-rank binding syntax:
arities (with their binders and sub-arities) and a well-foundedness assumption on the
sub-arity relation.

* **Arities.**  `Arity`, with binders `Binder α` and each binder's sub-arity given by
  `binderArity` (accessible as `i.arity` via `Carrier.Binder.arity`).  Binders are the
  binding positions opened by an arity.

* **Termination data.**  `subWf` asserts the sub-arity relation is well-founded; the
  recursion that descends under binders decreases along it.

Expressions, renamings, and the relative-monad structure are built on top of this data.
-/


/-- A carrier of a higher-rank binding syntax: the base data from which the framework
builds expressions, renamings, and substitutions. -/
structure Carrier where
  /-- Arities: the binding shape carried by each binder. -/
  Arity : Type
  /-- The binders of an arity. -/
  Binder : Arity → Type
  /-- The sub-arity of each binder. -/
  binderArity (α : Arity) : Binder α → Arity
  /-- The sub-arity relation `i.arity = α'` is well-founded; this is the termination
      data for the recursion that descends under binders. -/
  subWf : WellFounded
    (fun α' α : Arity => ∃ i : Binder α, binderArity α i = α')

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
