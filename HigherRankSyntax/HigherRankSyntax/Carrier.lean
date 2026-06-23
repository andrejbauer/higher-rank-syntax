/-!
# Carrier of a higher-rank binding syntax

A `Carrier` packages the signature-level base data of a higher-rank binding syntax:
arities (with their positions and sub-arities) and a well-foundedness assumption on the
sub-arity relation.

* **Arities.**  `Arity`, with positions `Position α` and each position's sub-arity given by
  `positionArity` (accessible as `i.arity` via `Carrier.Position.arity`).  Positions are the
  binding positions opened by an arity.

* **Termination data.**  `subWf` asserts the sub-arity relation is well-founded; the
  recursion that descends under positions decreases along it.

Expressions, renamings, and the relative-monad structure are built on top of this data.
-/


/-- A carrier of a higher-rank binding syntax: the base data from which the framework
builds expressions, renamings, and substitutions. -/
structure Carrier where
  /-- Arities: the binding shape carried by each position. -/
  Arity : Type
  /-- The positions of an arity. -/
  Position : Arity → Type
  /-- The sub-arity of each position. -/
  positionArity (α : Arity) : Position α → Arity
  /-- The sub-arity relation `i.arity = α'` is well-founded; this is the termination
      data for the recursion that descends under positions. -/
  subWf : WellFounded
    (fun α' α : Arity => ∃ i : Position α, positionArity α i = α')

/-- Dot-notation alias: `i.arity` for a position. -/
def Carrier.Position.arity {C : Carrier} {α : C.Arity} (i : C.Position α) : C.Arity :=
  C.positionArity α i

/-- One-step sub-arity relation: `α' ≺ α` when `α'` is the sub-arity of some position of
`α`.  Well-founded by `subWf`. -/
abbrev Carrier.Sub {C : Carrier} (α' α : C.Arity) : Prop :=
  ∃ i : C.Position α, i.arity = α'

/-- The carrier's sub-arity well-founded relation, packaged as a `WellFoundedRelation`
instance for use in `termination_by`. -/
instance (C : Carrier) : WellFoundedRelation C.Arity where
  rel := Carrier.Sub (C := C)
  wf := C.subWf
