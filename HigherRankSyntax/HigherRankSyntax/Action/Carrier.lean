import Mathlib.Logic.Equiv.Defs
import Batteries.Data.Sum.Basic

/-!
# Carrier of a higher-rank binding signature

A `Carrier` packages **two indexed containers** (in the sense of
Abbott–Altenkirch–Ghani) coupled by an action that describe a
higher-rank binding signature:

* The **shape container** `Shape ◅ ShapeSlots` decorated by
  `shapeArity` fixes the contexts in which expressions live, together
  with the arity of every variable inhabiting such a context.

* The **arity container** `Arity ◅ AritySlots` decorated by
  `arityArity` fixes the internal binder structure of an arity: each
  binder position of an arity is itself an arity — the arity of the
  variable bound there.

The two containers share the same position-decoration type, namely
`Arity`, which is what couples them.

On top of the two containers sits the **action**
`ext : Shape → Arity → Shape`, written `γ ⋈ α`, which extends a
context by all the binders introduced by an arity.  The action is
presented through a slot-equivalence

```
ShapeSlots (γ ⋈ α) ≃ ShapeSlots γ ⊕ AritySlots α
```

together with a single compatibility law saying that the decoration
of the extended container is the copair (along that equivalence) of
the two original decorations — a γ-slot keeps its original arity, and
an α-binder carries its sub-arity.
-/

namespace Action

/-- A carrier of a higher-rank binding signature: two indexed
containers, coupled by an action on shapes. -/
structure Carrier where
  /-- Shapes are the contexts in which expressions live. -/
  Shape : Type
  /-- Arities describe the binder structure of a variable. -/
  Arity : Type
  /-- The variable positions inside a shape. -/
  ShapeSlots : Shape → Type
  /-- The binder positions inside an arity. -/
  AritySlots : Arity → Type
  /-- Decoration of the shape container: the arity of the variable
      at a given slot. -/
  shapeArity (γ : Shape) : ShapeSlots γ → Arity
  /-- Decoration of the arity container: the arity of the variable
      bound at a given binder position. -/
  arityArity (α : Arity) : AritySlots α → Arity
  /-- One-step descent through `arityArity` is well-founded.  This
      is the termination assumption for the arity W-type: every
      chain `α ▷ arityArity α y₀ ▷ arityArity _ y₁ ▷ …` terminates. -/
  aritySubWf : WellFounded
    (fun α' α : Arity => ∃ y : AritySlots α, arityArity α y = α')
  /-- The action of an arity on a shape: extend `γ` by all the
      binders introduced by `α`. -/
  ext : Shape → Arity → Shape
  /-- The slots of `γ ⋈ α` split into the slots of `γ` and the
      binder positions of `α`. -/
  slotsExt (γ : Shape) (α : Arity) :
    ShapeSlots (ext γ α) ≃ ShapeSlots γ ⊕ AritySlots α
  /-- The decoration of the extended container is the copair (along
      `slotsExt`) of the two original decorations: a γ-slot keeps
      its original arity, a binder position of `α` carries its
      sub-arity. -/
  slotsExtCompat (γ : Shape) (α : Arity) (s : ShapeSlots (ext γ α)) :
    shapeArity (ext γ α) s =
      Sum.elim (shapeArity γ) (arityArity α) (slotsExt γ α s)

namespace Carrier

/-- Action of an arity on a shape.  The carrier is left implicit
and is inferred from the type of `γ`. -/
scoped infixl:65 " ⋈ " => Carrier.ext _

/-- Iterated action of a list of arities on a shape, in
**cons-as-snoc** order: the head of the list is the **outermost**
extension, applied last.  Concretely,
`γ ⋈* (α :: rest) = (γ ⋈* rest) ⋈ α`.

This convention makes the recursive step of the substitution
algorithm definitional: going under a binder of arity `β` prepends
`β` to the running list `τ`, and the resulting shape
`γ ⋈* (β :: τ)` reduces by `rfl` to `(γ ⋈* τ) ⋈ β`. -/
def extList {C : Carrier} (γ : C.Shape) : List C.Arity → C.Shape
  | [] => γ
  | α :: rest => C.ext (extList γ rest) α

scoped infixl:67 " ⋈* " => Carrier.extList

@[simp] theorem extList_nil {C : Carrier} (γ : C.Shape) :
    extList (C := C) γ [] = γ := rfl

@[simp] theorem extList_cons {C : Carrier} (γ : C.Shape)
    (α : C.Arity) (rest : List C.Arity) :
    extList γ (α :: rest) = C.ext (extList γ rest) α := rfl

/-- One-step sub-arity relation: `α' ≺ α` when `α'` is the sub-arity
attached to some binder position of `α`.  Termination of the
substitution and η-expansion algorithms descends along this
relation; the carrier asserts it is well-founded via `aritySubWf`. -/
abbrev AritySub {C : Carrier} (α' α : C.Arity) : Prop :=
  ∃ y : C.AritySlots α, C.arityArity α y = α'

/-- The carrier's sub-arity well-founded relation, packaged as a
`WellFoundedRelation` instance.  Instance resolution can locate it
when the underlying `C` is known from context. -/
instance (C : Carrier) : WellFoundedRelation C.Arity where
  rel := AritySub (C := C)
  wf := C.aritySubWf

end Carrier

end Action
