import HigherRankSyntax.Carrier

/-!
# Paths to nested slots

`SlotPath Δ Φ α` addresses a slot reached from `Δ` by repeatedly entering
binding arities.  `Φ` is the accumulated part preceding the addressed slot and
`α` is its binding arity, so a `SlotPath` is the hereditary counterpart of the
immediate slot relation `Δ ∋ α`.
-/

variable {A : Type} {C : Carrier A}

/-- An address into the recursively nested slots of an arity.

`here x` selects an immediate slot.  `nested x p` enters the binding arity of
`x` and follows `p`. -/
inductive SlotPath : C.Arity → C.Arity → C.Arity → Type where
  /-- An immediate slot. -/
  | here {Δ α : C.Arity} (x : Δ ∋ α) :
      SlotPath Δ (C.before x) α
  /-- A slot nested inside the binding arity of `x`. -/
  | nested {Δ α β Φ : C.Arity} (x : Δ ∋ β) (p : SlotPath β Φ α) :
      SlotPath Δ (C.before x ⋈ Φ) α

/-- The unit arity has no nested slots. -/
theorem SlotPath.unit_elim {Φ α : C.Arity}
    (p : SlotPath (C := C) 1 Φ α) : False := by
  cases p with
  | here x => exact C.unit_is_empty x
  | nested x _ => exact C.unit_is_empty x
