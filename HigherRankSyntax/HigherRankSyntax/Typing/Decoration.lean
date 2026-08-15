import HigherRankSyntax.SlotPath
import HigherRankSyntax.Typing.Boundary

/-!
# Decorations

A decoration assigns a boundary to every immediate and recursively nested slot
of an arity.  The boundary of a slot is written over the external base, the part
of the arity preceding that slot, and the slot's own binding arity, so it may
name a declared symbol, an earlier sibling, or a variable the slot itself binds.

A decorated telescope packages an arity with such an assignment over a base; a
theory is the case of the unit base.

A decoration is an annotation.  It does not assert that a boundary is a
well-formed sort, that the decorated slot inhabits it, or that the telescope is
a valid context.
-/

variable {A : Type} {C : Carrier A}

/-- A decoration assigns a boundary to every recursively nested slot. -/
abbrev Decoration (Ω Δ : C.Arity) : Type :=
  ∀ ⦃Φ α : C.Arity⦄, SlotPath (C := C) Δ Φ α → Boundary (Ω ⋈ Φ ⋈ α)

namespace Decoration

/-- The boundary attached to an immediate slot. -/
def boundary {Ω Δ α : C.Arity} (D : Decoration Ω Δ) (x : Δ ∋ α) :
    Boundary (Ω ⋈ C.before x ⋈ α) :=
  D (.here x)

/-- The decoration of a slot's binding arity. -/
def nested {Ω Δ α : C.Arity} (D : Decoration Ω Δ) (x : Δ ∋ α) :
    Decoration (Ω ⋈ C.before x) α :=
  fun ⦃_⦄ ⦃_⦄ p => D (.nested x p)

/-- The decoration making every slot a sort. -/
def allSort (Ω Δ : C.Arity) : Decoration Ω Δ :=
  fun ⦃_⦄ ⦃_⦄ _ => .sort

@[simp] theorem boundary_allSort {Ω Δ α : C.Arity} (x : Δ ∋ α) :
  (allSort Ω Δ).boundary x = .sort := rfl

@[simp] theorem nested_allSort {Ω Δ α : C.Arity} (x : Δ ∋ α) :
  (allSort Ω Δ).nested x = allSort (Ω ⋈ C.before x) α := rfl

end Decoration

/-- An arity equipped with a decoration over the base `Ω`. -/
structure DecoratedTelescope (Ω : C.Arity) where
  /-- The underlying arity. -/
  arity : C.Arity
  /-- The boundaries of its slots. -/
  decoration : Decoration Ω arity

/-- A theory: a decorated telescope over the unit base. -/
abbrev Theory (C : Carrier A) : Type := DecoratedTelescope (C := C) 1

section SmokeTests

/-- An immediate slot is decorated over the base, the part preceding it, and its
own binding arity. -/
example (Ω Δ α : C.Arity) (D : Decoration Ω Δ) (x : Δ ∋ α) :
    Boundary (Ω ⋈ C.before x ⋈ α) :=
  D (.here x)

/-- A once-nested slot accumulates both preceding parts. -/
example (Ω Δ α β : C.Arity) (D : Decoration Ω Δ) (x : Δ ∋ β) (y : β ∋ α) :
    Boundary (Ω ⋈ (C.before x ⋈ C.before y) ⋈ α) :=
  D (.nested x (.here y))

/-- Entering a binding arity and taking a boundary is taking the nested boundary. -/
example (Ω Δ α β : C.Arity) (D : Decoration Ω Δ) (x : Δ ∋ β) (y : β ∋ α) :
    (D.nested x).boundary y = D (.nested x (.here y)) :=
  rfl

end SmokeTests
