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
  ∀ ⦃Φ α : C.Arity⦄, SlotPath (C := C) Δ Φ α → Bd (Ω ⋈ Φ ⋈ α)

namespace Decoration

/-- The boundary attached to an immediate slot. -/
def boundary {Ω Δ α : C.Arity} (D : Decoration Ω Δ) (x : Δ ∋ α) :
    Bd (Ω ⋈ C.before x ⋈ α) :=
  D (.here x)

/-- The decoration of a slot's binding arity. -/
def nested {Ω Δ α : C.Arity} (D : Decoration Ω Δ) (x : Δ ∋ α) :
    Decoration (Ω ⋈ C.before x) α :=
  fun ⦃_⦄ ⦃_⦄ p => D (.nested x p)

/-- Restrict a decoration to the slots of the first factor. -/
def restrict {Ω Γ Δ : C.Arity} (D : Decoration Ω (Γ ⋈ Δ)) : Decoration Ω Γ :=
  fun ⦃_⦄ ⦃_⦄ p => D p.inl

/-- Transport a decoration along an equality of the decorated arity. -/
def castArity {Ω Γ Δ : C.Arity} (h : Γ = Δ) (D : Decoration Ω Γ) : Decoration Ω Δ :=
  h ▸ D

/-- The decoration making every slot a sort. -/
def allSort (Ω Δ : C.Arity) : Decoration Ω Δ :=
  fun ⦃_⦄ ⦃_⦄ _ => .sort

@[simp] theorem boundary_allSort {Ω Δ α : C.Arity} (x : Δ ∋ α) :
  (allSort Ω Δ).boundary x = .sort := rfl

@[simp] theorem nested_allSort {Ω Δ α : C.Arity} (x : Δ ∋ α) :
  (allSort Ω Δ).nested x = allSort (Ω ⋈ C.before x) α := rfl

end Decoration

/-- An arity equipped with a decoration over the base `Ω`. -/
structure dTel (Ω : C.Arity) where
  /-- The underlying arity. -/
  arity : C.Arity
  /-- The boundaries of its slots. -/
  decoration : Decoration Ω arity

/-- An ambient: a decorated telescope over the unit base. -/
abbrev Ambient (C : Carrier A) : Type := dTel (C := C) 1

namespace dTel

variable {Ω Λ : C.Arity}

/-- The entries preceding a slot, decorated as they are in the whole. -/
def before (Θ : dTel Ω) (z : Θ.arity ∋ Λ) : dTel Ω where
  arity := C.before z
  decoration := Decoration.restrict (Decoration.castArity (C.factor z).symm Θ.decoration)

/-- The entries a slot binds, over the base extended by the entries preceding it. -/
def binding (Θ : dTel Ω) (z : Θ.arity ∋ Λ) : dTel (Ω ⋈ (Θ.before z).arity) where
  arity := Λ
  decoration := Θ.decoration.nested z

/-- What a slot is declared to be, over the base, the entries preceding it, and
the entries it binds. -/
def boundary (Θ : dTel Ω) (z : Θ.arity ∋ Λ) :
    Bd (Ω ⋈ (Θ.before z).arity ⋈ (Θ.binding z).arity) :=
  Θ.decoration.boundary z

/-- The renaming taking the entries preceding a slot into the whole. -/
def inclusion (Θ : dTel Ω) (z : Θ.arity ∋ Λ) :
    Ω ⋈ (Θ.before z).arity →ʳ Ω ⋈ Θ.arity :=
  Renaming.prefixed Ω (C.inclusion z)

/-- Restricting to the entries preceding `z` and then to those preceding `w` is
restricting to those preceding `w` in the whole. -/
theorem before_before (Θ : dTel Ω) (z : Θ.arity ∋ Λ) {β : C.Arity}
    (w : (Θ.before z).arity ∋ β) :
  (Θ.before z).before w = Θ.before (C.inclusion z w) := sorry

/-- Restriction leaves the entries a slot binds. -/
theorem binding_before (Θ : dTel Ω) (z : Θ.arity ∋ Λ) {β : C.Arity}
    (w : (Θ.before z).arity ∋ β) :
  HEq ((Θ.before z).binding w) (Θ.binding (C.inclusion z w)) := sorry

/-- Restriction leaves what a slot is declared to be. -/
theorem boundary_before (Θ : dTel Ω) (z : Θ.arity ∋ Λ) {β : C.Arity}
    (w : (Θ.before z).arity ∋ β) :
  HEq ((Θ.before z).boundary w) (Θ.boundary (C.inclusion z w)) := sorry

@[simp] theorem arity_before (Θ : dTel Ω) (z : Θ.arity ∋ Λ) :
  (Θ.before z).arity = C.before z := rfl

@[simp] theorem arity_binding (Θ : dTel Ω) (z : Θ.arity ∋ Λ) :
  (Θ.binding z).arity = Λ := rfl

end dTel

section SmokeTests

/-- An immediate slot is decorated over the base, the part preceding it, and its
own binding arity. -/
example (Ω Δ α : C.Arity) (D : Decoration Ω Δ) (x : Δ ∋ α) :
    Bd (Ω ⋈ C.before x ⋈ α) :=
  D (.here x)

/-- A once-nested slot accumulates both preceding parts. -/
example (Ω Δ α β : C.Arity) (D : Decoration Ω Δ) (x : Δ ∋ β) (y : β ∋ α) :
    Bd (Ω ⋈ (C.before x ⋈ C.before y) ⋈ α) :=
  D (.nested x (.here y))

/-- The three projections of a slot, each over the base extended by the arities of
the previous ones. -/
example (Ω : C.Arity) (Θ : dTel Ω) {Λ : C.Arity} (z : Θ.arity ∋ Λ) :
    dTel Ω × dTel (Ω ⋈ (Θ.before z).arity)
      × Bd (Ω ⋈ (Θ.before z).arity ⋈ (Θ.binding z).arity) :=
  (Θ.before z, Θ.binding z, Θ.boundary z)

/-- Entering a binding arity and taking a boundary is taking the nested boundary. -/
example (Ω Δ α β : C.Arity) (D : Decoration Ω Δ) (x : Δ ∋ β) (y : β ∋ α) :
    (D.nested x).boundary y = D (.nested x (.here y)) :=
  rfl

end SmokeTests
