import HigherRankSyntax.Expr

/-!
# Decorations of raw telescopes

This file contains the foundational data of the T1 layer.  A classifier policy
`bd` says, for each coarse class, whether its slots need a classifier and in
which coarse class that classifier is written.  A precedence structure splits
the ambient arity at each slot, so a classifier may use the external base, all
earlier sibling slots, and the variables bound locally by that slot, but not any
later sibling.

A decoration assigns such a raw classifier expression to every immediate and
recursively nested slot of an arity.  A decorated telescope packages the raw
arity with this assignment over an external base; a decorated signature is the
special case over the empty base.  For `bd ty = none` and `bd tm = some ty`, the
telescope `A : Type, x : A` has a trivial decoration at `A` and decorates `x`
with the raw expression naming the preceding slot `A`.

These are classification annotations only.  A decoration does not assert that
the classifier is well formed, that the classified slot inhabits it, or that
the surrounding context is valid.  Those proof-irrelevant judgments belong to
the deferred T2 layer.
-/

variable {A : Type} {C : Carrier A}

/-- A coherent choice of the part of an arity preceding each slot. -/
class Precedence (C : Carrier A) where
  before : {Δ α : C.Arity} → {τ : C.Ty} → Δ ∋[τ] α → C.Arity
  after : {Δ α : C.Arity} → {τ : C.Ty} → Δ ∋[τ] α → C.Arity
  factor : {Δ α : C.Arity} → {τ : C.Ty} →
    (x : Δ ∋[τ] α) → before x ⋈ after x = Δ
  localized : {Δ α : C.Arity} → {τ : C.Ty} →
    (x : Δ ∋[τ] α) → after x ∋[τ] α
  reinject : {Δ α : C.Arity} → {τ : C.Ty} →
    (x : Δ ∋[τ] α) → factor x ▸ C.inr (localized x) = x
  before_inl : {Γ Δ α : C.Arity} → {τ : C.Ty} → (x : Γ ∋[τ] α) →
    before (C.inl x : Γ ⋈ Δ ∋[τ] α) = before x
  after_inl : {Γ Δ α : C.Arity} → {τ : C.Ty} → (x : Γ ∋[τ] α) →
    after (C.inl x : Γ ⋈ Δ ∋[τ] α) = after x ⋈ Δ
  before_inr : {Γ Δ α : C.Arity} → {τ : C.Ty} → (x : Δ ∋[τ] α) →
    before (C.inr x : Γ ⋈ Δ ∋[τ] α) = Γ ⋈ before x
  after_inr : {Γ Δ α : C.Arity} → {τ : C.Ty} → (x : Δ ∋[τ] α) →
    after (C.inr x : Γ ⋈ Δ ∋[τ] α) = after x

/-- The classifier data attached to a raw `τ`-slot over `Ω`.

If `bd τ = none`, the slot has no classifier and carries the unique `PUnit`
value.  If `bd τ = some υ`, it carries an expression in `Expr Ω υ`.  For
`bd ty = none` and `bd tm = some ty`, the telescope `A : Type, x : A`
therefore decorates `A` by `PUnit.unit` and `x` by the preceding type
expression `A`.
-/
def ClassifierAt (bd : C.Ty → Option C.Ty) (Ω : C.Arity) (τ : C.Ty) : Type :=
  match bd τ with
  | none => PUnit
  | some υ => Expr Ω υ

namespace ClassifierAt

variable {bd : C.Ty → Option C.Ty}

/-- Transport a classifier along an equality of raw contexts. -/
def cast {Γ Δ : C.Arity} (h : Γ = Δ) {τ : C.Ty} :
    ClassifierAt bd Γ τ → ClassifierAt bd Δ τ :=
  h ▸ fun a => a

theorem cast_injective {Γ Δ : C.Arity} (h : Γ = Δ) {τ : C.Ty} :
    Function.Injective (cast (bd := bd) h (τ := τ)) := by
  subst Δ
  intro a b hab
  exact hab

theorem cast_comp {Γ Δ Ξ : C.Arity} (h : Γ = Δ) (k : Δ = Ξ)
    {τ : C.Ty} (a : ClassifierAt bd Γ τ) :
    cast k (cast h a) = cast (h.trans k) a := by
  subst Δ
  subst Ξ
  rfl

theorem cast_proof_irrel {Γ Δ : C.Arity} (h k : Γ = Δ)
    {τ : C.Ty} (a : ClassifierAt bd Γ τ) :
    cast h a = cast k a := by
  have hk : h = k := Subsingleton.elim _ _
  subst k
  rfl

theorem cast_eq_cast_comp {Γ Δ Ξ : C.Arity} (h : Γ = Ξ)
    (k : Γ = Δ) (l : Δ = Ξ) {τ : C.Ty}
    (a : ClassifierAt bd Γ τ) :
    cast h a = cast l (cast k a) := by
  subst Δ
  subst Ξ
  rfl

end ClassifierAt

/-- A typed address into the recursively nested slots of a telescope.

`here x` selects an immediate slot.  `nested x p` enters the binding arity of
`x` and follows `p`.  The indices retain the prefix in which the selected
slot's classifier is written.
-/
inductive DecorationPath [P : Precedence C] :
    C.Arity → C.Arity → C.Arity → C.Ty → Type where
  | here {Δ α : C.Arity} {τ : C.Ty} (x : Δ ∋[τ] α) :
      DecorationPath Δ (P.before x) α τ
  | nested {Δ α β Φ : C.Arity} {τ υ : C.Ty}
      (x : Δ ∋[υ] β) (p : DecorationPath β Φ α τ) :
      DecorationPath Δ (P.before x ⋈ Φ) α τ

/-- A decoration assigns a classifier to every recursively nested slot. -/
abbrev Decoration [Precedence C] (bd : C.Ty → Option C.Ty)
    (Ω Δ : C.Arity) : Type :=
  ∀ ⦃Φ α : C.Arity⦄ ⦃τ : C.Ty⦄,
    DecorationPath (C := C) Δ Φ α τ → ClassifierAt bd (Ω ⋈ Φ ⋈ α) τ

namespace Decoration

variable [P : Precedence C] {bd : C.Ty → Option C.Ty}

/-- The classifier attached to an immediate slot. -/
def classifier {Ω Δ α : C.Arity} {τ : C.Ty}
    (D : Decoration bd Ω Δ) (x : Δ ∋[τ] α) :
    ClassifierAt bd (Ω ⋈ P.before x ⋈ α) τ :=
  D (.here x)

/-- The decoration of a slot's binding arity. -/
def nested {Ω Δ α : C.Arity} {τ : C.Ty}
    (D : Decoration bd Ω Δ) (x : Δ ∋[τ] α) :
    Decoration bd (Ω ⋈ P.before x) α :=
  fun ⦃_⦄ ⦃_⦄ ⦃_⦄ p => D (.nested x p)

end Decoration

/-- A raw signature equipped with a decoration over the empty base. -/
structure DecoratedSignature [Precedence C] (bd : C.Ty → Option C.Ty) where
  arity : C.Arity
  decoration : Decoration bd 1 arity

/-- A raw telescope equipped with a decoration over `Ω`. -/
structure DecoratedTelescope [Precedence C] (bd : C.Ty → Option C.Ty)
    (Ω : C.Arity) where
  arity : C.Arity
  decoration : Decoration bd Ω arity
