import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Data.Sum.Order
import Mathlib.SetTheory.Ordinal.Basic

private def sumLexAssocRel {α β γ : Type}
    (r : α → α → Prop) (s : β → β → Prop) (t : γ → γ → Prop) :
    Sum.Lex (Sum.Lex r s) t ≃r Sum.Lex r (Sum.Lex s t) where
  toEquiv := Equiv.sumAssoc α β γ
  map_rel_iff' := by rintro ((_ | _) | _) ((_ | _) | _) <;> simp

private theorem relIso_of_wellOrder_eq
    {α β : Type} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (e f : r ≃r s) :
  e = f
  := by
  ext x
  apply InitialSeg.eq e.toInitialSeg f.toInitialSeg

instance : CoeSort WellOrder (Type _) where coe W := W.α

/-- A carrier of higher-rank binding syntax: a submonoid `Arity` of `Function.End A` and,
for arities `Γ` and `α`, a well-ordered set `slotAt Γ α` of slots of `Γ` of arity `α`,
such that `1` has no slots, the slots of a product are the lexicographic sum of the
slots of its factors, and "`Γ` has a slot of arity `Δ`" is well-founded; each slot `x`
of `Δ` factors `Δ` as `before x * after x`. -/
structure Carrier (A : Type) where
  /-- The arities. -/
  Arity : Submonoid (Function.End A)
  /-- `slotAt Γ α`: the slots of `Γ` of arity `α`, well-ordered. -/
  slotAt : Arity → Arity → WellOrder
  /-- The unit arity has no slots. -/
  unit_empty : ∀ α, IsEmpty (slotAt 1 α)
  /-- The slots of `Γ * Δ` of arity `α` are order-isomorphic to the lexicographic sum of
  those of `Γ` and of `Δ`. -/
  slotAt_mul :
    ∀ Γ Δ α, Sum.Lex (slotAt Γ α).r (slotAt Δ α).r
      ≃r (slotAt (Γ * Δ) α).r
  /-- The relation "`Γ` has a slot of arity `Δ`" is well-founded. -/
  subWf : WellFounded (fun Δ Γ => Nonempty (slotAt Γ Δ))
  /-- The part of an arity preceding a slot. -/
  before : {Δ α : Arity} → slotAt Δ α → Arity
  /-- The part of an arity from a slot onwards. -/
  after : {Δ α : Arity} → slotAt Δ α → Arity
  /-- An arity is the product of its parts before and after any of its slots. -/
  factor : {Δ α : Arity} → (x : slotAt Δ α) → before x * after x = Δ
  /-- A slot `x` as a slot of `after x`. -/
  localized : {Δ α : Arity} → (x : slotAt Δ α) → slotAt (after x) α
  /-- Transported along `factor x`, the right injection of `localized x` into
  `before x * after x` is `x`. -/
  reinject : {Δ α : Arity} → (x : slotAt Δ α) →
    factor x ▸ slotAt_mul (before x) (after x) α (Sum.inr (localized x)) = x
  /-- The part of `Γ * Δ` before the left injection of `x` is the part of `Γ` before `x`. -/
  before_inl : {Γ Δ α : Arity} → (x : slotAt Γ α) →
    before (slotAt_mul Γ Δ α (Sum.inl x)) = before x
  /-- The part of `Γ * Δ` after the left injection of `x` is `after x * Δ`. -/
  after_inl : {Γ Δ α : Arity} → (x : slotAt Γ α) →
    after (slotAt_mul Γ Δ α (Sum.inl x)) = after x * Δ
  /-- The part of `Γ * Δ` before the right injection of `x` is `Γ * before x`. -/
  before_inr : {Γ Δ α : Arity} → (x : slotAt Δ α) →
    before (slotAt_mul Γ Δ α (Sum.inr x)) = Γ * before x
  /-- The part of `Γ * Δ` after the right injection of `x` is the part of `Δ` after `x`. -/
  after_inr : {Γ Δ α : Arity} → (x : slotAt Δ α) →
    after (slotAt_mul Γ Δ α (Sum.inr x)) = after x
  /-- A slot `x` below `y` is, transported along `factor y`, the left injection of a
  slot of `before y`. -/
  before_of_lt : {Δ α : Arity} → {x y : slotAt Δ α} → (slotAt Δ α).r x y →
    ∃ x' : slotAt (before y) α,
      factor y ▸ slotAt_mul (before y) (after y) α (Sum.inl x') = x

/-- `Sub Δ Γ`: `Γ` has a slot of arity `Δ`. -/
abbrev Carrier.Sub {A : Type} {C : Carrier A} (Δ Γ : C.Arity) : Prop :=
  Nonempty (C.slotAt Γ Δ)

/-- Arities are well-founded under `Carrier.Sub`. -/
instance {A : Type} (C : Carrier A) : WellFoundedRelation (C.Arity) where
  rel := Carrier.Sub
  wf := C.subWf

/-- `Γ ∋ α`: the slots of `Γ` of arity `α`. -/
abbrev SlotAt {A : Type} {C : Carrier A} (Γ Δ : C.Arity) : Type :=
  C.slotAt Γ Δ

infix:35 " ∋ " => SlotAt

/-- `Γ ⋈ Δ`: the product `Γ * Δ` of arities. -/
abbrev Ext {A : Type} {C : Carrier A} (Γ Δ : C.Arity) : C.Arity := Γ * Δ

infixl:65 " ⋈ " => Ext

namespace Carrier

/-- The left injection `Γ ∋ α → Γ * Δ ∋ α`. -/
def inl {A : Type} (C : Carrier A) {Γ Δ α : C.Arity} (x : Γ ∋ α) :
    Γ * Δ ∋ α :=
  C.slotAt_mul Γ Δ α (Sum.inl x)

/-- The right injection `Δ ∋ α → Γ * Δ ∋ α`. -/
def inr {A : Type} (C : Carrier A) {Γ Δ α : C.Arity} (x : Δ ∋ α) :
    Γ * Δ ∋ α :=
  C.slotAt_mul Γ Δ α (Sum.inr x)

/-- The map out of `Γ * Δ ∋ α` given by `f` on left-injected and `g` on
right-injected slots. -/
def copair {A : Type} (C : Carrier A) (Γ Δ : C.Arity) {α : C.Arity}
    (X : Type) (f : Γ ∋ α → X) (g : Δ ∋ α → X) (p : Γ * Δ ∋ α) :
    X :=
  Sum.elim f g ((C.slotAt_mul Γ Δ α).symm p)

theorem copair_inl
    {A : Type} (C : Carrier A) (Γ Δ : C.Arity) {α : C.Arity}
    (X : Type) (f : Γ ∋ α → X) (g : Δ ∋ α → X) :
  C.copair Γ Δ X f g ∘ C.inl = f
  := by
  funext x
  simp [copair, inl]

theorem copair_inr
    {A : Type} (C : Carrier A) (Γ Δ : C.Arity) {α : C.Arity}
    (X : Type) (f : Γ ∋ α → X) (g : Δ ∋ α → X) :
  C.copair Γ Δ X f g ∘ C.inr = g
  := by
  funext x
  simp [copair, inr]

@[simp]
theorem copair_apply_inl
    {A : Type} (C : Carrier A) (Γ Δ : C.Arity) {α : C.Arity}
    (X : Type) (f : Γ ∋ α → X) (g : Δ ∋ α → X) (x : Γ ∋ α) :
  C.copair Γ Δ X f g (C.inl x) = f x
  := congrFun (C.copair_inl Γ Δ X f g) x

@[simp]
theorem copair_apply_inr
    {A : Type} (C : Carrier A) (Γ Δ : C.Arity) {α : C.Arity}
    (X : Type) (f : Γ ∋ α → X) (g : Δ ∋ α → X) (x : Δ ∋ α) :
  C.copair Γ Δ X f g (C.inr x) = g x
  := congrFun (C.copair_inr Γ Δ X f g) x

/-- A slot of `Γ * Δ` as a slot of `Γ` or a slot of `Δ`. -/
def split {A : Type} (C : Carrier A) (Γ Δ : C.Arity) {α : C.Arity}
    (x : Γ * Δ ∋ α) : (Γ ∋ α) ⊕ (Δ ∋ α) :=
  (C.slotAt_mul Γ Δ α).symm x

@[simp]
theorem split_inl {A : Type} (C : Carrier A) {Γ Δ α : C.Arity} (x : Γ ∋ α) :
  C.split Γ Δ (C.inl x) = .inl x
  := by
  simp [split, inl]

@[simp]
theorem split_inr {A : Type} (C : Carrier A) {Γ Δ α : C.Arity} (x : Δ ∋ α) :
  C.split Γ Δ (C.inr x) = .inr x
  := by
  simp [split, inr]

/-- Every slot of `Γ * Δ` is a left- or a right-injected slot. -/
theorem cover
    {A : Type} (C : Carrier A)
    (Γ Δ : C.Arity) {α : C.Arity} (p : Γ * Δ ∋ α) :
  (∃ x : Γ ∋ α, p = C.inl x) ∨ (∃ y : Δ ∋ α, p = C.inr y)
  := by
  obtain ⟨x | y, rfl⟩ := (C.slotAt_mul Γ Δ α).surjective p
  · left
    use x
    rfl
  · right
    use y
    rfl

/-- The unit arity has no slots. -/
theorem unit_is_empty {A : Type} (C : Carrier A) {α : C.Arity} (x : 1 ∋ α) :
  False
  := (C.unit_empty α).false x

private def slotAt_mul_leftAssoc {A : Type} (C : Carrier A)
    (Γ Δ Ξ α : C.Arity) :
  Sum.Lex (C.slotAt Γ α).r (Sum.Lex (C.slotAt Δ α).r (C.slotAt Ξ α).r)
    ≃r (C.slotAt (Γ * (Δ * Ξ)) α).r := by
  apply RelIso.trans
  · apply RelIso.sumLexCongr
    · apply RelIso.refl
    · apply C.slotAt_mul
  · apply C.slotAt_mul

private def slotAt_mul_rightAssoc {A : Type} (C : Carrier A)
    (Γ Δ Ξ α : C.Arity) :
  Sum.Lex (C.slotAt Γ α).r (Sum.Lex (C.slotAt Δ α).r (C.slotAt Ξ α).r)
    ≃r (C.slotAt (Γ * (Δ * Ξ)) α).r := by
  apply RelIso.trans
  · apply RelIso.symm
    apply sumLexAssocRel
  · apply RelIso.trans
    · apply RelIso.sumLexCongr
      · apply C.slotAt_mul
      · apply RelIso.refl
    · apply C.slotAt_mul

private theorem slotAt_mul_assoc_apply
    {A : Type} (C : Carrier A) (Γ Δ Ξ α : C.Arity)
    (p : Sum (C.slotAt Γ α) (Sum (C.slotAt Δ α) (C.slotAt Ξ α))) :
  slotAt_mul_leftAssoc C Γ Δ Ξ α p = slotAt_mul_rightAssoc C Γ Δ Ξ α p
  := by
  apply DFunLike.congr_fun
  apply relIso_of_wellOrder_eq

theorem inr_inl
    {A : Type} (C : Carrier A) (Γ Δ Ξ : C.Arity) {α : C.Arity} (x : Δ ∋ α) :
  (C.inr (C.inl x) : Γ * (Δ * Ξ) ∋ α) = (C.inl (C.inr x) : (Γ * Δ) * Ξ ∋ α)
  := by
  simpa only [slotAt_mul_leftAssoc, slotAt_mul_rightAssoc, inl, inr]
    using slotAt_mul_assoc_apply C Γ Δ Ξ α (Sum.inr (Sum.inl x))

theorem inr_inr
    {A : Type} (C : Carrier A) (Γ Δ Ξ : C.Arity) {α : C.Arity} (x : Ξ ∋ α) :
  (C.inr (C.inr x) : Γ * (Δ * Ξ) ∋ α) = (C.inr x : (Γ * Δ) * Ξ ∋ α)
  := by
  simpa only [slotAt_mul_leftAssoc, slotAt_mul_rightAssoc, inl, inr]
    using slotAt_mul_assoc_apply C Γ Δ Ξ α (Sum.inr (Sum.inr x))

theorem inl_inl
    {A : Type} (C : Carrier A) (Γ Δ Ξ : C.Arity) {α : C.Arity} (x : Γ ∋ α) :
  (C.inl x : Γ * (Δ * Ξ) ∋ α) = (C.inl (C.inl x) : (Γ * Δ) * Ξ ∋ α)
  := by
  simpa only [slotAt_mul_leftAssoc, slotAt_mul_rightAssoc, inl, inr]
    using slotAt_mul_assoc_apply C Γ Δ Ξ α (Sum.inl x)

theorem unit_right
    {A : Type} (C : Carrier A) (Γ : C.Arity) {α : C.Arity} (x : Γ ∋ α) :
  (C.inl x : Γ * 1 ∋ α) = x
  := by
  have := C.unit_empty α
  rw [inl, relIso_of_wellOrder_eq (C.slotAt_mul Γ 1 α) (RelIso.sumLexEmpty _ _)]
  rfl

theorem unit_left
    {A : Type} (C : Carrier A) (Γ : C.Arity) {α : C.Arity} (x : Γ ∋ α) :
  (C.inr x : 1 * Γ ∋ α) = x
  := by
  have := C.unit_empty α
  rw [inr, relIso_of_wellOrder_eq (C.slotAt_mul 1 Γ α) (RelIso.emptySumLex _ _)]
  rfl

end Carrier
