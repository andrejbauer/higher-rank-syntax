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
  induction x using (IsWellFounded.wf (r := r)).induction with
  | h x ih =>
    rcases trichotomous_of s (e x) (f x) with hlt | heq | hgt
    · replace hlt : r (f.symm (e x)) x := by
        apply f.map_rel_iff.mp
        simpa using hlt
      exfalso
      apply irrefl_of s (e x)
      convert (e.map_rel_iff).2 hlt
      · symm
        simpa using ih (f.symm (e x)) hlt
    · exact heq
    · replace hgt : r (e.symm (f x)) x := by
        apply e.map_rel_iff.mp
        simpa using hgt
      exfalso
      apply irrefl_of s (f x)
      convert (f.map_rel_iff).2 hgt
      simpa using ih (e.symm (f x)) hgt

instance : CoeSort WellOrder (Type _) where coe W := W.α

/-- A carrier of a higher-rank binding syntax: the base data from which the framework
builds expressions, renamings, and substitutions. -/
structure Carrier (A : Type) where
  /-- Arities: the binding arities carried by positions. -/
  Arity : Submonoid (Function.End A)
  /-- The positions of an arity. -/
  slotAt : Arity → Arity → WellOrder
  /-- The monoidal unit has no slots. -/
  unit_empty : ∀ α, IsEmpty (slotAt 1 α)
  /-- Slot fibres of products are ordered sums. -/
  slotAt_mul : ∀ Γ Δ α, Sum.Lex (slotAt Γ α).r (slotAt Δ α).r ≃r (slotAt (Γ * Δ) α).r
  subWf : WellFounded (fun Δ Γ => Nonempty (slotAt Γ Δ))

/-- One-step sub-arity relation: `α' ≺ α` when `α'` is the sub-arity of some position of
`α`.  Well-founded by `subWf`. -/
abbrev Carrier.Sub {A : Type} {C : Carrier A} (Δ Γ : C.Arity) : Prop :=
  Nonempty (C.slotAt Γ Δ)

/-- The carrier's sub-arity well-founded relation, packaged as a `WellFoundedRelation`
instance for use in `termination_by`. -/
instance {A : Type} (C : Carrier A) : WellFoundedRelation (C.Arity) where
  rel := Carrier.Sub
  wf := C.subWf

abbrev SlotAt {A : Type} {C : Carrier A} (Γ Δ : C.Arity) : Type :=
  C.slotAt Γ Δ

infix:35 " ∋ " => SlotAt

abbrev Ext {A : Type} {C : Carrier A} (Γ Δ : C.Arity) : C.Arity := Δ * Γ

infixl:65 " ⋈ " => Ext

namespace Carrier

abbrev slotRel {A : Type} (C : Carrier A) (Γ α : C.Arity) :
    Γ ∋ α → Γ ∋ α → Prop :=
  (C.slotAt Γ α).r

def inl {A : Type} (C : Carrier A) {Γ Δ α : C.Arity} (x : Γ ∋ α) :
    Γ * Δ ∋ α :=
  C.slotAt_mul Γ Δ α (Sum.inl x)

def inr {A : Type} (C : Carrier A) {Γ Δ α : C.Arity} (x : Δ ∋ α) :
    Γ * Δ ∋ α :=
  C.slotAt_mul Γ Δ α (Sum.inr x)

def copair {A : Type} (C : Carrier A) (Γ Δ : C.Arity) {α : C.Arity} (X : Type)
    (f : Γ ∋ α → X) (g : Δ ∋ α → X) (p : Γ * Δ ∋ α) : X :=
  Sum.elim f g ((C.slotAt_mul Γ Δ α).symm p)

theorem copair_inl {A : Type} (C : Carrier A) (Γ Δ : C.Arity) {α : C.Arity} (X : Type)
    (f : Γ ∋ α → X) (g : Δ ∋ α → X) :
  C.copair Γ Δ X f g ∘ C.inl = f := by
  funext x
  simp [copair, inl]

theorem copair_inr {A : Type} (C : Carrier A) (Γ Δ : C.Arity) {α : C.Arity} (X : Type)
    (f : Γ ∋ α → X) (g : Δ ∋ α → X) :
  C.copair Γ Δ X f g ∘ C.inr = g := by
  funext x
  simp [copair, inr]

theorem cover
    {A : Type} (C : Carrier A)
    (Γ Δ : C.Arity) {α : C.Arity} (p : Γ * Δ ∋ α) :
  (∃ x : Γ ∋ α, p = C.inl x) ∨ (∃ y : Δ ∋ α, p = C.inr y) := by
  rcases h : (C.slotAt_mul Γ Δ α).symm p with x | y
  · left
    use x
    rw [← (C.slotAt_mul Γ Δ α).apply_symm_apply p, h]
    rfl
  · right
    use y
    rw [← (C.slotAt_mul Γ Δ α).apply_symm_apply p, h]
    rfl

/-- The monoidal unit has no slots. -/
theorem unit_is_empty {A : Type} (C : Carrier A) {α : C.Arity} (x : 1 ∋ α) : False :=
  (C.unit_empty α).false x

theorem inl_rel_iff {A : Type} (C : Carrier A) {Γ Δ α : C.Arity}
    {x y : Γ ∋ α} :
  C.slotRel (Γ * Δ) α (C.inl x) (C.inl y) ↔ C.slotRel Γ α x y := by
  simpa [slotRel, inl] using
    (C.slotAt_mul Γ Δ α).map_rel_iff (a := Sum.inl x) (b := Sum.inl y)

theorem inr_rel_iff {A : Type} (C : Carrier A) {Γ Δ α : C.Arity}
    {x y : Δ ∋ α} :
  C.slotRel (Γ * Δ) α (C.inr x) (C.inr y) ↔ C.slotRel Δ α x y := by
  simpa [slotRel, inr] using
    (C.slotAt_mul Γ Δ α).map_rel_iff (a := Sum.inr x) (b := Sum.inr y)

theorem inl_strictMono {A : Type} (C : Carrier A) {Γ Δ α : C.Arity}
    {x y : Γ ∋ α} (h : C.slotRel Γ α x y) :
  C.slotRel (Γ * Δ) α (C.inl x) (C.inl y) :=
  (C.inl_rel_iff (Γ := Γ) (Δ := Δ) (α := α)).2 h

theorem inr_strictMono {A : Type} (C : Carrier A) {Γ Δ α : C.Arity}
    {x y : Δ ∋ α} (h : C.slotRel Δ α x y) :
  C.slotRel (Γ * Δ) α (C.inr x) (C.inr y) :=
  (C.inr_rel_iff (Γ := Γ) (Δ := Δ) (α := α)).2 h

theorem inl_lt_inr {A : Type} (C : Carrier A) {Γ Δ α : C.Arity}
    (x : Γ ∋ α) (y : Δ ∋ α) :
  C.slotRel (Γ * Δ) α (C.inl x) (C.inr y) :=
  (C.slotAt_mul Γ Δ α).map_rel_iff.2 (Sum.Lex.sep x y)

/-- A product classifier is unique once its two injections agree. -/
theorem copair_uniq {A : Type} (C : Carrier A) (Γ Δ : C.Arity)
    {α : C.Arity} {X : Type} (h k : Γ * Δ ∋ α → X)
    (hinl : h ∘ C.inl = k ∘ C.inl)
    (hinr : h ∘ C.inr = k ∘ C.inr) :
  h = k := by
  funext p
  rcases C.cover Γ Δ p with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact congrFun hinl x
  · exact congrFun hinr y

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

private theorem slotAt_mul_assoc_apply {A : Type} (C : Carrier A)
    (Γ Δ Ξ α : C.Arity)
    (p : Sum (C.slotAt Γ α) (Sum (C.slotAt Δ α) (C.slotAt Ξ α))) :
  slotAt_mul_leftAssoc C Γ Δ Ξ α p = slotAt_mul_rightAssoc C Γ Δ Ξ α p := by
  have hSame : slotAt_mul_leftAssoc C Γ Δ Ξ α = slotAt_mul_rightAssoc C Γ Δ Ξ α := by
    apply relIso_of_wellOrder_eq
  exact congrArg (fun F => F p) hSame

theorem inr_inl {A : Type} (C : Carrier A)
    (Γ Δ Ξ : C.Arity) {α : C.Arity} (x : Δ ∋ α) :
  (C.inr (C.inl x) : Γ * (Δ * Ξ) ∋ α)
    = (C.inl (C.inr x) : (Γ * Δ) * Ξ ∋ α) := by
  simpa only [slotAt_mul_leftAssoc, slotAt_mul_rightAssoc, inl, inr]
    using slotAt_mul_assoc_apply C Γ Δ Ξ α (Sum.inr (Sum.inl x))

theorem inr_inr {A : Type} (C : Carrier A)
    (Γ Δ Ξ : C.Arity) {α : C.Arity} (x : Ξ ∋ α) :
  (C.inr (C.inr x) : Γ * (Δ * Ξ) ∋ α)
    = (C.inr x : (Γ * Δ) * Ξ ∋ α) := by
  simpa only [slotAt_mul_leftAssoc, slotAt_mul_rightAssoc, inl, inr]
    using slotAt_mul_assoc_apply C Γ Δ Ξ α (Sum.inr (Sum.inr x))

theorem inl_inl {A : Type} (C : Carrier A)
    (Γ Δ Ξ : C.Arity) {α : C.Arity} (x : Γ ∋ α) :
  (C.inl x : Γ * (Δ * Ξ) ∋ α)
    = (C.inl (C.inl x) : (Γ * Δ) * Ξ ∋ α) := by
  simpa only [slotAt_mul_leftAssoc, slotAt_mul_rightAssoc, inl, inr]
    using slotAt_mul_assoc_apply C Γ Δ Ξ α (Sum.inl x)

theorem unit_right {A : Type} (C : Carrier A) (Γ : C.Arity)
    {α : C.Arity} (x : Γ ∋ α) :
  (C.inl x : Γ * 1 ∋ α) = x := by
  letI := C.unit_empty α
  let hSame :
      C.slotAt_mul Γ 1 α
        = RelIso.sumLexEmpty (C.slotAt Γ α).r (C.slotAt 1 α).r := by
    apply relIso_of_wellOrder_eq
  replace hSame := congrArg (fun F => F (Sum.inl x)) hSame
  simpa only [inl] using hSame

theorem unit_left {A : Type} (C : Carrier A) (Γ : C.Arity)
    {α : C.Arity} (x : Γ ∋ α) :
  (C.inr x : 1 * Γ ∋ α) = x := by
  letI := C.unit_empty α
  let hSame :
      C.slotAt_mul 1 Γ α
        = RelIso.emptySumLex (C.slotAt 1 α).r (C.slotAt Γ α).r := by
    apply relIso_of_wellOrder_eq
  replace hSame := congrArg (fun F => F (Sum.inr x)) hSame
  simpa only [inr] using hSame

end Carrier
