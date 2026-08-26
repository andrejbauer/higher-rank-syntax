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
  slotAt_mul :
    ∀ Γ Δ α, Sum.Lex (slotAt Γ α).r (slotAt Δ α).r
      ≃r (slotAt (Γ * Δ) α).r
  subWf : WellFounded (fun Δ Γ => Nonempty (slotAt Γ Δ))
  /-- The part of an arity preceding a slot. -/
  before : {Δ α : Arity} → slotAt Δ α → Arity
  /-- The part of an arity from a slot onwards. -/
  after : {Δ α : Arity} → slotAt Δ α → Arity
  /-- A slot splits its arity. -/
  factor : {Δ α : Arity} → (x : slotAt Δ α) → before x * after x = Δ
  /-- A slot occurs in the second factor of its own splitting. -/
  localized : {Δ α : Arity} → (x : slotAt Δ α) → slotAt (after x) α
  /-- The localized slot is the slot. -/
  reinject : {Δ α : Arity} → (x : slotAt Δ α) →
    factor x ▸ slotAt_mul (before x) (after x) α (Sum.inr (localized x)) = x
  /-- Precedence of a left-injected slot ignores the extension. -/
  before_inl : {Γ Δ α : Arity} → (x : slotAt Γ α) →
    before (slotAt_mul Γ Δ α (Sum.inl x)) = before x
  /-- The remainder of a left-injected slot absorbs the extension. -/
  after_inl : {Γ Δ α : Arity} → (x : slotAt Γ α) →
    after (slotAt_mul Γ Δ α (Sum.inl x)) = after x * Δ
  /-- Precedence of a right-injected slot absorbs the base. -/
  before_inr : {Γ Δ α : Arity} → (x : slotAt Δ α) →
    before (slotAt_mul Γ Δ α (Sum.inr x)) = Γ * before x
  /-- The remainder of a right-injected slot ignores the base. -/
  after_inr : {Γ Δ α : Arity} → (x : slotAt Δ α) →
    after (slotAt_mul Γ Δ α (Sum.inr x)) = after x
  /-- A slot below `y` in its fibre lies in the part preceding `y`. -/
  before_of_lt : {Δ α : Arity} → {x y : slotAt Δ α} → (slotAt Δ α).r x y →
    ∃ x' : slotAt (before y) α,
      factor y ▸ slotAt_mul (before y) (after y) α (Sum.inl x') = x

/-- One-step sub-arity relation: `α' ≺ α` when `α'` is the sub-arity of some
position of `α`.  Well-founded by `subWf`. -/
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

abbrev Ext {A : Type} {C : Carrier A} (Γ Δ : C.Arity) : C.Arity := Γ * Δ

infixl:65 " ⋈ " => Ext

namespace Carrier

universe u

abbrev slotRel {A : Type} (C : Carrier A) (Γ α : C.Arity) :
    Γ ∋ α → Γ ∋ α → Prop :=
  (C.slotAt Γ α).r

def inl {A : Type} (C : Carrier A) {Γ Δ α : C.Arity} (x : Γ ∋ α) :
    Γ * Δ ∋ α :=
  C.slotAt_mul Γ Δ α (Sum.inl x)

def inr {A : Type} (C : Carrier A) {Γ Δ α : C.Arity} (x : Δ ∋ α) :
    Γ * Δ ∋ α :=
  C.slotAt_mul Γ Δ α (Sum.inr x)

@[simp] theorem slotAt_mul_symm_inr {A : Type} (C : Carrier A)
    {Γ Δ α : C.Arity} (x : Δ ∋ α) :
    (C.slotAt_mul Γ Δ α).symm (C.inr x) = Sum.inr x := by
  exact (C.slotAt_mul Γ Δ α).symm_apply_apply (Sum.inr x)

/-- The inclusion of the part of an arity preceding a slot. -/
def inclusion {A : Type} (C : Carrier A) {Δ α : C.Arity} (x : Δ ∋ α) :
    ∀ ⦃β : C.Arity⦄, C.before x ∋ β → Δ ∋ β :=
  fun ⦃_⦄ y => C.factor x ▸ C.inl y

/-- The localized slot is the slot. -/
theorem reinject_inr {A : Type} (C : Carrier A) {Δ α : C.Arity} (x : Δ ∋ α) :
  C.factor x ▸ (C.inr (C.localized x) : C.before x ⋈ C.after x ∋ α) = x :=
  C.reinject x

/-- Transporting a slot along an equality of arities leaves its precedence. -/
theorem before_cast {A : Type} (C : Carrier A) {Γ Δ α : C.Arity} (h : Γ = Δ)
    (x : Γ ∋ α) :
  C.before (h ▸ x) = C.before x := by
  subst h
  rfl

/-- Precedence inside the part preceding a slot agrees with precedence in the
whole. -/
theorem before_inclusion {A : Type} (C : Carrier A) {Δ α β : C.Arity}
    (y : Δ ∋ α) (x : C.before y ∋ β) :
  C.before (C.inclusion y x) = C.before x := by
  rw [Carrier.inclusion, C.before_cast, Carrier.inl]
  exact C.before_inl x

/-- Including from the part preceding `x`'s slot into the part preceding `y`, and
then into the whole, is including directly. -/
theorem inclusion_inclusion {A : Type} (C : Carrier A) {Δ α β γ : C.Arity}
    (y : Δ ∋ α) (w : C.before y ∋ β) (x : C.before w ∋ γ) :
  C.inclusion y (C.inclusion w x)
    = C.inclusion (C.inclusion y w) ((C.before_inclusion y w).symm ▸ x) := by
  unfold Carrier.inclusion
  sorry

/-- A slot below `y` in its fibre is the inclusion of a slot of `before y`. -/
theorem before_of_slotRel {A : Type} (C : Carrier A) {Δ α : C.Arity}
    {x y : Δ ∋ α} (h : C.slotRel Δ α x y) :
  ∃ x' : C.before y ∋ α, C.inclusion y x' = x :=
  C.before_of_lt h

def copair {A : Type} (C : Carrier A) (Γ Δ : C.Arity) {α : C.Arity}
    (X : Type) (f : Γ ∋ α → X) (g : Δ ∋ α → X) (p : Γ * Δ ∋ α) :
    X :=
  Sum.elim f g ((C.slotAt_mul Γ Δ α).symm p)

theorem copair_inl {A : Type} (C : Carrier A) (Γ Δ : C.Arity) {α : C.Arity}
    (X : Type) (f : Γ ∋ α → X) (g : Δ ∋ α → X) :
  C.copair Γ Δ X f g ∘ C.inl = f := by
  funext x
  simp [copair, inl]

theorem copair_inr {A : Type} (C : Carrier A) (Γ Δ : C.Arity) {α : C.Arity}
    (X : Type) (f : Γ ∋ α → X) (g : Δ ∋ α → X) :
  C.copair Γ Δ X f g ∘ C.inr = g := by
  funext x
  simp [copair, inr]

@[simp] theorem copair_apply_inl {A : Type} (C : Carrier A)
    (Γ Δ : C.Arity) {α : C.Arity}
    (X : Type) (f : Γ ∋ α → X) (g : Δ ∋ α → X)
    (x : Γ ∋ α) :
    C.copair Γ Δ X f g (C.inl x) = f x :=
  congrFun (C.copair_inl Γ Δ X f g) x

@[simp] theorem copair_apply_inr {A : Type} (C : Carrier A)
    (Γ Δ : C.Arity) {α : C.Arity}
    (X : Type) (f : Γ ∋ α → X) (g : Δ ∋ α → X)
    (x : Δ ∋ α) :
    C.copair Γ Δ X f g (C.inr x) = g x :=
  congrFun (C.copair_inr Γ Δ X f g) x

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

/-- Eliminate a product slot, retaining its equality with the chosen injection. -/
def coverCasesEq
    {A : Type} (C : Carrier A)
    (Γ Δ : C.Arity) {α : C.Arity}
    {motive : (p : Γ * Δ ∋ α) → Sort u}
    (p : Γ * Δ ∋ α)
    (left : (x : Γ ∋ α) → (p = C.inl x) → motive p)
    (right : (y : Δ ∋ α) → (p = C.inr y) → motive p) : motive p := by
  rcases h : (C.slotAt_mul Γ Δ α).symm p with x | y
  · apply left x
    rw [← (C.slotAt_mul Γ Δ α).apply_symm_apply p, h]
    rfl
  · apply right y
    rw [← (C.slotAt_mul Γ Δ α).apply_symm_apply p, h]
    rfl

/-- The monoidal unit has no slots. -/
theorem unit_is_empty {A : Type} (C : Carrier A) {α : C.Arity}
    (x : 1 ∋ α) : False :=
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
  C.inl_rel_iff.2 h

theorem inr_strictMono {A : Type} (C : Carrier A) {Γ Δ α : C.Arity}
    {x y : Δ ∋ α} (h : C.slotRel Δ α x y) :
  C.slotRel (Γ * Δ) α (C.inr x) (C.inr y) :=
  C.inr_rel_iff.2 h

theorem inl_lt_inr {A : Type} (C : Carrier A) {Γ Δ α : C.Arity}
    (x : Γ ∋ α) (y : Δ ∋ α) :
  C.slotRel (Γ * Δ) α (C.inl x) (C.inr y) :=
  (C.slotAt_mul Γ Δ α).map_rel_iff.2 (Sum.Lex.sep x y)

private theorem slotRel_cast {A : Type} (C : Carrier A) {Λ Δ α : C.Arity}
    (h : Λ = Δ) (u v : Λ ∋ α) :
  C.slotRel Δ α (h ▸ u) (h ▸ v) ↔ C.slotRel Λ α u v := by
  cases h
  rfl

/-- Everything preceding a slot is below it in the slot's fibre. -/
theorem inclusion_lt {A : Type} (C : Carrier A) {Δ α : C.Arity}
    (y : Δ ∋ α) (x : C.before y ∋ α) :
  C.slotRel Δ α (C.inclusion y x) y := by
  have key := (slotRel_cast C (C.factor y) (C.inl x)
      (C.slotAt_mul (C.before y) (C.after y) α (Sum.inr (C.localized y)))).2
    (C.inl_lt_inr x (C.localized y))
  rwa [C.reinject y] at key

/-- A product classifier is unique once its two injections agree. -/
theorem copair_uniq {A : Type} (C : Carrier A) (Γ Δ : C.Arity)
    {α : C.Arity} {X : Type} (h k : Γ * Δ ∋ α → X)
    (hinl : h ∘ C.inl = k ∘ C.inl) (hinr : h ∘ C.inr = k ∘ C.inr) :
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
