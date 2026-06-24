
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Data.Sum.Order
import Mathlib.SetTheory.Ordinal.Basic

private def sumLexAssocRel {α β γ : Type}
    (r : α → α → Prop) (s : β → β → Prop) (t : γ → γ → Prop) :
    Sum.Lex (Sum.Lex r s) t ≃r Sum.Lex r (Sum.Lex s t) where
  toEquiv := Equiv.sumAssoc α β γ
  map_rel_iff' := by rintro ((_ | _) | _) ((_ | _) | _) <;> simp

private theorem relIso_of_wellOrder_eq {α β : Type} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (e f : r ≃r s) : e = f := by
  ext x
  refine IsWellFounded.induction (r := r) (motive := fun x => e x = f x) x ?_
  intro x ih
  rcases trichotomous_of s (e x) (f x) with hlt | heq | hgt
  · let y : α := f.symm (e x)
    have hyx : r y x := f.map_rel_iff.mp (by simpa [y] using hlt)
    have hey : e y = f y := ih y hyx
    have hxy : y = x := e.injective (by simpa [y] using hey)
    exact (irrefl_of r x (hxy ▸ hyx)).elim
  · exact heq
  · let y : α := e.symm (f x)
    have hyx : r y x := by
      have herel : s (e y) (e x) ↔ r y x := e.map_rel_iff
      exact herel.mp (by simpa [y] using hgt)
    have hey : e y = f y := ih y hyx
    have hxy : y = x := by
      symm
      apply f.injective
      simpa [y] using hey
    exact (irrefl_of r x (hxy ▸ hyx)).elim

instance : CoeSort WellOrder (Type _) where coe W := W.α

/-- A carrier of a higher-rank binding syntax: the base data from which the framework
builds expressions, renamings, and substitutions. -/
structure Carrier (A : Type) where
  /-- Arities: the binding shape carried by each position. -/
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

theorem cover {A : Type} (C : Carrier A) (Γ Δ : C.Arity) {α : C.Arity}
    (p : Γ * Δ ∋ α) :
    (∃ x : Γ ∋ α, p = C.inl x) ∨ (∃ y : Δ ∋ α, p = C.inr y) := by
  rcases h : (C.slotAt_mul Γ Δ α).symm p with x | y
  · left
    refine ⟨x, ?_⟩
    have hp := (C.slotAt_mul Γ Δ α).apply_symm_apply p
    rw [h] at hp
    simpa [inl] using hp.symm
  · right
    refine ⟨y, ?_⟩
    have hp := (C.slotAt_mul Γ Δ α).apply_symm_apply p
    rw [h] at hp
    simpa [inr] using hp.symm

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
    C.slotRel (Γ * Δ) α (C.inl x) (C.inr y) := by
  exact (C.slotAt_mul Γ Δ α).map_rel_iff.2 (Sum.Lex.sep x y)

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

theorem inr_inl {A : Type} (C : Carrier A)
    (Γ Δ Ξ : C.Arity) {α : C.Arity} (x : Δ ∋ α) :
  (C.inr (C.inl x) : Γ * (Δ * Ξ) ∋ α)
    =
  (C.inl (C.inr x) : (Γ * Δ) * Ξ ∋ α) := by
  let rΓ := (C.slotAt Γ α).r
  let rΔ := (C.slotAt Δ α).r
  let rΞ := (C.slotAt Ξ α).r
  let L : Sum.Lex rΓ (Sum.Lex rΔ rΞ) ≃r (C.slotAt (Γ * (Δ * Ξ)) α).r :=
    (RelIso.sumLexCongr (RelIso.refl rΓ) (C.slotAt_mul Δ Ξ α)).trans
      (C.slotAt_mul Γ (Δ * Ξ) α)
  let R : Sum.Lex rΓ (Sum.Lex rΔ rΞ) ≃r (C.slotAt (Γ * (Δ * Ξ)) α).r :=
    (sumLexAssocRel rΓ rΔ rΞ).symm.trans
      ((RelIso.sumLexCongr (C.slotAt_mul Γ Δ α) (RelIso.refl rΞ)).trans
        (C.slotAt_mul (Γ * Δ) Ξ α))
  have h := relIso_of_wellOrder_eq L R
  change L (Sum.inr (Sum.inl x)) = R (Sum.inr (Sum.inl x))
  rw [h]

theorem inr_inr {A : Type} (C : Carrier A)
    (Γ Δ Ξ : C.Arity) {α : C.Arity} (x : Ξ ∋ α) :
  (C.inr (C.inr x) : Γ * (Δ * Ξ) ∋ α)
    =
  (C.inr x : (Γ * Δ) * Ξ ∋ α) := by
  let rΓ := (C.slotAt Γ α).r
  let rΔ := (C.slotAt Δ α).r
  let rΞ := (C.slotAt Ξ α).r
  let L : Sum.Lex rΓ (Sum.Lex rΔ rΞ) ≃r (C.slotAt (Γ * (Δ * Ξ)) α).r :=
    (RelIso.sumLexCongr (RelIso.refl rΓ) (C.slotAt_mul Δ Ξ α)).trans
      (C.slotAt_mul Γ (Δ * Ξ) α)
  let R : Sum.Lex rΓ (Sum.Lex rΔ rΞ) ≃r (C.slotAt (Γ * (Δ * Ξ)) α).r :=
    (sumLexAssocRel rΓ rΔ rΞ).symm.trans
      ((RelIso.sumLexCongr (C.slotAt_mul Γ Δ α) (RelIso.refl rΞ)).trans
        (C.slotAt_mul (Γ * Δ) Ξ α))
  have h : L = R := relIso_of_wellOrder_eq L R
  change L (Sum.inr (Sum.inr x)) = R (Sum.inr (Sum.inr x))
  rw [h]

theorem inl_inl {A : Type} (C : Carrier A)
    (Γ Δ Ξ : C.Arity) {α : C.Arity} (x : Γ ∋ α) :
  (C.inl x : Γ * (Δ * Ξ) ∋ α)
    =
  (C.inl (C.inl x) : (Γ * Δ) * Ξ ∋ α) := by
  let rΓ := (C.slotAt Γ α).r
  let rΔ := (C.slotAt Δ α).r
  let rΞ := (C.slotAt Ξ α).r
  let L : Sum.Lex rΓ (Sum.Lex rΔ rΞ) ≃r (C.slotAt (Γ * (Δ * Ξ)) α).r :=
    (RelIso.sumLexCongr (RelIso.refl rΓ) (C.slotAt_mul Δ Ξ α)).trans
      (C.slotAt_mul Γ (Δ * Ξ) α)
  let R : Sum.Lex rΓ (Sum.Lex rΔ rΞ) ≃r (C.slotAt (Γ * (Δ * Ξ)) α).r :=
    (sumLexAssocRel rΓ rΔ rΞ).symm.trans
      ((RelIso.sumLexCongr (C.slotAt_mul Γ Δ α) (RelIso.refl rΞ)).trans
        (C.slotAt_mul (Γ * Δ) Ξ α))
  have h : L = R := relIso_of_wellOrder_eq L R
  change L (Sum.inl x) = R (Sum.inl x)
  rw [h]

theorem unit_right {A : Type} (C : Carrier A) (Γ : C.Arity)
    {α : C.Arity} (x : Γ ∋ α) :
  (C.inl x : Γ * 1 ∋ α) = x := by
  change C.slotAt_mul Γ 1 α (Sum.inl x) = x
  letI := C.unit_empty α
  have hIso : C.slotAt_mul Γ 1 α = RelIso.sumLexEmpty (C.slotAt Γ α).r (C.slotAt 1 α).r :=
    relIso_of_wellOrder_eq _ _
  rw [hIso]
  rfl

theorem unit_left {A : Type} (C : Carrier A) (Γ : C.Arity)
    {α : C.Arity} (x : Γ ∋ α) :
  (C.inr x : 1 * Γ ∋ α) = x := by
  change C.slotAt_mul 1 Γ α (Sum.inr x) = x
  letI := C.unit_empty α
  have hIso : C.slotAt_mul 1 Γ α = RelIso.emptySumLex (C.slotAt 1 α).r (C.slotAt Γ α).r :=
    relIso_of_wellOrder_eq _ _
  rw [hIso]
  rfl

end Carrier
