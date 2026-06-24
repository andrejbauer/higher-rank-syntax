
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.SetTheory.Ordinal.Basic

namespace OrdinalSlot

def rank {o : Ordinal} (x : o.ToType) : Ordinal :=
  (Ordinal.typein (fun x y : o.ToType => x < y)).toRelEmbedding x

theorem ext {o : Ordinal} {x y : o.ToType} (h : rank x = rank y) : x = y := by
  exact Ordinal.typein_injective (fun x y : o.ToType => x < y) h

theorem rank_lt_iff {o : Ordinal} {x y : o.ToType} :
    rank x < rank y ↔ x < y := by
  exact (Ordinal.typein (fun x y : o.ToType => x < y)).toRelEmbedding.map_rel_iff

theorem rank_lt {o : Ordinal} {x y : o.ToType} (h : x < y) : rank x < rank y :=
  rank_lt_iff.mpr h

theorem lt_of_rank_lt {o : Ordinal} {x y : o.ToType} (h : rank x < rank y) : x < y :=
  rank_lt_iff.mp h

end OrdinalSlot

/-- A carrier of a higher-rank binding syntax: the base data from which the framework
builds expressions, renamings, and substitutions. -/
structure Carrier (A : Type) where
  /-- Arities: the binding shape carried by each position. -/
  Arity : Submonoid (Function.End A)
  /-- The positions of an arity. -/
  slotAt : Arity → Arity → Ordinal
  /-- The monoidal unit has no slots. -/
  unit_empty : ∀ α, slotAt 1 α = 0
  /-- Slot fibres of products are ordinal sums. -/
  slotAt_mul : ∀ Γ Δ α, slotAt (Γ * Δ) α = slotAt Γ α + slotAt Δ α
  inl : ∀ {Γ Δ α} , (slotAt Γ α).ToType → (slotAt (Γ * Δ) α).ToType
  inl_strictMono : ∀ {Γ Δ α}, StrictMono (inl (Γ := Γ) (Δ := Δ) (α := α))
  inl_rank : ∀ {Γ Δ α} (x : (slotAt Γ α).ToType),
    OrdinalSlot.rank (inl (Δ := Δ) x) = OrdinalSlot.rank x
  inr : ∀ {Γ Δ α} , (slotAt Δ α).ToType → (slotAt (Γ * Δ) α).ToType
  inr_strictMono : ∀ {Γ Δ α}, StrictMono (inr (Γ := Γ) (Δ := Δ) (α := α))
  inr_rank : ∀ {Γ Δ α} (x : (slotAt Δ α).ToType),
    OrdinalSlot.rank (inr (Γ := Γ) x) = slotAt Γ α + OrdinalSlot.rank x
  inl_lt_inr : ∀ {Γ Δ α} (x : (slotAt Γ α).ToType) (y : (slotAt Δ α).ToType),
                inl x < inr y
  copair : ∀ (Γ Δ) {α} , (X : Type) → ((slotAt Γ α).ToType → X) → ((slotAt Δ α).ToType → X) →
            (slotAt (Γ * Δ) α).ToType → X
  copair_inl : ∀ (Γ Δ : Arity) {α : Arity} (X : Type)
                   (f : (slotAt Γ α).ToType → X) (g : (slotAt Δ α).ToType → X),
                   copair Γ Δ X f g ∘ inl = f
  copair_inr : ∀ (Γ Δ : Arity) {α : Arity} (X : Type)
                   (f : (slotAt Γ α).ToType → X) (g : (slotAt Δ α).ToType → X),
                   copair Γ Δ X f g ∘ inr = g
  /-- Cover: every slot of a product comes from the right or left injection. -/
  cover : ∀ (Γ Δ : Arity) {α : Arity} (p : (slotAt (Γ * Δ) α).ToType),
    (∃ x : (slotAt Γ α).ToType, p = inl x) ∨
    (∃ y : (slotAt Δ α).ToType, p = inr y)
  subWf : WellFounded (fun Δ Γ => Nonempty (slotAt Γ Δ).ToType)


/-- One-step sub-arity relation: `α' ≺ α` when `α'` is the sub-arity of some position of
`α`.  Well-founded by `subWf`. -/
abbrev Carrier.Sub {A : Type} {C : Carrier A} (Δ Γ : C.Arity) : Prop :=
  Nonempty (C.slotAt Γ Δ).ToType

/-- The carrier's sub-arity well-founded relation, packaged as a `WellFoundedRelation`
instance for use in `termination_by`. -/
instance {A : Type} (C : Carrier A) : WellFoundedRelation (C.Arity) where
  rel := Carrier.Sub
  wf := C.subWf

abbrev SlotAt {A : Type} {C : Carrier A} (Γ Δ : C.Arity) : Type :=
  (C.slotAt Γ Δ).ToType

infix:35 " ∋ " => SlotAt

abbrev Ext {A : Type} {C : Carrier A} (Γ Δ : C.Arity) : C.Arity := Γ * Δ

infixl:65 " ⋈ " => Ext

namespace Carrier

/-- The monoidal unit has no slots. -/
theorem unit_is_empty {A : Type} (C : Carrier A) {α : C.Arity} (x : 1 ∋ α) :
    False :=
  not_lt_zero (Ordinal.typein_lt_self (C.unit_empty α ▸ x : (0 : Ordinal).ToType))

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

/-- A candidate coproduct structure on the product `Γ * Δ`, pinned by ordinal ranks. -/
structure CoprodData {A : Type} (C : Carrier A) (Γ Δ : C.Arity) where
  inl : (α : C.Arity) → Γ ∋ α → Γ * Δ ∋ α
  inr : (α : C.Arity) → Δ ∋ α → Γ * Δ ∋ α
  copair : (α : C.Arity) → (X : Type) → (Γ ∋ α → X) → (Δ ∋ α → X) →
    (Γ * Δ ∋ α) → X
  copair_inl : ∀ (α : C.Arity) (X : Type) (f : Γ ∋ α → X) (g : Δ ∋ α → X),
    copair α X f g ∘ inl α = f
  copair_inr : ∀ (α : C.Arity) (X : Type) (f : Γ ∋ α → X) (g : Δ ∋ α → X),
    copair α X f g ∘ inr α = g
  cover : ∀ (α : C.Arity) (p : Γ * Δ ∋ α),
    (∃ x : Γ ∋ α, p = inl α x) ∨ (∃ y : Δ ∋ α, p = inr α y)
  inl_rank : ∀ (α : C.Arity) (x : Γ ∋ α),
    OrdinalSlot.rank (inl α x) = OrdinalSlot.rank x
  inr_rank : ∀ (α : C.Arity) (x : Δ ∋ α),
    OrdinalSlot.rank (inr α x) = C.slotAt Γ α + OrdinalSlot.rank x
  inl_strictMono : ∀ (α : C.Arity), StrictMono (inl α)
  inr_strictMono : ∀ (α : C.Arity), StrictMono (inr α)
  inl_lt_inr : ∀ (α : C.Arity) (x : Γ ∋ α) (y : Δ ∋ α), inl α x < inr α y

private theorem CoprodData.ext_data {A : Type} {C : Carrier A} {Γ Δ : C.Arity}
    (P Q : CoprodData C Γ Δ)
    (hl : P.inl = Q.inl) (hr : P.inr = Q.inr) (hc : P.copair = Q.copair) :
    P = Q := by
  cases P
  cases Q
  subst hl
  subst hr
  subst hc
  rfl

instance {A : Type} {C : Carrier A} (Γ Δ : C.Arity) :
    Subsingleton (CoprodData C Γ Δ) := by
  constructor
  intro P Q
  have hl : P.inl = Q.inl := by
    funext α x
    apply OrdinalSlot.ext
    rw [P.inl_rank, Q.inl_rank]
  have hr : P.inr = Q.inr := by
    funext α x
    apply OrdinalSlot.ext
    rw [P.inr_rank, Q.inr_rank]
  have hc : P.copair = Q.copair := by
    funext α X f g p
    rcases P.cover α p with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · have hP := congrFun (P.copair_inl α X f g) x
      have hQ := congrFun (Q.copair_inl α X f g) x
      rw [← hl] at hQ
      exact hP.trans hQ.symm
    · have hP := congrFun (P.copair_inr α X f g) y
      have hQ := congrFun (Q.copair_inr α X f g) y
      rw [← hr] at hQ
      exact hP.trans hQ.symm
  exact CoprodData.ext_data P Q hl hr hc

def nativeCoprod {A : Type} (C : Carrier A) (Γ Δ : C.Arity) : CoprodData C Γ Δ where
  inl := fun _ x => C.inl x
  inr := fun _ x => C.inr x
  copair := fun _ X f g p => C.copair Γ Δ X f g p
  copair_inl := fun _ X f g => C.copair_inl Γ Δ X f g
  copair_inr := fun _ X f g => C.copair_inr Γ Δ X f g
  cover := fun _ p => C.cover Γ Δ p
  inl_rank := fun _ x => C.inl_rank x
  inr_rank := fun _ x => C.inr_rank x
  inl_strictMono := fun _ => C.inl_strictMono
  inr_strictMono := fun _ => C.inr_strictMono
  inl_lt_inr := fun _ x y => C.inl_lt_inr x y

theorem inr_inl {A : Type} (C : Carrier A)
    (Γ Δ Ξ : C.Arity) {α : C.Arity} (x : Δ ∋ α) :
  (C.inr (C.inl x) : Γ * (Δ * Ξ) ∋ α)
    =
  (C.inl (C.inr x) : (Γ * Δ) * Ξ ∋ α) := by
  apply OrdinalSlot.ext
  have hL := C.inr_rank (Γ := Γ) (Δ := Δ * Ξ) (α := α) (x := C.inl (Δ := Ξ) x)
  have hLm := C.inl_rank (Γ := Δ) (Δ := Ξ) (α := α) (x := x)
  have hR := C.inl_rank (Γ := Γ * Δ) (Δ := Ξ) (α := α) (x := C.inr (Γ := Γ) x)
  have hRm := C.inr_rank (Γ := Γ) (Δ := Δ) (α := α) (x := x)
  calc
    OrdinalSlot.rank (C.inr (C.inl x) : Γ * (Δ * Ξ) ∋ α)
        = C.slotAt Γ α + OrdinalSlot.rank (C.inl (Δ := Ξ) x) := hL
    _ = C.slotAt Γ α + OrdinalSlot.rank x := by rw [hLm]
    _ = OrdinalSlot.rank (C.inr (Γ := Γ) x) := hRm.symm
    _ = OrdinalSlot.rank (C.inl (C.inr x) : (Γ * Δ) * Ξ ∋ α) := hR.symm

theorem inr_inr {A : Type} (C : Carrier A)
    (Γ Δ Ξ : C.Arity) {α : C.Arity} (x : Ξ ∋ α) :
  (C.inr (C.inr x) : Γ * (Δ * Ξ) ∋ α)
    =
  (C.inr x : (Γ * Δ) * Ξ ∋ α) := by
  apply OrdinalSlot.ext
  have hL := C.inr_rank (Γ := Γ) (Δ := Δ * Ξ) (α := α) (x := C.inr (Γ := Δ) x)
  have hLm := C.inr_rank (Γ := Δ) (Δ := Ξ) (α := α) (x := x)
  have hR := C.inr_rank (Γ := Γ * Δ) (Δ := Ξ) (α := α) (x := x)
  calc
    OrdinalSlot.rank (C.inr (C.inr x) : Γ * (Δ * Ξ) ∋ α)
        = C.slotAt Γ α + OrdinalSlot.rank (C.inr (Γ := Δ) x) := hL
    _ = C.slotAt Γ α + (C.slotAt Δ α + OrdinalSlot.rank x) := by rw [hLm]
    _ = (C.slotAt Γ α + C.slotAt Δ α) + OrdinalSlot.rank x := by rw [add_assoc]
    _ = C.slotAt (Γ * Δ) α + OrdinalSlot.rank x := by rw [C.slotAt_mul]
    _ = OrdinalSlot.rank (C.inr (Γ := Γ * Δ) x) := hR.symm

theorem unit_right {A : Type} (C : Carrier A) (Γ : C.Arity)
    {α : C.Arity} (x : Γ ∋ α) :
  (C.inl x : Γ * 1 ∋ α) = x := by
  apply OrdinalSlot.ext
  exact C.inl_rank (Δ := 1) x

theorem unit_left {A : Type} (C : Carrier A) (Γ : C.Arity)
    {α : C.Arity} (x : Γ ∋ α) :
  (C.inr x : 1 * Γ ∋ α) = x := by
  apply OrdinalSlot.ext
  have h := C.inr_rank (Γ := 1) (Δ := Γ) (α := α) (x := x)
  calc
    OrdinalSlot.rank (C.inr (Γ := 1) x) = C.slotAt 1 α + OrdinalSlot.rank x := h
    _ = 0 + OrdinalSlot.rank x := by rw [C.unit_empty]
    _ = OrdinalSlot.rank x := by rw [zero_add]

end Carrier
