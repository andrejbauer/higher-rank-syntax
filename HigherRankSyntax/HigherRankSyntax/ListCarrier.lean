import HigherRankSyntax.Carrier
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.SuccPred

/-!
# The list carrier

`ListCarrier.carrier` is a carrier whose arities are the endofunctions `prepend ℓ`
of `List Entry`, identified with the lists `ℓ` of entries; each entry carries a binding
arity, itself such a list.  The slots of `Γ` of arity `α` are the positions of `Γ`
whose entry has binding arity `α`, ordered left to right.  The part of `Γ` before a
slot is the segment strictly before its position, the part after it is the segment
from its position on.  `C` is this carrier, and `C.single α` is the arity with a
single entry, of binding arity `α`.
-/

namespace ListCarrier

/-- An entry of an arity: `Entry.mk Δ` has binding arity `Δ`. -/
inductive Entry where
  | mk : List Entry → Entry

/-- The binding arity of an entry. -/
def Entry.arity : Entry → List Entry
  | .mk Δ => Δ

theorem Entry.sizeOf_arity_lt (e : Entry) :
  sizeOf e.arity < sizeOf e
  := by
  cases e
  simp [arity]

theorem sizeOf_arity_lt_of_mem {e : Entry} {ℓ : List Entry} (h : e ∈ ℓ) :
  sizeOf e.arity < sizeOf ℓ
  := lt_trans e.sizeOf_arity_lt (List.sizeOf_lt_of_mem h)

/-- Prepending a fixed list, as an endofunction of lists. -/
def prepend (ℓ : List Entry) : Function.End (List Entry) :=
  fun Θ => ℓ ++ Θ

/-- The submonoid of the endofunctions of `List Entry` of the form `prepend ℓ`. -/
def aritySubmonoid : Submonoid (Function.End (List Entry)) where
  carrier := Set.range prepend
  one_mem' := ⟨[], rfl⟩
  mul_mem' := by
    rintro _ _ ⟨ℓ₁, rfl⟩ ⟨ℓ₂, rfl⟩
    use ℓ₁ ++ ℓ₂
    funext Θ
    apply List.append_assoc

/-- The list `ℓ` of an arity `prepend ℓ`. -/
def underlyingList (Γ : aritySubmonoid) : List Entry := Γ.val []

theorem val_apply (Γ : aritySubmonoid) (Θ : List Entry) :
  Γ.val Θ = underlyingList Γ ++ Θ
  := by
  obtain ⟨ℓ, h⟩ := Γ.property
  simp [underlyingList, ← h, prepend]

/-- The arity `prepend ℓ`. -/
def ofList (ℓ : List Entry) : aritySubmonoid :=
  ⟨prepend ℓ, ℓ, rfl⟩

@[simp]
theorem underlyingList_ofList (ℓ : List Entry) :
  underlyingList (ofList ℓ) = ℓ
  := List.append_nil ℓ

theorem underlyingList_mul (Γ Δ : aritySubmonoid) :
  underlyingList (Γ * Δ) = underlyingList Γ ++ underlyingList Δ
  := val_apply Γ (underlyingList Δ)

/-- An arity is determined by its underlying list. -/
theorem arity_ext {Γ Δ : aritySubmonoid} (h : underlyingList Γ = underlyingList Δ) :
  Γ = Δ
  := by
  apply Subtype.ext
  funext Θ
  rw [val_apply Γ, val_apply Δ, h]

/-- The positions of `ℓ` whose entry satisfies `P`. -/
def Position (P : Entry → Prop) (ℓ : List Entry) : Type :=
  { i : Fin ℓ.length // P (ℓ.get i) }

/-- The index of a position, as an order embedding into `ℕ`. -/
def positionEmbedding (P : Entry → Prop) (ℓ : List Entry) :
    (fun x y : Position P ℓ => x.val < y.val) ↪r ((· < ·) : ℕ → ℕ → Prop) where
  toFun x := x.val.val
  inj' _ _ h := Subtype.ext (Fin.val_injective h)
  map_rel_iff' := Iff.rfl

instance (P : Entry → Prop) (ℓ : List Entry) :
    IsWellOrder (Position P ℓ) (fun x y => x.val < y.val) :=
  (positionEmbedding P ℓ).isWellOrder

/-- The positions of `ℓ` whose entry satisfies `P`, ordered by index. -/
@[reducible] def positionWellOrder (P : Entry → Prop) (ℓ : List Entry) : WellOrder :=
  ⟨Position P ℓ, fun x y => x.val < y.val, inferInstance⟩

/-- The order isomorphism of positions induced by an equality `ℓ = ℓ'`. -/
def positionCongr (P : Entry → Prop) {ℓ ℓ' : List Entry} (h : ℓ = ℓ') :
    (positionWellOrder P ℓ).r ≃r (positionWellOrder P ℓ').r := by
  subst h
  exact RelIso.refl _

/-- Transporting a position along a list equality preserves its index. -/
theorem positionCongr_val
    (P : Entry → Prop) {ℓ ℓ' : List Entry} (h : ℓ = ℓ') (x : Position P ℓ) :
  (positionCongr P h x).val.val = x.val.val
  := by
  subst h
  rfl

private def sumSubtypeEquiv (P : Entry → Prop) (ℓ₁ ℓ₂ : List Entry) :
    Position P ℓ₁ ⊕ Position P ℓ₂
      ≃ { x : Fin ℓ₁.length ⊕ Fin ℓ₂.length //
          Sum.elim (fun i => P (ℓ₁.get i)) (fun j => P (ℓ₂.get j)) x } where
  toFun x :=
    match x with
    | .inl y => ⟨.inl y.val, y.property⟩
    | .inr y => ⟨.inr y.val, y.property⟩
  invFun x :=
    match x with
    | ⟨.inl i, h⟩ => .inl ⟨i, h⟩
    | ⟨.inr j, h⟩ => .inr ⟨j, h⟩
  left_inv x := by rcases x with y | y <;> rfl
  right_inv x := by rcases x with ⟨i | j, h⟩ <;> rfl

private def finAppendEquiv (ℓ₁ ℓ₂ : List Entry) :
    Fin ℓ₁.length ⊕ Fin ℓ₂.length ≃ Fin (ℓ₁ ++ ℓ₂).length :=
  finSumFinEquiv.trans (finCongr List.length_append.symm)

private theorem elim_position_iff (P : Entry → Prop) (ℓ₁ ℓ₂ : List Entry)
    (x : Fin ℓ₁.length ⊕ Fin ℓ₂.length) :
  Sum.elim (fun i => P (ℓ₁.get i)) (fun j => P (ℓ₂.get j)) x
    ↔ P ((ℓ₁ ++ ℓ₂).get (finAppendEquiv ℓ₁ ℓ₂ x))
  := by
  rcases x with i | j
  · simp [finAppendEquiv]
  · simp [finAppendEquiv]

private def positionAppendEquiv (P : Entry → Prop) (ℓ₁ ℓ₂ : List Entry) :
    Position P ℓ₁ ⊕ Position P ℓ₂ ≃ Position P (ℓ₁ ++ ℓ₂) :=
  (sumSubtypeEquiv P ℓ₁ ℓ₂).trans
    (Equiv.subtypeEquiv (finAppendEquiv ℓ₁ ℓ₂) (elim_position_iff P ℓ₁ ℓ₂))

private theorem positionAppendEquiv_val_inl
    (P : Entry → Prop) {ℓ₁ ℓ₂ : List Entry} (y : Position P ℓ₁) :
  ((positionAppendEquiv P ℓ₁ ℓ₂) (Sum.inl y)).val.val = y.val.val
  := rfl

private theorem positionAppendEquiv_val_inr
    (P : Entry → Prop) {ℓ₁ ℓ₂ : List Entry} (y : Position P ℓ₂) :
  ((positionAppendEquiv P ℓ₁ ℓ₂) (Sum.inr y)).val.val = ℓ₁.length + y.val.val
  := rfl

/-- The positions of `ℓ₁ ++ ℓ₂` as the lexicographic sum of the positions of `ℓ₁` and
of `ℓ₂`, the latter shifted by `ℓ₁.length`. -/
def positionAppend (P : Entry → Prop) (ℓ₁ ℓ₂ : List Entry) :
    Sum.Lex (positionWellOrder P ℓ₁).r (positionWellOrder P ℓ₂).r
      ≃r (positionWellOrder P (ℓ₁ ++ ℓ₂)).r where
  toEquiv := positionAppendEquiv P ℓ₁ ℓ₂
  map_rel_iff' := by
    rintro (x | x) (y | y)
    · simp only [positionWellOrder, Fin.lt_def, positionAppendEquiv_val_inl, Sum.lex_inl_inl]
    · simp only [positionWellOrder, Fin.lt_def, positionAppendEquiv_val_inl,
        positionAppendEquiv_val_inr, Sum.Lex.sep, iff_true]
      omega
    · simp only [positionWellOrder, Fin.lt_def, positionAppendEquiv_val_inl,
        positionAppendEquiv_val_inr, Sum.lex_inr_inl, iff_false]
      omega
    · simp only [positionWellOrder, Fin.lt_def, positionAppendEquiv_val_inr, Sum.lex_inr_inr]
      omega

/-- `slotPredicate α e`: the binding arity of `e` is `α`. -/
def slotPredicate (α : aritySubmonoid) (e : Entry) : Prop :=
  e.arity = underlyingList α

/-- The slots of `Γ` of arity `α`: the positions of `Γ` whose entry has binding
arity `α`. -/
abbrev Slot (Γ α : aritySubmonoid) : Type :=
  Position (slotPredicate α) (underlyingList Γ)

/-- The slots of `Γ * Δ` of arity `α` as the lexicographic sum of those of `Γ` and of
`Δ`. -/
def slotAppend (Γ Δ α : aritySubmonoid) :
    Sum.Lex (positionWellOrder (slotPredicate α) (underlyingList Γ)).r
        (positionWellOrder (slotPredicate α) (underlyingList Δ)).r
      ≃r (positionWellOrder (slotPredicate α) (underlyingList (Γ * Δ))).r :=
  (positionAppend (slotPredicate α) (underlyingList Γ) (underlyingList Δ)).trans
    (positionCongr (slotPredicate α) (underlyingList_mul Γ Δ).symm)

theorem slotAppend_val_inl {Γ Δ α : aritySubmonoid} (x : Slot Γ α) :
  (slotAppend Γ Δ α (Sum.inl x)).val.val = x.val.val
  := by
  rw [slotAppend, RelIso.trans_apply, positionCongr_val]
  rfl

theorem slotAppend_val_inr {Γ Δ α : aritySubmonoid} (x : Slot Δ α) :
  (slotAppend Γ Δ α (Sum.inr x)).val.val = (underlyingList Γ).length + x.val.val
  := by
  rw [slotAppend, RelIso.trans_apply, positionCongr_val]
  rfl

theorem sub_sizeOf {Δ Γ : aritySubmonoid} (x : Slot Γ Δ) :
  sizeOf (underlyingList Δ) < sizeOf (underlyingList Γ)
  := by
  rw [← x.property]
  apply sizeOf_arity_lt_of_mem
  apply List.get_mem

/-! ### Splitting an arity at a slot -/

/-- The part of `Γ` strictly before the slot `x`. -/
def before {Γ α : aritySubmonoid} (x : Slot Γ α) : aritySubmonoid :=
  ofList ((underlyingList Γ).take x.val.val)

/-- The part of `Γ` from the slot `x` on. -/
def after {Γ α : aritySubmonoid} (x : Slot Γ α) : aritySubmonoid :=
  ofList ((underlyingList Γ).drop x.val.val)

theorem before_after {Γ α : aritySubmonoid} (x : Slot Γ α) :
  before x * after x = Γ
  := by
  apply arity_ext
  rw [underlyingList_mul]
  simp only [before, after, underlyingList_ofList]
  apply List.take_append_drop

/-- The slot `x` as the first position of `after x`. -/
def localized {Γ α : aritySubmonoid} (x : Slot Γ α) : Slot (after x) α := by
  refine ⟨⟨0, ?_⟩, ?_⟩
  · simp only [after, underlyingList_ofList, List.length_drop]
    omega
  · simpa [after, slotPredicate, List.get_eq_getElem] using x.property

theorem transport_val {Γ Δ α : aritySubmonoid} (h : Γ = Δ) (x : Slot Γ α) :
  (h ▸ x : Slot Δ α).val.val = x.val.val
  := by
  subst h
  rfl

theorem reinject {Γ α : aritySubmonoid} (x : Slot Γ α) :
  before_after x ▸ slotAppend (before x) (after x) α (Sum.inr (localized x)) = x
  := by
  apply Subtype.ext
  apply Fin.ext
  rw [transport_val, slotAppend_val_inr]
  simp only [before, localized, underlyingList_ofList, List.length_take]
  omega

theorem before_inl {Γ Δ α : aritySubmonoid} (x : Slot Γ α) :
  before (slotAppend Γ Δ α (Sum.inl x)) = before x
  := by
  apply arity_ext
  simp only [before, underlyingList_ofList]
  rw [slotAppend_val_inl, underlyingList_mul]
  apply List.take_append_of_le_length x.val.isLt.le

theorem after_inl {Γ Δ α : aritySubmonoid} (x : Slot Γ α) :
  after (slotAppend Γ Δ α (Sum.inl x)) = after x * Δ
  := by
  apply arity_ext
  simp only [after, underlyingList_ofList]
  rw [slotAppend_val_inl]
  simp only [underlyingList_mul, underlyingList_ofList]
  apply List.drop_append_of_le_length x.val.isLt.le

theorem before_inr {Γ Δ α : aritySubmonoid} (x : Slot Δ α) :
  before (slotAppend Γ Δ α (Sum.inr x)) = Γ * before x
  := by
  apply arity_ext
  simp only [before, underlyingList_ofList]
  rw [slotAppend_val_inr]
  simp only [underlyingList_mul, underlyingList_ofList]
  apply List.take_length_add_append

theorem after_inr {Γ Δ α : aritySubmonoid} (x : Slot Δ α) :
  after (slotAppend Γ Δ α (Sum.inr x)) = after x
  := by
  apply arity_ext
  simp only [after, underlyingList_ofList]
  rw [slotAppend_val_inr, underlyingList_mul]
  apply List.drop_length_add_append

theorem before_of_lt {Γ α : aritySubmonoid} {x y : Slot Γ α} (h : x.val < y.val) :
  ∃ x' : Slot (before y) α,
    before_after y ▸ slotAppend (before y) (after y) α (Sum.inl x') = x
  := by
  have hx : x.val.val < (underlyingList (before y)).length := by
    simp only [before, underlyingList_ofList, List.length_take]
    omega
  use ⟨⟨x.val.val, hx⟩, by simpa [before] using x.property⟩
  apply Subtype.ext
  apply Fin.ext
  rw [transport_val, slotAppend_val_inl]

/-! ### The carrier -/

/-- The carrier whose arities are lists of entries and whose slots of arity `α` are
the positions holding an entry of binding arity `α`, ordered left to right. -/
def carrier : Carrier (List Entry) where
  Arity := aritySubmonoid
  slotAt Γ α := positionWellOrder (slotPredicate α) (underlyingList Γ)
  unit_empty _ := ⟨fun x => x.val.elim0⟩
  slotAt_mul := slotAppend
  subWf :=
    Subrelation.wf (fun ⟨x⟩ => sub_sizeOf x)
      (InvImage.wf (fun Γ => sizeOf (underlyingList Γ)) Nat.lt_wfRel.wf)
  before := before
  after := after
  factor := before_after
  localized := localized
  reinject := reinject
  before_inl := before_inl
  after_inl := after_inl
  before_inr := before_inr
  after_inr := after_inr
  before_of_lt := before_of_lt

end ListCarrier

/-- The list carrier `ListCarrier.carrier`. -/
abbrev C : Carrier (List ListCarrier.Entry) := ListCarrier.carrier

open ListCarrier

/-! ### Single-entry arities -/

/-- An arity is determined by its underlying list. -/
theorem ListCarrier.underlyingList_injective {Γ Δ : C.Arity}
    (h : underlyingList Γ = underlyingList Δ) :
  Γ = Δ
  := arity_ext h

/-- The arity with a single entry, of binding arity `α`. -/
def C.single (α : C.Arity) : C.Arity :=
  ofList [Entry.mk (underlyingList α)]

/-- The underlying list of `C.single α` is `[Entry.mk (underlyingList α)]`. -/
@[simp]
theorem C.underlyingList_single (α : C.Arity) :
  underlyingList (C.single α) = [Entry.mk (underlyingList α)]
  := underlyingList_ofList _

/-- The slot of `C.single α` of arity `α`, at position `0`. -/
def C.singleSlot (α : C.Arity) : C.single α ∋ α :=
  ⟨⟨0, by simp⟩, rfl⟩

/-- Every position of a one-element list `[a]` holds `a`. -/
theorem ListCarrier.get_singleton {ℓ : List Entry} {a : Entry} (hl : ℓ = [a])
    (i : Fin ℓ.length) :
  ℓ.get i = a
  := by
  subst hl
  simp

/-- Single-entry arities are equal only for equal binding arities. -/
theorem C.single_injective :
  Function.Injective C.single
  := by
  intro α β h
  have hlist := congrArg underlyingList h
  simp only [underlyingList_single, List.cons.injEq, Entry.mk.injEq, and_true] at hlist
  apply underlyingList_injective hlist

/-- `C.singleSlot α` is the only slot of `C.single α` of arity `α`. -/
theorem C.single_slot_unique {α : C.Arity} (z : C.single α ∋ α) :
  z = C.singleSlot α
  := by
  apply Subtype.ext
  apply Fin.ext
  simp

/-- Every slot of `C.single α` has arity `α`. -/
theorem C.single_arity {α β : C.Arity} (x : C.single α ∋ β) :
  β = α
  := by
  apply underlyingList_injective
  rw [← x.property, get_singleton (underlyingList_single α) x.val]
  rfl
