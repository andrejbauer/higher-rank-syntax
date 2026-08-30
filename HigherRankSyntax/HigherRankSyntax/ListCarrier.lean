import HigherRankSyntax.Carrier
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.SuccPred

/-!
# The list carrier

`listCarrier` is the free carrier on nothing: arities are lists of entries, an
entry is a binding arity, slots are list positions.  Precedence is the
left-to-right order of positions, so the part of an arity preceding a slot is
the segment strictly before its position.
-/

namespace ListCarrier

/-- An entry: a binding arity. -/
inductive Entry where
  | mk : List Entry → Entry

/-- The binding arity of an entry. -/
def Entry.arity : Entry → List Entry
  | .mk Δ => Δ

theorem Entry.sizeOf_arity_lt (e : Entry) : sizeOf e.arity < sizeOf e := by
  cases e with
  | mk Δ => simp only [Entry.arity, Entry.mk.sizeOf_spec]; omega

theorem sizeOf_arity_lt_of_mem {e : Entry} {ℓ : List Entry} (h : e ∈ ℓ) :
    sizeOf e.arity < sizeOf ℓ :=
  lt_trans e.sizeOf_arity_lt (List.sizeOf_lt_of_mem h)

/-- Prepending a fixed list, as an endofunction of lists. -/
def prepend (ℓ : List Entry) : Function.End (List Entry) :=
  fun Θ => ℓ ++ Θ

/-- The arity submonoid: endofunctions of the form `prepend ℓ`. -/
def aritySubmonoid : Submonoid (Function.End (List Entry)) where
  carrier := Set.range prepend
  one_mem' := ⟨[], rfl⟩
  mul_mem' := by
    rintro _ _ ⟨ℓ₁, rfl⟩ ⟨ℓ₂, rfl⟩
    exact ⟨ℓ₁ ++ ℓ₂, funext fun Θ => List.append_assoc ℓ₁ ℓ₂ Θ⟩

/-- The underlying list of an arity. -/
def underlyingList (Γ : aritySubmonoid) : List Entry := Γ.val []

theorem val_apply (Γ : aritySubmonoid) (Θ : List Entry) :
    Γ.val Θ = underlyingList Γ ++ Θ := by
  obtain ⟨ℓ, h⟩ := Γ.property
  rw [underlyingList, ← h]
  simp [prepend]

theorem underlyingList_one : underlyingList (1 : aritySubmonoid) = [] := rfl

/-- The arity presented by a list. -/
def ofList (ℓ : List Entry) : aritySubmonoid :=
  ⟨prepend ℓ, ℓ, rfl⟩

@[simp] theorem underlyingList_ofList (ℓ : List Entry) :
    underlyingList (ofList ℓ) = ℓ :=
  List.append_nil ℓ

theorem underlyingList_mul (Γ Δ : aritySubmonoid) :
    underlyingList (Γ * Δ) = underlyingList Γ ++ underlyingList Δ :=
  val_apply Γ (underlyingList Δ)

/-- An arity is determined by its underlying list. -/
theorem arity_ext {Γ Δ : aritySubmonoid}
    (h : underlyingList Γ = underlyingList Δ) : Γ = Δ := by
  apply Subtype.ext
  funext Θ
  rw [val_apply Γ, val_apply Δ, h]

/-- Positions of a list whose entry satisfies a predicate. -/
def Position (P : Entry → Prop) (ℓ : List Entry) : Type :=
  { i : Fin ℓ.length // P (ℓ.get i) }

/-- Position order embeds into `ℕ`. -/
def positionEmbedding (P : Entry → Prop) (ℓ : List Entry) :
    (fun x y : Position P ℓ => x.val < y.val) ↪r ((· < ·) : ℕ → ℕ → Prop) where
  toFun x := x.val.val
  inj' _ _ h := Subtype.ext (Fin.val_injective h)
  map_rel_iff' := Iff.rfl

instance (P : Entry → Prop) (ℓ : List Entry) :
    IsWellOrder (Position P ℓ) (fun x y => x.val < y.val) :=
  (positionEmbedding P ℓ).isWellOrder

/-- The well-order of positions at a predicate. -/
@[reducible] def positionWellOrder (P : Entry → Prop) (ℓ : List Entry) : WellOrder :=
  ⟨Position P ℓ, fun x y => x.val < y.val, inferInstance⟩

/-- Transport of position well-orders along a list equation. -/
def positionCongr (P : Entry → Prop) {ℓ ℓ' : List Entry} (h : ℓ = ℓ') :
    (positionWellOrder P ℓ).r ≃r (positionWellOrder P ℓ').r := by
  subst h
  exact RelIso.refl _

/-- Transporting a position along a list equality preserves its index. -/
theorem positionCongr_val (P : Entry → Prop) {ℓ ℓ' : List Entry}
    (h : ℓ = ℓ') (x : Position P ℓ) :
    ((positionCongr P h x).val.val : ℕ) = x.val.val := by
  subst h
  rfl

private theorem split_index_lt {ℓ₁ ℓ₂ : List Entry} (k : Fin (ℓ₁ ++ ℓ₂).length)
    (h : ¬ k.val < ℓ₁.length) : k.val - ℓ₁.length < ℓ₂.length := by
  have hlen : (ℓ₁ ++ ℓ₂).length = ℓ₁.length + ℓ₂.length := List.length_append
  omega

private theorem get_append_left {ℓ₁ ℓ₂ : List Entry} (k : Fin (ℓ₁ ++ ℓ₂).length)
    (h : k.val < ℓ₁.length) : (ℓ₁ ++ ℓ₂).get k = ℓ₁.get ⟨k.val, h⟩ := by
  simp [List.get_eq_getElem, List.getElem_append_left h]

private theorem get_append_right {ℓ₁ ℓ₂ : List Entry} (k : Fin (ℓ₁ ++ ℓ₂).length)
    (h : ¬ k.val < ℓ₁.length) (hlt : k.val - ℓ₁.length < ℓ₂.length) :
    (ℓ₁ ++ ℓ₂).get k = ℓ₂.get ⟨k.val - ℓ₁.length, hlt⟩ := by
  simp [List.get_eq_getElem, List.getElem_append_right (Nat.le_of_not_lt h)]

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
  finSumFinEquiv.trans
    (finCongr (Eq.symm (List.length_append : (ℓ₁ ++ ℓ₂).length = ℓ₁.length + ℓ₂.length)))

private theorem elim_position_iff (P : Entry → Prop) (ℓ₁ ℓ₂ : List Entry)
    (x : Fin ℓ₁.length ⊕ Fin ℓ₂.length) :
    Sum.elim (fun i => P (ℓ₁.get i)) (fun j => P (ℓ₂.get j)) x
      ↔ P ((ℓ₁ ++ ℓ₂).get (finAppendEquiv ℓ₁ ℓ₂ x)) := by
  rcases x with i | j
  · have hv : ((finAppendEquiv ℓ₁ ℓ₂) (Sum.inl i)).val = i.val := by
      simp [finAppendEquiv]
    have hlt : ((finAppendEquiv ℓ₁ ℓ₂) (Sum.inl i)).val < ℓ₁.length := by
      rw [hv]; exact i.isLt
    rw [Sum.elim_inl, get_append_left _ hlt]
    have heq : (⟨((finAppendEquiv ℓ₁ ℓ₂) (Sum.inl i)).val, hlt⟩ : Fin ℓ₁.length) = i :=
      Fin.ext hv
    rw [heq]
  · have hv : ((finAppendEquiv ℓ₁ ℓ₂) (Sum.inr j)).val = ℓ₁.length + j.val := by
      simp [finAppendEquiv]
    have hnot : ¬ ((finAppendEquiv ℓ₁ ℓ₂) (Sum.inr j)).val < ℓ₁.length := by omega
    have hlt := split_index_lt ((finAppendEquiv ℓ₁ ℓ₂) (Sum.inr j)) hnot
    rw [Sum.elim_inr, get_append_right _ hnot hlt]
    have hval : ((finAppendEquiv ℓ₁ ℓ₂) (Sum.inr j)).val - ℓ₁.length = j.val := by omega
    have heq : (⟨((finAppendEquiv ℓ₁ ℓ₂) (Sum.inr j)).val - ℓ₁.length, hlt⟩ : Fin ℓ₂.length) = j :=
      Fin.ext hval
    rw [heq]

private def positionAppendEquiv (P : Entry → Prop) (ℓ₁ ℓ₂ : List Entry) :
    Position P ℓ₁ ⊕ Position P ℓ₂ ≃ Position P (ℓ₁ ++ ℓ₂) :=
  (sumSubtypeEquiv P ℓ₁ ℓ₂).trans
    (Equiv.subtypeEquiv (finAppendEquiv ℓ₁ ℓ₂) (elim_position_iff P ℓ₁ ℓ₂))

private theorem positionAppendEquiv_val_inl (P : Entry → Prop) {ℓ₁ ℓ₂ : List Entry}
    (y : Position P ℓ₁) :
    ((positionAppendEquiv P ℓ₁ ℓ₂) (Sum.inl y)).val.val = y.val.val :=
  rfl

private theorem positionAppendEquiv_val_inr (P : Entry → Prop) {ℓ₁ ℓ₂ : List Entry}
    (y : Position P ℓ₂) :
    ((positionAppendEquiv P ℓ₁ ℓ₂) (Sum.inr y)).val.val = ℓ₁.length + y.val.val :=
  rfl

/-- Positions of a concatenation are the lexicographic sum of positions. -/
def positionAppend (P : Entry → Prop) (ℓ₁ ℓ₂ : List Entry) :
    Sum.Lex (positionWellOrder P ℓ₁).r (positionWellOrder P ℓ₂).r
      ≃r (positionWellOrder P (ℓ₁ ++ ℓ₂)).r where
  toEquiv := positionAppendEquiv P ℓ₁ ℓ₂
  map_rel_iff' := by
    intro x y
    rcases x with x | x <;> rcases y with y | y
    · simp only [positionWellOrder, Fin.lt_def, positionAppendEquiv_val_inl, Sum.lex_inl_inl]
    · refine iff_of_true ?_ (Sum.Lex.sep _ _)
      simp only [positionWellOrder, Fin.lt_def, positionAppendEquiv_val_inl,
        positionAppendEquiv_val_inr]
      omega
    · refine iff_of_false ?_ (fun h => nomatch h)
      simp only [positionWellOrder, Fin.lt_def, positionAppendEquiv_val_inl,
        positionAppendEquiv_val_inr]
      omega
    · simp only [positionWellOrder, Fin.lt_def, positionAppendEquiv_val_inr, Sum.lex_inr_inr]
      omega

/-- The slot predicate: matching binding arity. -/
def slotPredicate (α : aritySubmonoid) (e : Entry) : Prop :=
  e.arity = underlyingList α

/-- The slots of `Γ` at binding arity `α`. -/
abbrev Slot (Γ α : aritySubmonoid) : Type :=
  Position (slotPredicate α) (underlyingList Γ)

/-- Slots of a product are the lexicographic sum of slots. -/
def slotAppend (Γ Δ α : aritySubmonoid) :
    Sum.Lex (positionWellOrder (slotPredicate α) (underlyingList Γ)).r
        (positionWellOrder (slotPredicate α) (underlyingList Δ)).r
      ≃r (positionWellOrder (slotPredicate α) (underlyingList (Γ * Δ))).r :=
  (positionAppend (slotPredicate α) (underlyingList Γ) (underlyingList Δ)).trans
    (positionCongr (slotPredicate α) (underlyingList_mul Γ Δ).symm)

theorem slotAppend_val_inl {Γ Δ α : aritySubmonoid} (x : Slot Γ α) :
    (slotAppend Γ Δ α (Sum.inl x)).val.val = x.val.val := by
  let f := positionAppend (slotPredicate α) (underlyingList Γ) (underlyingList Δ)
  let g := positionCongr (slotPredicate α) (underlyingList_mul Γ Δ).symm
  have htrans := congrArg (fun y => y.val.val) (RelIso.trans_apply f g (Sum.inl x))
  have hcongr := positionCongr_val (slotPredicate α)
    (underlyingList_mul Γ Δ).symm (f (Sum.inl x))
  exact htrans.trans (hcongr.trans (positionAppendEquiv_val_inl (slotPredicate α) x))

theorem slotAppend_val_inr {Γ Δ α : aritySubmonoid} (x : Slot Δ α) :
    (slotAppend Γ Δ α (Sum.inr x)).val.val
      = (underlyingList Γ).length + x.val.val := by
  let f := positionAppend (slotPredicate α) (underlyingList Γ) (underlyingList Δ)
  let g := positionCongr (slotPredicate α) (underlyingList_mul Γ Δ).symm
  have htrans := congrArg (fun y => y.val.val) (RelIso.trans_apply f g (Sum.inr x))
  have hcongr := positionCongr_val (slotPredicate α)
    (underlyingList_mul Γ Δ).symm (f (Sum.inr x))
  exact htrans.trans (hcongr.trans (positionAppendEquiv_val_inr (slotPredicate α) x))

theorem sub_sizeOf {Δ Γ : aritySubmonoid} (x : Slot Γ Δ) :
    sizeOf (underlyingList Δ) < sizeOf (underlyingList Γ) := by
  have hmem : (underlyingList Γ).get x.val ∈ underlyingList Γ :=
    List.get_mem (underlyingList Γ) x.val
  have hlt := sizeOf_arity_lt_of_mem hmem
  rwa [x.property] at hlt

/-! ### Precedence -/

/-- The list segment preceding a slot. -/
def before {Γ α : aritySubmonoid} (x : Slot Γ α) : aritySubmonoid :=
  ofList ((underlyingList Γ).take x.val.val)

/-- The list segment beginning at a slot. -/
def after {Γ α : aritySubmonoid} (x : Slot Γ α) : aritySubmonoid :=
  ofList ((underlyingList Γ).drop x.val.val)

theorem before_after {Γ α : aritySubmonoid} (x : Slot Γ α) :
    before x * after x = Γ := by
  apply arity_ext
  calc
    underlyingList (before x * after x) =
        underlyingList (before x) ++ underlyingList (after x) :=
      underlyingList_mul (before x) (after x)
    _ = List.take x.val.val (underlyingList Γ) ++
        List.drop x.val.val (underlyingList Γ) := by
      simp [before, after]
    _ = underlyingList Γ := List.take_append_drop _ _

/-- A slot sits at the head of the segment beginning at it. -/
def localized {Γ α : aritySubmonoid} (x : Slot Γ α) : Slot (after x) α := by
  refine ⟨⟨0, ?_⟩, ?_⟩
  · simp only [after, underlyingList_ofList, List.length_drop]
    omega
  · simpa [after, slotPredicate, List.get_eq_getElem] using x.property

theorem transport_val {Γ Δ α : aritySubmonoid}
    (h : Γ = Δ) (x : Slot Γ α) :
    (h ▸ x : Slot Δ α).val.val = x.val.val := by
  subst h
  rfl

theorem reinject {Γ α : aritySubmonoid} (x : Slot Γ α) :
    before_after x ▸ slotAppend (before x) (after x) α (Sum.inr (localized x)) = x := by
  apply Subtype.ext
  apply Fin.ext
  calc
    (before_after x ▸ slotAppend (before x) (after x) α (Sum.inr (localized x))
        : Slot Γ α).val.val
        = (slotAppend (before x) (after x) α (Sum.inr (localized x))).val.val :=
      transport_val (before_after x) _
    _ = (underlyingList (before x)).length + (localized x).val.val :=
      slotAppend_val_inr (localized x)
    _ = x.val.val := by
      simp [before, localized]

theorem before_inl {Γ Δ α : aritySubmonoid} (x : Slot Γ α) :
    before (slotAppend Γ Δ α (Sum.inl x)) = before x := by
  apply arity_ext
  simp only [before, underlyingList_ofList]
  rw [slotAppend_val_inl]
  calc
    List.take x.val.val (underlyingList (Γ * Δ)) =
        List.take x.val.val (underlyingList Γ ++ underlyingList Δ) :=
      congrArg (List.take x.val.val) (underlyingList_mul Γ Δ)
    _ = List.take x.val.val (underlyingList Γ) :=
      List.take_append_of_le_length (Nat.le_of_lt x.val.isLt)

theorem after_inl {Γ Δ α : aritySubmonoid} (x : Slot Γ α) :
    after (slotAppend Γ Δ α (Sum.inl x)) = after x * Δ := by
  apply arity_ext
  simp only [after, underlyingList_ofList]
  rw [slotAppend_val_inl]
  calc
    List.drop x.val.val (underlyingList (Γ * Δ)) =
        List.drop x.val.val (underlyingList Γ ++ underlyingList Δ) :=
      congrArg (List.drop x.val.val) (underlyingList_mul Γ Δ)
    _ = List.drop x.val.val (underlyingList Γ) ++ underlyingList Δ :=
      List.drop_append_of_le_length (Nat.le_of_lt x.val.isLt)
    _ = underlyingList (ofList (List.drop x.val.val (underlyingList Γ)) * Δ) := by
      symm
      simpa only [underlyingList_ofList] using
        underlyingList_mul (ofList (List.drop x.val.val (underlyingList Γ))) Δ

theorem before_inr {Γ Δ α : aritySubmonoid} (x : Slot Δ α) :
    before (slotAppend Γ Δ α (Sum.inr x)) = Γ * before x := by
  apply arity_ext
  simp only [before, underlyingList_ofList]
  rw [slotAppend_val_inr]
  calc
    List.take ((underlyingList Γ).length + x.val.val) (underlyingList (Γ * Δ)) =
        List.take ((underlyingList Γ).length + x.val.val)
          (underlyingList Γ ++ underlyingList Δ) :=
      congrArg (List.take _) (underlyingList_mul Γ Δ)
    _ = underlyingList Γ ++ List.take x.val.val (underlyingList Δ) := by
      simp [List.take_append]
    _ = underlyingList (Γ * ofList (List.take x.val.val (underlyingList Δ))) := by
      symm
      simpa only [underlyingList_ofList] using
        underlyingList_mul Γ (ofList (List.take x.val.val (underlyingList Δ)))

theorem after_inr {Γ Δ α : aritySubmonoid} (x : Slot Δ α) :
    after (slotAppend Γ Δ α (Sum.inr x)) = after x := by
  apply arity_ext
  simp only [after, underlyingList_ofList]
  rw [slotAppend_val_inr]
  calc
    List.drop ((underlyingList Γ).length + x.val.val) (underlyingList (Γ * Δ)) =
        List.drop ((underlyingList Γ).length + x.val.val)
          (underlyingList Γ ++ underlyingList Δ) :=
      congrArg (List.drop _) (underlyingList_mul Γ Δ)
    _ = List.drop x.val.val (underlyingList Δ) := by
      simp [List.drop_append]

theorem before_of_lt {Γ α : aritySubmonoid} {x y : Slot Γ α}
    (h : x.val < y.val) :
    ∃ x' : Slot (before y) α,
      before_after y ▸ slotAppend (before y) (after y) α (Sum.inl x') = x := by
  have hxy : x.val.val < y.val.val := h
  have hlen : (underlyingList (before y)).length = y.val.val := by
    simp only [before, underlyingList_ofList, List.length_take]
    omega
  refine ⟨⟨⟨x.val.val, by omega⟩, ?_⟩, ?_⟩
  · have hget : (underlyingList (before y)).get ⟨x.val.val, by omega⟩
        = (underlyingList Γ).get x.val := by
      simp only [before, underlyingList_ofList, List.get_eq_getElem, List.getElem_take]
    rw [hget]
    exact x.property
  · apply Subtype.ext
    apply Fin.ext
    calc
      _ = (slotAppend (before y) (after y) α (Sum.inl _)).val.val :=
        transport_val (before_after y) _
      _ = x.val.val := slotAppend_val_inl _

/-! ### Sizes -/

theorem sizeOf_take_lt : ∀ (ℓ : List Entry) (i : ℕ), i < ℓ.length →
    sizeOf (ℓ.take i) < sizeOf ℓ
  | a :: rest, 0, _ => by
      cases a with
      | mk Δ => simp [Entry.mk.sizeOf_spec]; omega
  | a :: rest, i + 1, h => by
      have := sizeOf_take_lt rest i (by simpa using h)
      simp only [List.take_succ_cons, List.cons.sizeOf_spec]
      omega

/-! ### The carrier -/

/-- The free carrier on lists, with left-to-right precedence. -/
def carrier : Carrier (List Entry) where
  Arity := aritySubmonoid
  slotAt Γ α := positionWellOrder (slotPredicate α) (underlyingList Γ)
  unit_empty _ := ⟨fun x => x.val.elim0⟩
  slotAt_mul := slotAppend
  subWf :=
    Subrelation.wf
      (fun {Δ Γ} h => by
        obtain ⟨x⟩ := h
        exact sub_sizeOf x)
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

/-- A slot injected into the left list retains its position. -/
theorem carrier_inl_val {Γ Δ α : carrier.Arity} (x : Γ ∋ α) :
    ((carrier.inl x : Γ ⋈ Δ ∋ α) : Slot (Γ * Δ) α).val.val = x.val.val :=
  slotAppend_val_inl x

/-- A slot injected into the right list is shifted by the left list's length. -/
theorem carrier_inr_val {Γ Δ α : carrier.Arity} (x : Δ ∋ α) :
    ((carrier.inr x : Γ ⋈ Δ ∋ α) : Slot (Γ * Δ) α).val.val =
      (underlyingList Γ).length + x.val.val :=
  slotAppend_val_inr x

end ListCarrier

/-- The free carrier on lists. -/
abbrev listCarrier : Carrier (List ListCarrier.Entry) :=
  ListCarrier.carrier

/-- The carrier fixed for this development. -/
abbrev C : Carrier (List ListCarrier.Entry) := ListCarrier.carrier

open ListCarrier in
/-- Including a slot into the whole keeps its position. -/
theorem inclusion_val {Δ α β : C.Arity} (y : Δ ∋ α) (x : C.before y ∋ β) :
    ((C.inclusion y x : Δ ∋ β) : Slot Δ β).val.val = (x : Slot _ β).val.val := by
  rw [Carrier.inclusion]
  exact (transport_val _ _).trans (carrier_inl_val x)

open ListCarrier

/-! ### Single-entry arities -/

/-- An arity is determined by its underlying list. -/
theorem ListCarrier.underlyingList_injective {Γ Δ : C.Arity}
    (h : underlyingList Γ = underlyingList Δ) : Γ = Δ := by
  apply Subtype.ext
  funext Θ
  rw [val_apply, val_apply, h]

/-- The arity of a single entry binding `α`. -/
def C.single (α : C.Arity) : C.Arity :=
  ofList [Entry.mk (underlyingList α)]

/-- The underlying list of a single-entry arity. -/
@[simp] theorem C.underlyingList_single (α : C.Arity) :
    underlyingList (C.single α) = [Entry.mk (underlyingList α)] :=
  underlyingList_ofList _

/-- The one slot of a single-entry arity. -/
def C.singleSlot (α : C.Arity) : C.single α ∋ α :=
  ⟨⟨0, by simp⟩, rfl⟩

/-- Reading a position of a one-element list. -/
theorem ListCarrier.get_singleton {ℓ : List Entry} {a : Entry} (hl : ℓ = [a])
    (i : Fin ℓ.length) : ℓ.get i = a := by
  subst hl
  have hi : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
  subst hi
  rfl

/-- A single-entry arity has exactly one slot. -/
theorem C.single_slot_unique {α : C.Arity} (z : C.single α ∋ α) : z = C.singleSlot α := by
  apply Subtype.ext
  apply Fin.ext
  have hlen : (underlyingList (C.single α)).length = 1 :=
    congrArg List.length (C.underlyingList_single α)
  exact Nat.lt_one_iff.mp (hlen ▸ z.val.isLt)

/-- A single-entry arity has slots only at its own binding arity. -/
theorem C.single_arity {α β : C.Arity} (x : C.single α ∋ β) : β = α :=
  (underlyingList_injective
    ((congrArg Entry.arity
      (ListCarrier.get_singleton (C.underlyingList_single α) x.val)).symm.trans
        x.property)).symm
