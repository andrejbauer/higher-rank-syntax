import HigherRankSyntax.Expr
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.SuccPred

/-!
# The list carrier

`listCarrier Ty` is the free simply-typed carrier on a set `Ty` of result
classes: arities are lists of entries, an entry is a pair of a binding
arity and a result class, slots are list positions.
-/

namespace ListCarrier

/-- An entry: a binding arity together with a result class. -/
inductive Entry (Ty : Type) where
  | mk : List (Entry Ty) → Ty → Entry Ty

variable {Ty : Type}

/-- The binding arity of an entry. -/
def Entry.arity : Entry Ty → List (Entry Ty)
  | .mk Δ _ => Δ

/-- The result class of an entry. -/
def Entry.result : Entry Ty → Ty
  | .mk _ τ => τ

theorem Entry.sizeOf_arity_lt (e : Entry Ty) : sizeOf e.arity < sizeOf e := by
  cases e with
  | mk Δ τ => simp only [Entry.arity, Entry.mk.sizeOf_spec]; omega

theorem sizeOf_arity_lt_of_mem {e : Entry Ty} {ℓ : List (Entry Ty)} (h : e ∈ ℓ) :
    sizeOf e.arity < sizeOf ℓ :=
  lt_trans e.sizeOf_arity_lt (List.sizeOf_lt_of_mem h)

/-- Prepending a fixed list, as an endofunction of lists. -/
def prepend (ℓ : List (Entry Ty)) : Function.End (List (Entry Ty)) :=
  fun Θ => ℓ ++ Θ

/-- The arity submonoid: endofunctions of the form `prepend ℓ`. -/
def aritySubmonoid (Ty : Type) : Submonoid (Function.End (List (Entry Ty))) where
  carrier := Set.range prepend
  one_mem' := ⟨[], rfl⟩
  mul_mem' := by
    rintro _ _ ⟨ℓ₁, rfl⟩ ⟨ℓ₂, rfl⟩
    exact ⟨ℓ₁ ++ ℓ₂, funext fun Θ => List.append_assoc ℓ₁ ℓ₂ Θ⟩

/-- The underlying list of an arity. -/
def underlyingList (Γ : aritySubmonoid Ty) : List (Entry Ty) := Γ.val []

theorem val_apply (Γ : aritySubmonoid Ty) (Θ : List (Entry Ty)) :
    Γ.val Θ = underlyingList Γ ++ Θ := by
  obtain ⟨ℓ, h⟩ := Γ.property
  rw [underlyingList, ← h]
  simp [prepend]

theorem underlyingList_one : underlyingList (1 : aritySubmonoid Ty) = [] := rfl

/-- The arity presented by a list. -/
def ofList (ℓ : List (Entry Ty)) : aritySubmonoid Ty :=
  ⟨prepend ℓ, ℓ, rfl⟩

@[simp] theorem underlyingList_ofList (ℓ : List (Entry Ty)) :
    underlyingList (ofList ℓ) = ℓ :=
  List.append_nil ℓ

theorem underlyingList_mul (Γ Δ : aritySubmonoid Ty) :
    underlyingList (Γ * Δ) = underlyingList Γ ++ underlyingList Δ :=
  val_apply Γ (underlyingList Δ)

/-- An arity is determined by its underlying list. -/
theorem arity_ext {Γ Δ : aritySubmonoid Ty}
    (h : underlyingList Γ = underlyingList Δ) : Γ = Δ := by
  apply Subtype.ext
  funext Θ
  rw [val_apply Γ, val_apply Δ, h]

/-- Positions of a list whose entry satisfies a predicate. -/
def Position (P : Entry Ty → Prop) (ℓ : List (Entry Ty)) : Type :=
  { i : Fin ℓ.length // P (ℓ.get i) }

/-- Position order embeds into `ℕ`. -/
def positionEmbedding (P : Entry Ty → Prop) (ℓ : List (Entry Ty)) :
    (fun x y : Position P ℓ => x.val < y.val) ↪r ((· < ·) : ℕ → ℕ → Prop) where
  toFun x := x.val.val
  inj' _ _ h := Subtype.ext (Fin.val_injective h)
  map_rel_iff' := Iff.rfl

instance (P : Entry Ty → Prop) (ℓ : List (Entry Ty)) :
    IsWellOrder (Position P ℓ) (fun x y => x.val < y.val) :=
  (positionEmbedding P ℓ).isWellOrder

/-- The well-order of positions at a predicate. -/
@[reducible] def positionWellOrder (P : Entry Ty → Prop) (ℓ : List (Entry Ty)) : WellOrder :=
  ⟨Position P ℓ, fun x y => x.val < y.val, inferInstance⟩

/-- Transport of position well-orders along a list equation. -/
def positionCongr (P : Entry Ty → Prop) {ℓ ℓ' : List (Entry Ty)} (h : ℓ = ℓ') :
    (positionWellOrder P ℓ).r ≃r (positionWellOrder P ℓ').r := by
  subst h
  exact RelIso.refl _

/-- Transporting a position along a list equality preserves its index. -/
theorem positionCongr_val (P : Entry Ty → Prop) {ℓ ℓ' : List (Entry Ty)}
    (h : ℓ = ℓ') (x : Position P ℓ) :
    ((positionCongr P h x).val.val : ℕ) = x.val.val := by
  subst h
  rfl

private theorem split_index_lt {ℓ₁ ℓ₂ : List (Entry Ty)} (k : Fin (ℓ₁ ++ ℓ₂).length)
    (h : ¬ k.val < ℓ₁.length) : k.val - ℓ₁.length < ℓ₂.length := by
  have hlen : (ℓ₁ ++ ℓ₂).length = ℓ₁.length + ℓ₂.length := List.length_append
  omega

private theorem get_append_left {ℓ₁ ℓ₂ : List (Entry Ty)} (k : Fin (ℓ₁ ++ ℓ₂).length)
    (h : k.val < ℓ₁.length) : (ℓ₁ ++ ℓ₂).get k = ℓ₁.get ⟨k.val, h⟩ := by
  simp [List.get_eq_getElem, List.getElem_append_left h]

private theorem get_append_right {ℓ₁ ℓ₂ : List (Entry Ty)} (k : Fin (ℓ₁ ++ ℓ₂).length)
    (h : ¬ k.val < ℓ₁.length) (hlt : k.val - ℓ₁.length < ℓ₂.length) :
    (ℓ₁ ++ ℓ₂).get k = ℓ₂.get ⟨k.val - ℓ₁.length, hlt⟩ := by
  simp [List.get_eq_getElem, List.getElem_append_right (Nat.le_of_not_lt h)]

private def sumSubtypeEquiv (P : Entry Ty → Prop) (ℓ₁ ℓ₂ : List (Entry Ty)) :
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

private def finAppendEquiv (ℓ₁ ℓ₂ : List (Entry Ty)) :
    Fin ℓ₁.length ⊕ Fin ℓ₂.length ≃ Fin (ℓ₁ ++ ℓ₂).length :=
  finSumFinEquiv.trans
    (finCongr (Eq.symm (List.length_append : (ℓ₁ ++ ℓ₂).length = ℓ₁.length + ℓ₂.length)))

private theorem elim_position_iff (P : Entry Ty → Prop) (ℓ₁ ℓ₂ : List (Entry Ty))
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

private def positionAppendEquiv (P : Entry Ty → Prop) (ℓ₁ ℓ₂ : List (Entry Ty)) :
    Position P ℓ₁ ⊕ Position P ℓ₂ ≃ Position P (ℓ₁ ++ ℓ₂) :=
  (sumSubtypeEquiv P ℓ₁ ℓ₂).trans
    (Equiv.subtypeEquiv (finAppendEquiv ℓ₁ ℓ₂) (elim_position_iff P ℓ₁ ℓ₂))

private theorem positionAppendEquiv_val_inl (P : Entry Ty → Prop) {ℓ₁ ℓ₂ : List (Entry Ty)}
    (y : Position P ℓ₁) :
    ((positionAppendEquiv P ℓ₁ ℓ₂) (Sum.inl y)).val.val = y.val.val :=
  rfl

private theorem positionAppendEquiv_val_inr (P : Entry Ty → Prop) {ℓ₁ ℓ₂ : List (Entry Ty)}
    (y : Position P ℓ₂) :
    ((positionAppendEquiv P ℓ₁ ℓ₂) (Sum.inr y)).val.val = ℓ₁.length + y.val.val :=
  rfl

/-- Positions of a concatenation are the lexicographic sum of positions. -/
def positionAppend (P : Entry Ty → Prop) (ℓ₁ ℓ₂ : List (Entry Ty)) :
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

/-- The slot predicate: matching binding arity and result class. -/
def slotPredicate (α : aritySubmonoid Ty) (τ : Ty) (e : Entry Ty) : Prop :=
  e.arity = underlyingList α ∧ e.result = τ

theorem sub_sizeOf {Δ Γ : aritySubmonoid Ty} {τ : Ty}
    (x : Position (slotPredicate Δ τ) (underlyingList Γ)) :
    sizeOf (underlyingList Δ) < sizeOf (underlyingList Γ) := by
  have hmem : (underlyingList Γ).get x.val ∈ underlyingList Γ :=
    List.get_mem (underlyingList Γ) x.val
  have hlt := sizeOf_arity_lt_of_mem hmem
  rwa [x.property.1] at hlt

/-- The free simply-typed carrier on the class set `Ty`. -/
def carrier (Ty : Type) : Carrier (List (Entry Ty)) where
  Ty := Ty
  Arity := aritySubmonoid Ty
  slotAt Γ α τ := positionWellOrder (slotPredicate α τ) (underlyingList Γ)
  unit_empty _ _ := ⟨fun x => x.val.elim0⟩
  slotAt_mul Γ Δ α τ :=
    (positionAppend (slotPredicate α τ) (underlyingList Γ) (underlyingList Δ)).trans
      (positionCongr (slotPredicate α τ) (underlyingList_mul Γ Δ).symm)
  subWf :=
    Subrelation.wf
      (fun {Δ Γ} h => by
        obtain ⟨τ, ⟨x⟩⟩ := h
        exact sub_sizeOf x)
      (InvImage.wf (fun Γ => sizeOf (underlyingList Γ)) Nat.lt_wfRel.wf)

end ListCarrier

/-- The free simply-typed carrier on the class set `Ty`. -/
abbrev listCarrier (Ty : Type) : Carrier (List (ListCarrier.Entry Ty)) :=
  ListCarrier.carrier Ty

section SmokeTests

example {Ty : Type} (Γ : (listCarrier Ty).Arity) : Ext Γ 1 = Γ := rfl

#check fun (Γ : (listCarrier Unit).Arity) (τ : (listCarrier Unit).Ty) =>
  Expr (C := listCarrier Unit) Γ τ

end SmokeTests
