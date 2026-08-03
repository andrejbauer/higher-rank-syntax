import HigherRankSyntax.Typing.Decoration
import ListCarrier

/-!
# Precedence for the list carrier

The prefix of a list slot is the segment strictly before its position.
-/

namespace ListCarrier

variable {Ty : Type}

/-- The list segment preceding a slot. -/
def before {Γ α : (listCarrier Ty).Arity} {τ : Ty}
    (x : Γ ∋[τ] α) : (listCarrier Ty).Arity :=
  ofList ((underlyingList Γ).take x.val.val)

/-- The list segment beginning at a slot. -/
def after {Γ α : (listCarrier Ty).Arity} {τ : Ty}
    (x : Γ ∋[τ] α) : (listCarrier Ty).Arity :=
  ofList ((underlyingList Γ).drop x.val.val)

theorem before_after {Γ α : (listCarrier Ty).Arity} {τ : Ty}
    (x : Γ ∋[τ] α) : before x ⋈ after x = Γ := by
  apply arity_ext
  calc
    underlyingList (before x ⋈ after x) =
        underlyingList (before x) ++ underlyingList (after x) :=
      underlyingList_mul (before x) (after x)
    _ = List.take x.val.val (underlyingList Γ) ++
        List.drop x.val.val (underlyingList Γ) := by
      simp [before, after]
    _ = underlyingList Γ := List.take_append_drop _ _

private def localized {Γ α : (listCarrier Ty).Arity} {τ : Ty}
    (x : Γ ∋[τ] α) : after x ∋[τ] α := by
  refine ⟨⟨0, ?_⟩, ?_⟩
  · simp [after]
    omega
  · simpa [after, slotPredicate, List.get_eq_getElem] using x.property

private theorem transport_val {Γ Δ α : (listCarrier Ty).Arity} {τ : Ty}
    (h : Γ = Δ) (x : Γ ∋[τ] α) :
    (h ▸ x : Δ ∋[τ] α).val.val = x.val.val := by
  subst h
  rfl

private theorem reinject {Γ α : (listCarrier Ty).Arity} {τ : Ty}
    (x : Γ ∋[τ] α) :
    before_after x ▸ (listCarrier Ty).inr (localized x) = x := by
  apply Subtype.ext
  apply Fin.ext
  calc
    (before_after x ▸ (listCarrier Ty).inr (localized x) : Γ ∋[τ] α).val.val =
        ((listCarrier Ty).inr (localized x) : before x ⋈ after x ∋[τ] α).val.val :=
      transport_val (before_after x) _
    _ = (underlyingList (before x)).length + (localized x).val.val :=
      carrier_inr_val (localized x)
    _ = x.val.val := by
      simp [before, localized]

private theorem before_inl {Γ Δ α : (listCarrier Ty).Arity} {τ : Ty}
    (x : Γ ∋[τ] α) :
    before ((listCarrier Ty).inl x : Γ ⋈ Δ ∋[τ] α) = before x := by
  apply arity_ext
  simp only [before, underlyingList_ofList, carrier_inl_val]
  calc
    List.take x.val.val (underlyingList (Γ ⋈ Δ)) =
        List.take x.val.val (underlyingList Γ ++ underlyingList Δ) :=
      congrArg (List.take x.val.val) (underlyingList_mul Γ Δ)
    _ = List.take x.val.val (underlyingList Γ) :=
      List.take_append_of_le_length (Nat.le_of_lt x.val.isLt)

private theorem after_inl {Γ Δ α : (listCarrier Ty).Arity} {τ : Ty}
    (x : Γ ∋[τ] α) :
    after ((listCarrier Ty).inl x : Γ ⋈ Δ ∋[τ] α) = after x ⋈ Δ := by
  apply arity_ext
  simp only [after, underlyingList_ofList, carrier_inl_val]
  calc
    List.drop x.val.val (underlyingList (Γ ⋈ Δ)) =
        List.drop x.val.val (underlyingList Γ ++ underlyingList Δ) :=
      congrArg (List.drop x.val.val) (underlyingList_mul Γ Δ)
    _ = List.drop x.val.val (underlyingList Γ) ++ underlyingList Δ :=
      List.drop_append_of_le_length (Nat.le_of_lt x.val.isLt)
    _ = underlyingList (ofList (List.drop x.val.val (underlyingList Γ)) ⋈ Δ) := by
      symm
      simpa only [Ext, underlyingList_ofList] using
        underlyingList_mul (ofList (List.drop x.val.val (underlyingList Γ))) Δ

private theorem before_inr {Γ Δ α : (listCarrier Ty).Arity} {τ : Ty}
    (x : Δ ∋[τ] α) :
    before ((listCarrier Ty).inr x : Γ ⋈ Δ ∋[τ] α) = Γ ⋈ before x := by
  apply arity_ext
  simp only [before, underlyingList_ofList, carrier_inr_val]
  calc
    List.take ((underlyingList Γ).length + x.val.val) (underlyingList (Γ ⋈ Δ)) =
        List.take ((underlyingList Γ).length + x.val.val)
          (underlyingList Γ ++ underlyingList Δ) :=
      congrArg (List.take _) (underlyingList_mul Γ Δ)
    _ = underlyingList Γ ++ List.take x.val.val (underlyingList Δ) := by
      simp [List.take_append]
    _ = underlyingList (Γ ⋈ ofList (List.take x.val.val (underlyingList Δ))) := by
      symm
      simpa only [Ext, underlyingList_ofList] using
        underlyingList_mul Γ (ofList (List.take x.val.val (underlyingList Δ)))

private theorem after_inr {Γ Δ α : (listCarrier Ty).Arity} {τ : Ty}
    (x : Δ ∋[τ] α) :
    after ((listCarrier Ty).inr x : Γ ⋈ Δ ∋[τ] α) = after x := by
  apply arity_ext
  simp only [after, underlyingList_ofList, carrier_inr_val]
  calc
    List.drop ((underlyingList Γ).length + x.val.val) (underlyingList (Γ ⋈ Δ)) =
        List.drop ((underlyingList Γ).length + x.val.val)
          (underlyingList Γ ++ underlyingList Δ) :=
      congrArg (List.drop _) (underlyingList_mul Γ Δ)
    _ = List.drop x.val.val (underlyingList Δ) := by
      simp [List.drop_append]

/-- The canonical left-to-right precedence of list positions. -/
instance : Precedence (listCarrier Ty) where
  before := before
  after := after
  factor := before_after
  localized := localized
  reinject := reinject
  before_inl := before_inl
  after_inl := after_inl
  before_inr := before_inr
  after_inr := after_inr

end ListCarrier
