import HigherRankSyntax.PrefixedSyntaxMonad
import ListCarrier

/-!
# The magma signature

The signature of magmas over the list carrier at the class set `Unit`: one
binary operation slot and the variable contexts `variableContext n`.
-/

namespace Magmas

open ListCarrier

universe u

/-- The carrier of the magma example: the list carrier at one class. -/
abbrev magmaCarrier : Carrier (List (Entry Unit)) := listCarrier Unit

/-- The entry shape with no arguments: ordinary variables. -/
def nullaryEntry : Entry Unit := .mk [] ()

/-- The entry shape with two arguments: the shape of multiplication. -/
def binaryEntry : Entry Unit := .mk [nullaryEntry, nullaryEntry] ()

/-- The magma signature: its sole slot is multiplication. -/
def magmaSignature : magmaCarrier.Arity :=
  ofList [binaryEntry]

/-- The context of `n` ordinary variables. -/
def variableContext (n : ℕ) : magmaCarrier.Arity :=
  ofList (List.replicate n nullaryEntry)

@[simp] theorem magmaArity_right_unit (Γ : magmaCarrier.Arity) :
    Γ ⋈ (1 : magmaCarrier.Arity) = Γ := rfl

/-- The fixed-prefix relative monad for the magma signature. -/
def magmaPrefixedSyntaxMonad : RelativeMonad (J magmaCarrier) :=
  PrefixedSyntaxMonad magmaCarrier magmaSignature

/-- The multiplication slot of the signature. -/
def multiplicationSlot : magmaSignature ∋[()] variableContext 2 :=
  ⟨⟨0, by decide⟩, ⟨rfl, rfl⟩⟩

theorem variableContext_list (n : ℕ) :
    List.replicate n nullaryEntry = underlyingList (variableContext n) := by
  simp [variableContext]

/-- The `j`-th variable of the context `variableContext n`. -/
def variableSlot (n : ℕ) (j : Fin n) :
    variableContext n ∋[()] (1 : magmaCarrier.Arity) :=
  (positionCongr (slotPredicate 1 ()) (variableContext_list n))
    ⟨⟨j.val, by simp⟩, by
      simp [slotPredicate, List.get_eq_getElem, List.getElem_replicate,
        nullaryEntry, Entry.arity, Entry.result, underlyingList_one]⟩

/-- The underlying list position of a variable slot. -/
theorem variableSlot_val (n : ℕ) (j : Fin n) :
    (variableSlot n j).val.val = j.val := by
  apply positionCongr_val

/-- The underlying list position of the multiplication slot. -/
theorem multiplicationSlot_val : multiplicationSlot.val.val = 0 := rfl

/-- Every slot of the magma signature has the binary binding arity. -/
theorem signatureSlot_arity {α : magmaCarrier.Arity}
    (x : magmaSignature ∋[()] α) : α = variableContext 2 := by
  apply arity_ext
  have h : underlyingList α = [nullaryEntry, nullaryEntry] := by
    symm
    simpa [magmaSignature, List.get_eq_getElem, binaryEntry,
      Entry.arity, Entry.result] using x.property.1
  rw [h, variableContext]
  simp

/-- Eliminate a slot of the magma signature as its unique multiplication slot. -/
def signatureSlot_cases
    {motive : ∀ {α : magmaCarrier.Arity}, magmaSignature ∋[()] α → Sort u}
    (multiplication : motive multiplicationSlot)
    {α : magmaCarrier.Arity} (x : magmaSignature ∋[()] α) : motive x := by
  have hα := signatureSlot_arity x
  subst α
  have h : x = multiplicationSlot := by
    apply Subtype.ext
    apply Fin.ext
    have hlt := x.val.isLt
    simp only [magmaSignature, underlyingList_ofList, List.length_cons,
      List.length_nil] at hlt
    rw [multiplicationSlot_val]
    omega
  rw [h]
  exact multiplication

/-- The sole signature slot is multiplication. -/
theorem signatureSlot_eq (x : magmaSignature ∋[()] variableContext 2) :
    x = multiplicationSlot := by
  apply Subtype.ext
  apply Fin.ext
  have hlt := x.val.isLt
  simp only [magmaSignature, underlyingList_ofList, List.length_cons,
    List.length_nil] at hlt
  rw [multiplicationSlot_val]
  omega

/-- Every slot of a variable context has nullary binding arity. -/
theorem variableSlot_arity (n : ℕ) {α : magmaCarrier.Arity}
    (x : variableContext n ∋[()] α) : α = 1 := by
  apply arity_ext
  have h : underlyingList α = [] := by
    symm
    simpa [variableContext, List.get_eq_getElem, List.getElem_replicate,
      nullaryEntry, Entry.arity, Entry.result] using x.property.1
  rw [h]
  exact underlyingList_one.symm

/-- Eliminate a variable-context slot as one of its ordinary variables. -/
def variableSlot_cases (n : ℕ)
    {motive : ∀ {α : magmaCarrier.Arity}, variableContext n ∋[()] α → Sort u}
    (variableCase : ∀ j : Fin n, motive (variableSlot n j))
    {α : magmaCarrier.Arity} (x : variableContext n ∋[()] α) : motive x := by
  have hα := variableSlot_arity n x
  subst α
  let j : Fin n := ⟨x.val.val, by
    have hlt := x.val.isLt
    simpa [variableContext] using hlt⟩
  have h : x = variableSlot n j := by
    apply Subtype.ext
    apply Fin.ext
    rw [variableSlot_val]
  rw [h]
  exact variableCase j

/-- The finite index of a variable-context slot. -/
def variableSlotIndex (n : ℕ) {α : magmaCarrier.Arity}
    (x : variableContext n ∋[()] α) : Fin n :=
  ⟨x.val.val, by
    have hlt := x.val.isLt
    simpa [variableContext] using hlt⟩

@[simp] theorem variableSlotIndex_variableSlot (n : ℕ) (j : Fin n) :
    variableSlotIndex n (variableSlot n j) = j := by
  apply Fin.ext
  exact variableSlot_val n j

theorem variableSlot_eq_variableSlotIndex (n : ℕ)
    (x : variableContext n ∋[()] (1 : magmaCarrier.Arity)) :
    x = variableSlot n (variableSlotIndex n x) := by
  apply Subtype.ext
  apply Fin.ext
  rw [variableSlot_val]
  rfl

/-- Eliminate a multiplication argument as its left or right position. -/
def multiplicationArgument_cases
    {motive : ∀ {α : magmaCarrier.Arity}, variableContext 2 ∋[()] α → Sort u}
    (left : motive (variableSlot 2 ⟨0, by decide⟩))
    (right : motive (variableSlot 2 ⟨1, by decide⟩))
    {α : magmaCarrier.Arity} (x : variableContext 2 ∋[()] α) : motive x := by
  apply variableSlot_cases 2 (motive := motive)
  intro j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j
  · exact left
  · exact right

/-- The expression `x j`, the `j`-th variable as an expression. -/
def variableExpression (n : ℕ) (j : Fin n) :
    Expr (C := magmaCarrier) (magmaSignature ⋈ variableContext n) () :=
  Expr.η (Γ := magmaSignature ⋈ variableContext n) (α := 1)
    (magmaCarrier.inr (variableSlot n j))

/-- The two argument expressions of a multiplication application. -/
def multiplicationArguments (n : ℕ)
    (e f : Expr (C := magmaCarrier) (magmaSignature ⋈ variableContext n) ()) :
    Expr.Args (magmaSignature ⋈ variableContext n) (variableContext 2) :=
  fun {_} {σ} i =>
    match σ with
    | () =>
      multiplicationArgument_cases
        (motive := fun {Δ} _ => Expr (magmaSignature ⋈ variableContext n ⋈ Δ) ())
        e f
        i

/-- The expression obtained by applying multiplication to two expressions. -/
def multiplicationExpression (n : ℕ)
    (e f : Expr (C := magmaCarrier) (magmaSignature ⋈ variableContext n) ()) :
    Expr (magmaSignature ⋈ variableContext n) () :=
  .ap (magmaCarrier.inl multiplicationSlot) (multiplicationArguments n e f)

@[simp] theorem multiplicationArguments_left (n : ℕ)
    (e f : Expr (C := magmaCarrier) (magmaSignature ⋈ variableContext n) ()) :
    multiplicationArguments n e f (variableSlot 2 ⟨0, by decide⟩) = e := by
  unfold multiplicationArguments
  rfl

@[simp] theorem multiplicationArguments_right (n : ℕ)
    (e f : Expr (C := magmaCarrier) (magmaSignature ⋈ variableContext n) ()) :
    multiplicationArguments n e f (variableSlot 2 ⟨1, by decide⟩) = f := by
  unfold multiplicationArguments
  rfl

end Magmas
