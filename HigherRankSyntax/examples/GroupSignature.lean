import ListCarrier

/-!
# The group signature

The theory of groups as a signature over the list carrier at the class set
`Unit`: three entries (the declaration shapes with zero, two, and one
argument), the signature `groupSignature` with slots `u`, `m`, `i`, and the
variable contexts `variableContext n`.
-/

namespace Groups

open ListCarrier

/-- The carrier of the group example: the list carrier at one class. -/
abbrev groupCarrier : Carrier (List (Entry Unit)) := listCarrier Unit

/-- The entry shape with no arguments: variables, and the shape of `u`. -/
def nullaryEntry : Entry Unit := .mk [] ()

/-- The entry shape with one argument: the shape of `i`. -/
def unaryEntry : Entry Unit := .mk [nullaryEntry] ()

/-- The entry shape with two arguments: the shape of `m`. -/
def binaryEntry : Entry Unit := .mk [nullaryEntry, nullaryEntry] ()

/-- The group signature: slots `u`, `m`, `i` in this order. -/
def groupSignature : groupCarrier.Arity :=
  ofList [nullaryEntry, binaryEntry, unaryEntry]

/-- The context of `n` ordinary variables. -/
def variableContext (n : ℕ) : groupCarrier.Arity :=
  ofList (List.replicate n nullaryEntry)

/-- The `u`-slot of the signature. -/
def unitSlot : groupSignature ∋[()] (1 : groupCarrier.Arity) :=
  ⟨⟨0, by decide⟩, ⟨rfl, rfl⟩⟩

/-- The `m`-slot of the signature. -/
def multiplicationSlot : groupSignature ∋[()] variableContext 2 :=
  ⟨⟨1, by decide⟩, ⟨rfl, rfl⟩⟩

/-- The `i`-slot of the signature. -/
def inversionSlot : groupSignature ∋[()] variableContext 1 :=
  ⟨⟨2, by decide⟩, ⟨rfl, rfl⟩⟩

theorem variableContext_list (n : ℕ) :
    List.replicate n nullaryEntry = underlyingList (variableContext n) := by
  simp [variableContext]

/-- The `j`-th variable of the context `variableContext n`. -/
def variableSlot (n : ℕ) (j : Fin n) :
    variableContext n ∋[()] (1 : groupCarrier.Arity) :=
  (positionCongr (slotPredicate 1 ()) (variableContext_list n))
    ⟨⟨j.val, by simp⟩, by
      simp [slotPredicate, List.get_eq_getElem, List.getElem_replicate,
        nullaryEntry, Entry.arity, Entry.result, underlyingList_one]⟩

section SmokeTests

/-- The expression `u`, over the signature extended by `n` variables. -/
def unitExpression (n : ℕ) :
    Expr (C := groupCarrier) (groupSignature ⋈ variableContext n) () :=
  .ap (groupCarrier.inl unitSlot) (fun {_} {_} i => (groupCarrier.unit_is_empty i).elim)

/-- The expression `x j`, the `j`-th variable as an expression. -/
def variableExpression (n : ℕ) (j : Fin n) :
    Expr (C := groupCarrier) (groupSignature ⋈ variableContext n) () :=
  Expr.η (Γ := groupSignature ⋈ variableContext n) (α := 1)
    (groupCarrier.inr (variableSlot n j))

end SmokeTests

end Groups
