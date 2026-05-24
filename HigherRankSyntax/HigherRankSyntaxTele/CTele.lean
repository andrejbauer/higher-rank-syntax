import HigherRankSyntaxTele.Renaming

/-!
# Classifiable Telescopes

`CTele C` bundles a shape with three function-typed renaming-style fields:

* `weaken` — `(Γ : Shape C) → Γ →ʳ Γ ⋈* shape` — embeds the base into the
  extended shape.
* `embed` — `(Γ : Shape C) → shape →ʳ Γ ⋈* shape` — embeds the telescope's
  own shape into the extended shape.
* `classify` — CPS dispatch of a slot of `Γ ⋈* shape` into either a
  `shape`-slot or a `Γ`-slot.

All three are *function-typed* and constructed alongside the shape by
`id` / `cons`, so the walker never inducts on the underlying Tele.
-/


/-- A classifiable telescope. -/
structure CTele (C : Carrier) where
  /-- The underlying shape (telescope). -/
  shape : Shape C
  /-- Weakening: embed the base shape into the extended shape. -/
  weaken : (Γ : Shape C) → Γ →ʳ Γ ⋈* shape
  /-- Embedding: embed the telescope's own shape into the extended shape. -/
  embed : (Γ : Shape C) → shape →ʳ Γ ⋈* shape
  /-- Classifier (CPS-style): dispatch a slot of `Γ ⋈* shape` into either a
  `shape`-slot or a `Γ`-slot. -/
  classify : (Γ : Shape C) → {α : C.Arity} → (X : Type) →
             ((Γ ⋈* shape) ∋ α) →
             ((shape ∋ α) → X) → ((Γ ∋ α) → X) → X

namespace CTele

/-- The identity CTele: empty shape, identity weakening, vacuous embed,
classifier returning everything to the base. -/
def id {C : Carrier} : CTele C where
  shape := Shape.nil
  weaken := fun Γ => Renaming.id Γ
  embed := fun _Γ => ⟨fun {_} p => nomatch p⟩
  classify := fun _Γ _α _X p _k_shape k_Γ => k_Γ p

/-- Extend a CTele by one arity at the top. -/
def cons {C : Carrier} (a : C.Arity) (t : CTele C) : CTele C where
  shape := t.shape ⋈ a
  weaken := fun Γ => ⟨fun {_} p => .there (t.weaken Γ p)⟩
  embed := fun Γ => ⟨fun {_} p =>
    match p with
    | .here i  => .here i
    | .there q => .there (t.embed Γ q)⟩
  classify := fun Γ _α X p k_shape k_Γ =>
    match p with
    | .here i  => k_shape (.here i)
    | .there p' => t.classify Γ X p' (fun q_t => k_shape (.there q_t)) k_Γ

/-! ### Construction from a list of arities -/

/-- Build a CTele from a list of arities (the head of the list is the outermost
extension). -/
def ofList {C : Carrier} : List C.Arity → CTele C
  | []        => CTele.id
  | a :: rest => CTele.cons a (ofList rest)

/-! ### Some sanity checks -/

@[simp] theorem id_shape {C : Carrier} : (CTele.id : CTele C).shape = Shape.nil := rfl

@[simp] theorem cons_shape {C : Carrier} (a : C.Arity) (t : CTele C) :
    (CTele.cons a t).shape = t.shape ⋈ a := rfl

@[simp] theorem ofList_nil {C : Carrier} :
    (ofList ([] : List C.Arity)) = (CTele.id : CTele C) := rfl

@[simp] theorem ofList_cons {C : Carrier} (a : C.Arity) (rest : List C.Arity) :
    ofList (a :: rest) = CTele.cons a (ofList rest) := rfl

end CTele
