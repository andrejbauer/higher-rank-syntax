import HigherRankSyntaxSig.Renaming

/-!
# Classifiable Telescopes

`CTele C` bundles a shape (telescope) with the structural data needed to use
it inside the framework: at minimum, a weakening renaming.  All fields are
function-typed so composition is strict via Lean's η.
-/


/-- A classifiable telescope: a shape together with its weakening renaming and a
classifier (bipartition of slots into "in this telescope" vs "in the below"). -/
structure CTele (C : Carrier) where
  /-- The underlying shape (telescope). -/
  shape : Shape C
  /-- Weakening renaming: any shape Γ can be embedded into `Γ ⋈* shape`. -/
  weaken : ∀ (Γ : Shape C), Γ →ʳ Γ ⋈* shape
  /-- Classifier (CPS-style for η-friendly composition): given a slot of
  `Γ ⋈* shape`, dispatch into either a `shape`-slot or a `Γ`-slot via continuations. -/
  classify : (Γ : Shape C) → {α : C.Arity} → (X : Type) →
             ((Γ ⋈* shape) ∋ α) →
             ((shape ∋ α) → X) → ((Γ ∋ α) → X) → X

namespace CTele

/-- The identity CTele: empty shape, identity weakening, vacuous classifier. -/
def id {C : Carrier} : CTele C where
  shape := Shape.nil
  weaken := fun Γ => Renaming.id Γ
  classify := fun _Γ _α _X p _k_shape k_Γ => k_Γ p
  -- shape is Shape.nil = Tele.id, so (Γ ⋈* shape) = Γ; the slot is a Γ-slot

/-- Extend a CTele by one arity at the top. -/
def cons {C : Carrier} (a : C.Arity) (t : CTele C) : CTele C where
  shape := t.shape ⋈ a
  weaken := fun Γ => Renaming.weaken (Γ ⋈* t.shape) a ∘ʳʳ t.weaken Γ
  classify := fun Γ α X p k_shape k_Γ =>
    -- p : (Γ ⋈* (t.shape ⋈ a)) ∋ α reduces to ((Γ ⋈* t.shape) ⋈ a) ∋ α
    match p with
    | .here i  => k_shape (.here i)
    | .there p' => t.classify Γ X p' (fun q_t => k_shape (.there q_t)) k_Γ

-- Composition omitted for now — would require embedding t-slots and s-slots
-- into the composed shape, which is non-trivial without additional structural data
-- carried by the CTele.  Exploring this after `id` and `cons` are working.

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

@[simp] theorem ofList_nil {C : Carrier} : (ofList ([] : List C.Arity)) = (CTele.id : CTele C) := rfl

@[simp] theorem ofList_cons {C : Carrier} (a : C.Arity) (rest : List C.Arity) :
    ofList (a :: rest) = CTele.cons a (ofList rest) := rfl

/-! ### Weaken reductions -/

example {C : Carrier} (Γ : Shape C) : (CTele.id (C := C)).weaken Γ = 𝟙ʳ := rfl

example {C : Carrier} (a : C.Arity) (Γ : Shape C) :
    (CTele.cons a CTele.id).weaken Γ = Renaming.weaken Γ a ∘ʳʳ 𝟙ʳ := rfl

example {C : Carrier} (a : C.Arity) (Γ : Shape C) :
    (CTele.cons a CTele.id).weaken Γ = Renaming.weaken Γ a := rfl

/-! ### `ofList` and shape -/

example {C : Carrier} (a : C.Arity) :
    (CTele.ofList [a] : CTele C).shape = Shape.nil ⋈ a := rfl

example {C : Carrier} (a b : C.Arity) :
    (CTele.ofList [a, b] : CTele C).shape = Shape.nil ⋈ b ⋈ a := rfl

end CTele



