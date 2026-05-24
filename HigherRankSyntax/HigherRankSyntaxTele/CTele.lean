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

Together with two propositional fields:

* `classify_embed` — classifying an embedded shape-slot returns it via
  the shape-continuation.
* `classify_weaken` — classifying a weakened base-slot returns it via
  the base-continuation.

All three function fields are constructed alongside the shape by `id` /
`cons`, so the walker never inducts on the underlying Tele.  The two
propositional fields are populated alongside, by `nomatch`/`rfl` and by
the recursive proofs.
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
  /-- Reflection: classifying an embedded shape-slot fires the shape continuation. -/
  classify_embed : ∀ (Γ : Shape C) (X : Type) {α : C.Arity} (q_τ : shape ∋ α)
                   (k_shape : (shape ∋ α) → X) (k_Γ : (Γ ∋ α) → X),
                   classify Γ X (embed Γ q_τ) k_shape k_Γ = k_shape q_τ
  /-- Reflection: classifying a weakened base-slot fires the base continuation. -/
  classify_weaken : ∀ (Γ : Shape C) (X : Type) {α : C.Arity} (q_Γ : Γ ∋ α)
                    (k_shape : (shape ∋ α) → X) (k_Γ : (Γ ∋ α) → X),
                    classify Γ X (weaken Γ q_Γ) k_shape k_Γ = k_Γ q_Γ
  /-- Cover (η-rule of the sum decomposition): every slot is either a
  τ-embedded shape-slot or a τ-weakened base-slot. -/
  cover : ∀ (Γ : Shape C) {α : C.Arity} (p : (Γ ⋈* shape) ∋ α),
          (∃ q_τ : shape ∋ α, p = (embed Γ).apply q_τ)
            ∨ (∃ q_Γ : Γ ∋ α, p = (weaken Γ).apply q_Γ)

namespace CTele

/-- The identity CTele: empty shape, identity weakening, vacuous embed,
classifier returning everything to the base. -/
def id {C : Carrier} : CTele C where
  shape := Shape.nil
  weaken := fun Γ => Renaming.id Γ
  embed := fun _Γ => ⟨fun {_} p => nomatch p⟩
  classify := fun _Γ _α _X p _k_shape k_Γ => k_Γ p
  classify_embed := fun _Γ _X _α q_τ _k_shape _k_Γ => nomatch q_τ
  classify_weaken := fun _Γ _X _α _q_Γ _k_shape _k_Γ => rfl
  cover := fun _Γ _α p => Or.inr ⟨p, rfl⟩

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
  classify_embed := fun Γ X _α q_τ k_shape k_Γ => by
    cases q_τ with
    | here _i  => rfl
    | there q' => exact t.classify_embed Γ X q' (fun q_t => k_shape (.there q_t)) k_Γ
  classify_weaken := fun Γ X _α q_Γ k_shape k_Γ' => by
    exact t.classify_weaken Γ X q_Γ (fun q_t => k_shape (.there q_t)) k_Γ'
  cover := fun Γ _α p => by
    cases p with
    | here i  => exact Or.inl ⟨ListSlotAt.here i, rfl⟩
    | there q =>
      rcases t.cover Γ q with ⟨q_τ, h⟩ | ⟨q_Γ, h⟩
      · refine Or.inl ⟨ListSlotAt.there q_τ, ?_⟩
        show ListSlotAt.there q = ListSlotAt.there ((t.embed Γ).apply q_τ)
        congr 1
      · refine Or.inr ⟨q_Γ, ?_⟩
        show ListSlotAt.there q = ListSlotAt.there ((t.weaken Γ).apply q_Γ)
        congr 1

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

/-! ### β/ι reduction lemmas for the concrete constructors

These are `rfl`-provable equations that `simp` can use to reduce
`(CTele.id _).classify _ _ ...` and `(CTele.cons _ _ ).classify _ _ ...`
calls when their slot argument is in constructor form.  The multi-discriminee
match Lean compiles `cons.classify` into doesn't auto-reduce, so we expose
the reductions explicitly.
-/

@[simp] theorem id_classify {C : Carrier} (Γ : Shape C) (X : Type) {α : C.Arity}
    (p : Γ ∋ α) (k_shape : ((CTele.id : CTele C).shape ∋ α) → X) (k_Γ : (Γ ∋ α) → X) :
    (CTele.id : CTele C).classify Γ X p k_shape k_Γ = k_Γ p := rfl

@[simp] theorem cons_classify_here {C : Carrier} (a : C.Arity) (t : CTele C)
    (Γ : Shape C) (X : Type) (i : C.Binder a)
    (k_shape : ((CTele.cons a t).shape ∋ i.arity) → X) (k_Γ : (Γ ∋ i.arity) → X) :
    (CTele.cons a t).classify Γ X (ListSlotAt.here i) k_shape k_Γ
      = k_shape (ListSlotAt.here i) := rfl

@[simp] theorem cons_classify_there {C : Carrier} (a : C.Arity) (t : CTele C)
    (Γ : Shape C) (X : Type) {α : C.Arity} (p : (Γ ⋈* t.shape) ∋ α)
    (k_shape : ((CTele.cons a t).shape ∋ α) → X) (k_Γ : (Γ ∋ α) → X) :
    (CTele.cons a t).classify Γ X (ListSlotAt.there p) k_shape k_Γ
      = t.classify Γ X p (fun q_t => k_shape (.there q_t)) k_Γ := rfl

@[simp] theorem cons_embed_here {C : Carrier} (a : C.Arity) (t : CTele C)
    (Γ : Shape C) (i : C.Binder a) :
    ((CTele.cons a t).embed Γ).apply (ListSlotAt.here i) = .here i := rfl

@[simp] theorem cons_embed_there {C : Carrier} (a : C.Arity) (t : CTele C)
    (Γ : Shape C) {α : C.Arity} (q : t.shape ∋ α) :
    ((CTele.cons a t).embed Γ).apply (ListSlotAt.there q)
      = .there ((t.embed Γ).apply q) := rfl

@[simp] theorem id_weaken {C : Carrier} (Γ : Shape C) {α : C.Arity} (p : Γ ∋ α) :
    ((CTele.id : CTele C).weaken Γ).apply p = p := rfl

@[simp] theorem cons_weaken {C : Carrier} (a : C.Arity) (t : CTele C)
    (Γ : Shape C) {α : C.Arity} (p : Γ ∋ α) :
    ((CTele.cons a t).weaken Γ).apply p = .there ((t.weaken Γ).apply p) := rfl

end CTele
