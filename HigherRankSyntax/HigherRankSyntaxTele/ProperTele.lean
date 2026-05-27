import HigherRankSyntaxTele.Renaming

/-!
# Proper Telescopes (`ProperTele`)

A type class on `Tele C.Arity` exhibiting `Γ ⋈* S` as the coproduct
`Γ + S` (per arity), providing the structural ops needed to dispatch a
slot of `Γ ⋈* S` between the Γ-side and the S-side:

* `inl Γ` — left injection of the base `Γ` into `Γ ⋈* S` (the traditional
  weakening Γ ↪ Γ ⋈* S).
* `inr Γ` — right injection of the telescope `S` into `Γ ⋈* S`.
* `classify Γ` — CPS dispatch of a `(Γ ⋈* S)`-slot to either side.
* `classify_inr`, `classify_inl` — reflection lemmas.
* `cover` — every slot is in the image of exactly one of `inl`, `inr`
  (the propositional inverse of `classify`, needed to case-split a slot
  into its two possible forms when proving equations).

Two instances are declared:

* `Tele.id` — trivial (no S-slots).
* `Tele.cons a ∘ᵗ T` from `[ProperTele T]` — extend by one binder.

Tele equality is unchanged by the class — instances live in the
instance slot, not in Tele's data, so the strict-monoid laws on Tele
(`id_comp`, `comp_id`, `comp_assoc`) keep their `rfl` proofs.
-/


/-- A `ProperTele` instance exhibits `Γ ⋈* S` as the coproduct `Γ + S`
(fibrewise per arity): two injection renamings and a classifier, so that
a slot of `Γ ⋈* S` dispatches uniformly between Γ-slots and S-slots. -/
class ProperTele {C : Carrier} (S : Tele C.Arity) : Type 1 where
  /-- Left injection: the base shape `Γ` into `Γ ⋈* S` — the traditional
  weakening Γ ↪ Γ ⋈* S. -/
  inl : (Γ : Shape C) → Γ →ʳ Γ ⋈* S
  /-- Right injection: the telescope's own shape `S` into `Γ ⋈* S`. -/
  inr : (Γ : Shape C) → S →ʳ Γ ⋈* S
  /-- Classifier (CPS): dispatch a slot of `Γ ⋈* S` into either an S-slot
  or a Γ-slot. -/
  classify : (Γ : Shape C) → {α : C.Arity} → (X : Type) →
             Γ ⋈* S ∋ α →
             (S ∋ α → X) → (Γ ∋ α → X) → X
  /-- Reflection: classifying a right-injected S-slot fires the S-continuation. -/
  classify_inr : ∀ (Γ : Shape C) (X : Type) {α : C.Arity} (x : S ∋ α)
                   (f : S ∋ α → X) (g : Γ ∋ α → X),
                   classify Γ X (inr Γ x) f g = f x
  /-- Reflection: classifying a left-injected Γ-slot fires the Γ-continuation. -/
  classify_inl : ∀ (Γ : Shape C) (X : Type) {α : C.Arity} (y : Γ ∋ α)
                    (f : S ∋ α → X) (g : Γ ∋ α → X),
                    classify Γ X (inl Γ y) f g = g y
  /-- Cover: every slot is in the image of `inr` or `inl`. -/
  cover : ∀ (Γ : Shape C) {α : C.Arity} (p : Γ ⋈* S ∋ α),
          (∃ x : S ∋ α, p = (inr Γ).apply x)
            ∨ (∃ y : Γ ∋ α, p = (inl Γ).apply y)
  /-- The right injection at empty base is the identity renaming. -/
  inr_nil_id : ∀ {α : C.Arity} (x : S ∋ α),
    (inr Shape.nil).apply x = x

namespace ProperTele

/-- The identity telescope: empty; the classifier returns everything to Γ. -/
instance instId {C : Carrier} : ProperTele (Tele.id : Tele C.Arity) where
  inl := fun Γ => Renaming.id Γ
  inr := fun _Γ => ⟨fun {_} p => nomatch p⟩
  classify := fun _Γ _α _X p _f g => g p
  classify_inr := fun _Γ _X _α x _f _g => nomatch x
  classify_inl := fun _Γ _X _α _y _f _g => rfl
  cover := fun _Γ _α p => Or.inr ⟨p, rfl⟩
  inr_nil_id := fun x => nomatch x

/-- Extend a `ProperTele` by one arity at the top. -/
instance instCons {C : Carrier} (a : C.Arity) (T : Tele C.Arity) [ProperTele T] :
    ProperTele (Tele.cons a ∘ᵗ T) where
  inl := fun Γ => ⟨fun {_} p => .there ((ProperTele.inl Γ).apply p)⟩
  inr := fun Γ => ⟨fun {_} p =>
    match p with
    | .here i  => .here i
    | .there x => .there ((ProperTele.inr Γ).apply x)⟩
  classify := fun Γ _α X p f g =>
    match p with
    | .here i   => f (.here i)
    | .there p' => ProperTele.classify Γ X p'
                     (fun y => f (.there y)) g
  classify_inr := fun Γ X _α x f g => by
    cases x with
    | here _i  => rfl
    | there x' =>
      exact ProperTele.classify_inr Γ X x'
              (fun y => f (.there y)) g
  classify_inl := fun Γ X _α y f g => by
    exact ProperTele.classify_inl Γ X y
            (fun z => f (.there z)) g
  cover := fun Γ _α p => by
    cases p with
    | here i  => exact Or.inl ⟨ListSlotAt.here i, rfl⟩
    | there p' =>
      rcases ProperTele.cover Γ p' with ⟨x, h⟩ | ⟨y, h⟩
      · refine Or.inl ⟨ListSlotAt.there x, ?_⟩
        show ListSlotAt.there p' = ListSlotAt.there ((ProperTele.inr Γ).apply x)
        congr 1
      · refine Or.inr ⟨y, ?_⟩
        show ListSlotAt.there p' = ListSlotAt.there ((ProperTele.inl Γ).apply y)
        congr 1
  inr_nil_id := fun x => by
    cases x with
    | here _i => rfl
    | there x' =>
      show ListSlotAt.there ((ProperTele.inr Shape.nil).apply x') = .there x'
      rw [ProperTele.inr_nil_id x']

/-- A singleton telescope.  Definitionally the same shape as
`Tele.cons a ∘ᵗ Tele.id`; provided directly so instance search finds it
once strict unit reduction has simplified the telescope to `Tele.cons a`. -/
instance instSingleton {C : Carrier} (a : C.Arity) :
    ProperTele (Tele.cons a : Tele C.Arity) :=
  inferInstanceAs (ProperTele (Tele.cons a ∘ᵗ (Tele.id : Tele C.Arity)))

end ProperTele
