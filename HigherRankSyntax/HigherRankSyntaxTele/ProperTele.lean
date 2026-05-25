import HigherRankSyntaxTele.Renaming

/-!
# Proper Telescopes (`ProperTele`)

A type class on `Tele C.Arity` providing the structural ops needed to
dispatch slots of `Γ ⋈* S` between S-side and Γ-side:

* `weaken Γ` — embeds Γ into `Γ ⋈* S`.
* `embed Γ`  — embeds S into `Γ ⋈* S`.
* `classify Γ` — CPS dispatch of a `(Γ ⋈* S)`-slot to either side.
* `classify_embed`, `classify_weaken` — reflection lemmas.
* `cover` — every slot is in the image of exactly one of `weaken`, `embed`
  (the propositional inverse of `classify`, needed to case-split a slot
  into its two possible forms when proving equations).

Two instances are declared:

* `Tele.id` — trivial (no S-slots).
* `Tele.cons a ∘ᵗ T` from `[ProperTele T]` — extend by one binder.

Tele equality is unchanged by the class — instances live in the
instance slot, not in Tele's data, so the strict-monoid laws on Tele
(`id_comp`, `comp_id`, `comp_assoc`) keep their `rfl` proofs.
-/


/-- A `ProperTele` instance equips a telescope with classifier and
weaken/embed renamings so that a slot of `Γ ⋈* S` dispatches uniformly
between S-slots and Γ-slots. -/
class ProperTele {C : Carrier} (S : Tele C.Arity) : Type 1 where
  /-- Weakening: embed the base shape into the extended shape. -/
  weaken : (Γ : Shape C) → Γ →ʳ Γ ⋈* S
  /-- Embedding: embed the telescope's own shape into the extended shape. -/
  embed : (Γ : Shape C) → S →ʳ Γ ⋈* S
  /-- Classifier (CPS): dispatch a slot of `Γ ⋈* S` into either an S-slot
  or a Γ-slot. -/
  classify : (Γ : Shape C) → {α : C.Arity} → (X : Type) →
             Γ ⋈* S ∋ α →
             (S ∋ α → X) → (Γ ∋ α → X) → X
  /-- Reflection: classifying an embedded S-slot fires the S-continuation. -/
  classify_embed : ∀ (Γ : Shape C) (X : Type) {α : C.Arity} (x : S ∋ α)
                   (f : S ∋ α → X) (g : Γ ∋ α → X),
                   classify Γ X (embed Γ x) f g = f x
  /-- Reflection: classifying a weakened Γ-slot fires the Γ-continuation. -/
  classify_weaken : ∀ (Γ : Shape C) (X : Type) {α : C.Arity} (y : Γ ∋ α)
                    (f : S ∋ α → X) (g : Γ ∋ α → X),
                    classify Γ X (weaken Γ y) f g = g y
  /-- Cover: every slot is in the image of `embed` or `weaken`. -/
  cover : ∀ (Γ : Shape C) {α : C.Arity} (p : Γ ⋈* S ∋ α),
          (∃ x : S ∋ α, p = (embed Γ).apply x)
            ∨ (∃ y : Γ ∋ α, p = (weaken Γ).apply y)
  /-- The S-side embedding at empty base is the identity renaming. -/
  embed_nil_id : ∀ {α : C.Arity} (x : S ∋ α),
    (embed Shape.nil).apply x = x

namespace ProperTele

/-- The identity telescope: empty, classifier returns everything to Γ. -/
instance instId {C : Carrier} : ProperTele (Tele.id : Tele C.Arity) where
  weaken := fun Γ => Renaming.id Γ
  embed := fun _Γ => ⟨fun {_} p => nomatch p⟩
  classify := fun _Γ _α _X p _f g => g p
  classify_embed := fun _Γ _X _α x _f _g => nomatch x
  classify_weaken := fun _Γ _X _α _y _f _g => rfl
  cover := fun _Γ _α p => Or.inr ⟨p, rfl⟩
  embed_nil_id := fun x => nomatch x

/-- Extend a `ProperTele` by one arity at the top. -/
instance instCons {C : Carrier} (a : C.Arity) (T : Tele C.Arity) [ProperTele T] :
    ProperTele (Tele.cons a ∘ᵗ T) where
  weaken := fun Γ => ⟨fun {_} p => .there ((ProperTele.weaken Γ).apply p)⟩
  embed := fun Γ => ⟨fun {_} p =>
    match p with
    | .here i  => .here i
    | .there x => .there ((ProperTele.embed Γ).apply x)⟩
  classify := fun Γ _α X p f g =>
    match p with
    | .here i   => f (.here i)
    | .there p' => ProperTele.classify Γ X p'
                     (fun y => f (.there y)) g
  classify_embed := fun Γ X _α x f g => by
    cases x with
    | here _i  => rfl
    | there x' =>
      exact ProperTele.classify_embed Γ X x'
              (fun y => f (.there y)) g
  classify_weaken := fun Γ X _α y f g => by
    exact ProperTele.classify_weaken Γ X y
            (fun z => f (.there z)) g
  cover := fun Γ _α p => by
    cases p with
    | here i  => exact Or.inl ⟨ListSlotAt.here i, rfl⟩
    | there p' =>
      rcases ProperTele.cover Γ p' with ⟨x, h⟩ | ⟨y, h⟩
      · refine Or.inl ⟨ListSlotAt.there x, ?_⟩
        show ListSlotAt.there p' = ListSlotAt.there ((ProperTele.embed Γ).apply x)
        congr 1
      · refine Or.inr ⟨y, ?_⟩
        show ListSlotAt.there p' = ListSlotAt.there ((ProperTele.weaken Γ).apply y)
        congr 1
  embed_nil_id := fun x => by
    cases x with
    | here _i => rfl
    | there x' =>
      show ListSlotAt.there ((ProperTele.embed Shape.nil).apply x') = .there x'
      rw [ProperTele.embed_nil_id x']

/-- A singleton telescope.  This is definitionally the same shape as
`Tele.cons a ∘ᵗ Tele.id`, but adding the direct instance helps typeclass search
after strict unit reduction has simplified the telescope to `Tele.cons a`. -/
instance instSingleton {C : Carrier} (a : C.Arity) :
    ProperTele (Tele.cons a : Tele C.Arity) :=
  inferInstanceAs (ProperTele (Tele.cons a ∘ᵗ (Tele.id : Tele C.Arity)))

end ProperTele
