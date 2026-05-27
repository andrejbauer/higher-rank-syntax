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

/-- Compose two proper telescopes, keeping the structural operations coherent
with the two-stage view of `Γ ⋈* S ⋈* T`.  This is deliberately a named
constructor rather than a global instance, to avoid making typeclass search
try arbitrary telescope decompositions. -/
@[reducible]
def compose {C : Carrier} (S T : Shape C) [ProperTele S] [ProperTele T] :
    ProperTele (S ⋈* T) where
  weaken := fun Γ =>
    (ProperTele.weaken (Γ ⋈* S) : Γ ⋈* S →ʳ Γ ⋈* S ⋈* T) ∘ʳʳ
      (ProperTele.weaken Γ : Γ →ʳ Γ ⋈* S)
  embed := fun Γ => ⟨fun {_} p =>
    ProperTele.classify S _ p
      (fun t => (ProperTele.embed (Γ ⋈* S)).apply t)
      (fun s => (ProperTele.weaken (Γ ⋈* S)).apply
        ((ProperTele.embed Γ).apply s))⟩
  classify := fun Γ _α X p f g =>
    ProperTele.classify (Γ ⋈* S) X p
      (fun t => f ((ProperTele.embed S).apply t))
      (fun q => ProperTele.classify Γ X q
        (fun s => f ((ProperTele.weaken S).apply s))
        g)
  classify_embed := fun Γ X _α x f g => by
    rcases ProperTele.cover S x with ⟨t, h_t⟩ | ⟨s, h_s⟩
    · subst h_t
      have h_embed :
          ({
            apply := fun {x} p =>
              ProperTele.classify S (Γ ⋈* (S ⋈* T) ∋ x) p
                (fun t => (ProperTele.embed (Γ ⋈* S)).apply t)
                (fun s => (ProperTele.weaken (Γ ⋈* S)).apply
                  ((ProperTele.embed Γ).apply s))
          } : (S ⋈* T) →ʳ Γ ⋈* (S ⋈* T)).apply
            ((ProperTele.embed S).apply t)
          =
          (ProperTele.embed (Γ ⋈* S)).apply t :=
        ProperTele.classify_embed S _ t _ _
      rw [h_embed]
      rw [ProperTele.classify_embed (Γ ⋈* S)]
    · subst h_s
      have h_weaken :
          ({
            apply := fun {x} p =>
              ProperTele.classify S (Γ ⋈* (S ⋈* T) ∋ x) p
                (fun t => (ProperTele.embed (Γ ⋈* S)).apply t)
                (fun s => (ProperTele.weaken (Γ ⋈* S)).apply
                  ((ProperTele.embed Γ).apply s))
          } : (S ⋈* T) →ʳ Γ ⋈* (S ⋈* T)).apply
            ((ProperTele.weaken S).apply s)
          =
          (ProperTele.weaken (Γ ⋈* S)).apply ((ProperTele.embed Γ).apply s) :=
        ProperTele.classify_weaken S _ s _ _
      rw [h_weaken]
      rw [ProperTele.classify_weaken (Γ ⋈* S)]
      rw [ProperTele.classify_embed Γ]
  classify_weaken := fun Γ X _α y f g => by
    change
      ProperTele.classify (Γ ⋈* S) X
        ((ProperTele.weaken (Γ ⋈* S)).apply ((ProperTele.weaken Γ).apply y))
        (fun t => f ((ProperTele.embed S).apply t))
        (fun q => ProperTele.classify Γ X q
          (fun s => f ((ProperTele.weaken S).apply s)) g)
      =
      g y
    rw [ProperTele.classify_weaken (Γ ⋈* S)]
    rw [ProperTele.classify_weaken Γ]
  cover := fun Γ _α p => by
    rcases ProperTele.cover (Γ ⋈* S) p with ⟨t, h_t⟩ | ⟨q, h_q⟩
    · refine Or.inl ⟨(ProperTele.embed S).apply t, ?_⟩
      subst h_t
      have h_embed :
          ({
            apply := fun {x} p =>
              ProperTele.classify S (Γ ⋈* (S ⋈* T) ∋ x) p
                (fun t => (ProperTele.embed (Γ ⋈* S)).apply t)
                (fun s => (ProperTele.weaken (Γ ⋈* S)).apply
                  ((ProperTele.embed Γ).apply s))
          } : (S ⋈* T) →ʳ Γ ⋈* (S ⋈* T)).apply
            ((ProperTele.embed S).apply t)
          =
          (ProperTele.embed (Γ ⋈* S)).apply t :=
        ProperTele.classify_embed S _ t _ _
      exact h_embed.symm
    · subst h_q
      rcases ProperTele.cover Γ q with ⟨s, h_s⟩ | ⟨y, h_y⟩
      · refine Or.inl ⟨(ProperTele.weaken S).apply s, ?_⟩
        subst h_s
        have h_weaken :
            ({
              apply := fun {x} p =>
                ProperTele.classify S (Γ ⋈* (S ⋈* T) ∋ x) p
                  (fun t => (ProperTele.embed (Γ ⋈* S)).apply t)
                  (fun s => (ProperTele.weaken (Γ ⋈* S)).apply
                    ((ProperTele.embed Γ).apply s))
            } : (S ⋈* T) →ʳ Γ ⋈* (S ⋈* T)).apply
              ((ProperTele.weaken S).apply s)
            =
            (ProperTele.weaken (Γ ⋈* S)).apply ((ProperTele.embed Γ).apply s) :=
          ProperTele.classify_weaken S _ s _ _
        exact h_weaken.symm
      · refine Or.inr ⟨y, ?_⟩
        subst h_y
        rfl
  embed_nil_id := fun {_α} x => by
    rcases ProperTele.cover S x with ⟨t, h_t⟩ | ⟨s, h_s⟩
    · subst h_t
      have h_embed :
          ({
            apply := fun {x} p =>
              ProperTele.classify S (Shape.nil ⋈* (S ⋈* T) ∋ x) p
                (fun t => (ProperTele.embed (Shape.nil ⋈* S)).apply t)
                (fun s => (ProperTele.weaken (Shape.nil ⋈* S)).apply
                  ((ProperTele.embed Shape.nil).apply s))
          } : (S ⋈* T) →ʳ Shape.nil ⋈* (S ⋈* T)).apply
            ((ProperTele.embed S).apply t)
          =
          (ProperTele.embed (Shape.nil ⋈* S)).apply t :=
        ProperTele.classify_embed S _ t _ _
      exact h_embed
    · subst h_s
      have h_weaken :
          ({
            apply := fun {x} p =>
              ProperTele.classify S (Shape.nil ⋈* (S ⋈* T) ∋ x) p
                (fun t => (ProperTele.embed (Shape.nil ⋈* S)).apply t)
                (fun s => (ProperTele.weaken (Shape.nil ⋈* S)).apply
                  ((ProperTele.embed Shape.nil).apply s))
          } : (S ⋈* T) →ʳ Shape.nil ⋈* (S ⋈* T)).apply
            ((ProperTele.weaken S).apply s)
          =
          (ProperTele.weaken (Shape.nil ⋈* S)).apply
            ((ProperTele.embed Shape.nil).apply s) :=
        ProperTele.classify_weaken S _ s _ _
      rw [h_weaken]
      rw [ProperTele.embed_nil_id s]
      change (ProperTele.weaken S).apply s = (ProperTele.weaken S).apply s
      rfl

/-- In the canonical composed `ProperTele`, embedding a `T`-slot is the same
as first embedding it into `S ⋈* T` and then embedding the composite. -/
theorem compose_embed_embed {C : Carrier} (S T : Shape C)
    [ProperTele S] [ProperTele T] (Γ : Shape C)
    {α : C.Arity} (x : T ∋ α) :
    letI : ProperTele (S ⋈* T) := ProperTele.compose S T
    (ProperTele.embed Γ : (S ⋈* T) →ʳ Γ ⋈* (S ⋈* T)).apply
      ((ProperTele.embed S : T →ʳ S ⋈* T).apply x)
      =
    (ProperTele.embed (Γ ⋈* S) : T →ʳ Γ ⋈* S ⋈* T).apply x := by
  exact ProperTele.classify_embed S _ x _ _

/-- In the canonical composed `ProperTele`, embedding an `S`-slot is the same
as first embedding it into the base and then weakening through `T`. -/
theorem compose_embed_weaken {C : Carrier} (S T : Shape C)
    [ProperTele S] [ProperTele T] (Γ : Shape C)
    {α : C.Arity} (x : S ∋ α) :
    letI : ProperTele (S ⋈* T) := ProperTele.compose S T
    (ProperTele.embed Γ : (S ⋈* T) →ʳ Γ ⋈* (S ⋈* T)).apply
      ((ProperTele.weaken S : S →ʳ S ⋈* T).apply x)
      =
    (ProperTele.weaken (Γ ⋈* S) : Γ ⋈* S →ʳ Γ ⋈* S ⋈* T).apply
      ((ProperTele.embed Γ : S →ʳ Γ ⋈* S).apply x) := by
  exact ProperTele.classify_weaken S _ x _ _

/-- Weakening through a canonical composed `ProperTele` is the two-stage
weakening through its factors. -/
theorem compose_weaken {C : Carrier} (S T : Shape C)
    [ProperTele S] [ProperTele T] (Γ : Shape C)
    {α : C.Arity} (x : Γ ∋ α) :
    letI : ProperTele (S ⋈* T) := ProperTele.compose S T
    (ProperTele.weaken Γ : Γ →ʳ Γ ⋈* (S ⋈* T)).apply x
      =
    (ProperTele.weaken (Γ ⋈* S) : Γ ⋈* S →ʳ Γ ⋈* S ⋈* T).apply
      ((ProperTele.weaken Γ : Γ →ʳ Γ ⋈* S).apply x) := by
  rfl

end ProperTele
