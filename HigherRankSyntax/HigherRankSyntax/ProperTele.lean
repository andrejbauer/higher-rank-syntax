import HigherRankSyntax.Renaming

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
          (∃ x : S ∋ α, p = (inr Γ) x)
            ∨ (∃ y : Γ ∋ α, p = (inl Γ) y)
  /-- The right injection at empty base is the identity renaming. -/
  inr_nil_id : ∀ {α : C.Arity} (x : S ∋ α),
    (inr Shape.nil) x = x

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
  inl := fun Γ => ⟨fun {_} p => .there ((ProperTele.inl Γ) p)⟩
  inr := fun Γ => ⟨fun {_} p =>
    match p with
    | .here i  => .here i
    | .there x => .there ((ProperTele.inr Γ) x)⟩
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
        show ListSlotAt.there p' = ListSlotAt.there ((ProperTele.inr Γ) x)
        congr 1
      · refine Or.inr ⟨y, ?_⟩
        show ListSlotAt.there p' = ListSlotAt.there ((ProperTele.inl Γ) y)
        congr 1
  inr_nil_id := fun x => by
    cases x with
    | here _i => rfl
    | there x' =>
      show ListSlotAt.there ((ProperTele.inr Shape.nil) x') = .there x'
      rw [ProperTele.inr_nil_id x']

/-- A singleton telescope.  Definitionally the same shape as
`Tele.cons a ∘ᵗ Tele.id`; provided directly so instance search finds it
once strict unit reduction has simplified the telescope to `Tele.cons a`. -/
instance instSingleton {C : Carrier} (a : C.Arity) :
    ProperTele (Tele.cons a : Tele C.Arity) :=
  inferInstanceAs (ProperTele (Tele.cons a ∘ᵗ (Tele.id : Tele C.Arity)))

/-- Extend an already proper telescope by a concrete list of binders.  Unlike
`compose`, this recurses over the list, so extension by one more binder is
definitionally the `instCons` instance needed by recursive expression proofs. -/
@[reducible]
def extendList {C : Carrier} (S : Shape C) [ProperTele S] :
    (ρ : List C.Arity) → ProperTele (S ⋈* Tele.ofList ρ)
  | [] => inferInstanceAs (ProperTele S)
  | β :: rest =>
      letI : ProperTele (S ⋈* Tele.ofList rest) := extendList S rest
      inferInstanceAs (ProperTele ((S ⋈* Tele.ofList rest) ⋈ β))

/-- A concrete list of binders is a proper telescope. -/
@[reducible]
def ofList {C : Carrier} (ρ : List C.Arity) :
    ProperTele (Tele.ofList ρ : Shape C) :=
  extendList (Shape.nil : Shape C) ρ

/-- Instance form of `extendList` so typeclass synthesis can supply
`ProperTele (Γ ⋈* Tele.ofList ρ)` automatically whenever `Γ` is already a proper
telescope. -/
@[reducible]
instance instExtendList {C : Carrier} (Γ : Shape C) [ProperTele Γ]
    (ρ : List C.Arity) :
    ProperTele (Γ ⋈* Tele.ofList ρ) :=
  extendList Γ ρ

/-- Instance form of `ofList` so typeclass synthesis can supply
`ProperTele (Tele.ofList ρ)` automatically. -/
@[reducible]
instance instOfList {C : Carrier} (ρ : List C.Arity) :
    ProperTele (Tele.ofList ρ : Shape C) :=
  ofList ρ

/-- In a concrete list extension, the right injection of a list-side slot is
the same as first injecting it into `S ⋈* Tele.ofList ρ` and then injecting the
composite. -/
theorem extendList_inr_inr {C : Carrier} (S : Shape C) [ProperTele S]
    (ρ : List C.Arity) (Γ : Shape C)
    {α : C.Arity} (x : Tele.ofList ρ ∋ α) :
    (ProperTele.inr Γ : S ⋈* Tele.ofList ρ →ʳ Γ ⋈* (S ⋈* Tele.ofList ρ))
      ((ProperTele.inr S : Tele.ofList ρ →ʳ S ⋈* Tele.ofList ρ) x)
      =
    (ProperTele.inr (Γ ⋈* S) : Tele.ofList ρ →ʳ Γ ⋈* S ⋈* Tele.ofList ρ) x := by
  induction ρ with
  | nil => exact nomatch x
  | cons β rest ih =>
      cases x with
      | here i => rfl
      | there x' =>
          change
            ListSlotAt.there
              ((ProperTele.inr Γ : S ⋈* Tele.ofList rest →ʳ
                Γ ⋈* (S ⋈* Tele.ofList rest))
                ((ProperTele.inr S : Tele.ofList rest →ʳ
                  S ⋈* Tele.ofList rest) x'))
            =
            ListSlotAt.there
              ((ProperTele.inr (Γ ⋈* S) : Tele.ofList rest →ʳ
                Γ ⋈* S ⋈* Tele.ofList rest) x')
          congr 1
          exact ih x'

/-- In a concrete list extension, the right injection of an `S`-slot into the
composite is the same as injecting it into the base and then weakening through
the list. -/
theorem extendList_inr_inl {C : Carrier} (S : Shape C) [ProperTele S]
    (ρ : List C.Arity) (Γ : Shape C)
    {α : C.Arity} (x : S ∋ α) :
    (ProperTele.inr Γ : S ⋈* Tele.ofList ρ →ʳ Γ ⋈* (S ⋈* Tele.ofList ρ))
      ((ProperTele.inl S : S →ʳ S ⋈* Tele.ofList ρ) x)
      =
    (ProperTele.inl (Γ ⋈* S) : Γ ⋈* S →ʳ Γ ⋈* S ⋈* Tele.ofList ρ)
      ((ProperTele.inr Γ : S →ʳ Γ ⋈* S) x) := by
  induction ρ with
  | nil =>
      change (ProperTele.inr Γ) x = (ProperTele.inr Γ) x
      rfl
  | cons β rest ih =>
      change
        ListSlotAt.there
          ((ProperTele.inr Γ : S ⋈* Tele.ofList rest →ʳ
            Γ ⋈* (S ⋈* Tele.ofList rest))
            ((ProperTele.inl S : S →ʳ S ⋈* Tele.ofList rest) x))
        =
        ListSlotAt.there
          ((ProperTele.inl (Γ ⋈* S) : Γ ⋈* S →ʳ
            Γ ⋈* S ⋈* Tele.ofList rest)
            ((ProperTele.inr Γ : S →ʳ Γ ⋈* S) x))
      congr 1

/-- Weakening through a concrete list extension is the iterated weakening
through that list. -/
theorem extendList_inl {C : Carrier} (S : Shape C) [ProperTele S]
    (ρ : List C.Arity) (Γ : Shape C)
    {α : C.Arity} (x : Γ ∋ α) :
    (ProperTele.inl Γ : Γ →ʳ Γ ⋈* (S ⋈* Tele.ofList ρ)) x
      =
    (ProperTele.inl (Γ ⋈* S) : Γ ⋈* S →ʳ Γ ⋈* S ⋈* Tele.ofList ρ)
      ((ProperTele.inl Γ : Γ →ʳ Γ ⋈* S) x) := by
  induction ρ with
  | nil => rfl
  | cons β rest ih =>
      change
        ListSlotAt.there
          ((ProperTele.inl Γ : Γ →ʳ Γ ⋈* (S ⋈* Tele.ofList rest)) x)
        =
        ListSlotAt.there
          ((ProperTele.inl (Γ ⋈* S) : Γ ⋈* S →ʳ
            Γ ⋈* S ⋈* Tele.ofList rest)
            ((ProperTele.inl Γ : Γ →ʳ Γ ⋈* S) x))
      congr 1

/-- Compose two proper telescopes, keeping the structural operations coherent
with the two-stage view of `Γ ⋈* S ⋈* T`.  This is deliberately a named
constructor rather than a global instance, to avoid making typeclass search
try arbitrary telescope decompositions. -/
@[reducible]
def compose {C : Carrier} (S T : Shape C) [ProperTele S] [ProperTele T] :
    ProperTele (S ⋈* T) where
  inl := fun Γ =>
    (ProperTele.inl (Γ ⋈* S) : Γ ⋈* S →ʳ Γ ⋈* S ⋈* T) ∘ʳʳ
      (ProperTele.inl Γ : Γ →ʳ Γ ⋈* S)
  inr := fun Γ => ⟨fun {_} p =>
    ProperTele.classify S _ p
      (fun t => (ProperTele.inr (Γ ⋈* S)) t)
      (fun s => (ProperTele.inl (Γ ⋈* S))
        ((ProperTele.inr Γ) s))⟩
  classify := fun Γ _α X p f g =>
    ProperTele.classify (Γ ⋈* S) X p
      (fun t => f ((ProperTele.inr S) t))
      (fun q => ProperTele.classify Γ X q
        (fun s => f ((ProperTele.inl S) s))
        g)
  classify_inr := fun Γ X _α x f g => by
    rcases ProperTele.cover S x with ⟨t, h_t⟩ | ⟨s, h_s⟩
    · subst h_t
      have h_embed :
          ({
            apply := fun {x} p =>
              ProperTele.classify S (Γ ⋈* (S ⋈* T) ∋ x) p
                (fun t => (ProperTele.inr (Γ ⋈* S)) t)
                (fun s => (ProperTele.inl (Γ ⋈* S))
                  ((ProperTele.inr Γ) s))
          } : (S ⋈* T) →ʳ Γ ⋈* (S ⋈* T))
            ((ProperTele.inr S) t)
          =
          (ProperTele.inr (Γ ⋈* S)) t :=
        ProperTele.classify_inr S _ t _ _
      rw [h_embed]
      rw [ProperTele.classify_inr (Γ ⋈* S)]
    · subst h_s
      have h_weaken :
          ({
            apply := fun {x} p =>
              ProperTele.classify S (Γ ⋈* (S ⋈* T) ∋ x) p
                (fun t => (ProperTele.inr (Γ ⋈* S)) t)
                (fun s => (ProperTele.inl (Γ ⋈* S))
                  ((ProperTele.inr Γ) s))
          } : (S ⋈* T) →ʳ Γ ⋈* (S ⋈* T))
            ((ProperTele.inl S) s)
          =
          (ProperTele.inl (Γ ⋈* S)) ((ProperTele.inr Γ) s) :=
        ProperTele.classify_inl S _ s _ _
      rw [h_weaken]
      rw [ProperTele.classify_inl (Γ ⋈* S)]
      rw [ProperTele.classify_inr Γ]
  classify_inl := fun Γ X _α y f g => by
    change
      ProperTele.classify (Γ ⋈* S) X
        ((ProperTele.inl (Γ ⋈* S)) ((ProperTele.inl Γ) y))
        (fun t => f ((ProperTele.inr S) t))
        (fun q => ProperTele.classify Γ X q
          (fun s => f ((ProperTele.inl S) s)) g)
      =
      g y
    rw [ProperTele.classify_inl (Γ ⋈* S)]
    rw [ProperTele.classify_inl Γ]
  cover := fun Γ _α p => by
    rcases ProperTele.cover (Γ ⋈* S) p with ⟨t, h_t⟩ | ⟨q, h_q⟩
    · refine Or.inl ⟨(ProperTele.inr S) t, ?_⟩
      subst h_t
      have h_embed :
          ({
            apply := fun {x} p =>
              ProperTele.classify S (Γ ⋈* (S ⋈* T) ∋ x) p
                (fun t => (ProperTele.inr (Γ ⋈* S)) t)
                (fun s => (ProperTele.inl (Γ ⋈* S))
                  ((ProperTele.inr Γ) s))
          } : (S ⋈* T) →ʳ Γ ⋈* (S ⋈* T))
            ((ProperTele.inr S) t)
          =
          (ProperTele.inr (Γ ⋈* S)) t :=
        ProperTele.classify_inr S _ t _ _
      exact h_embed.symm
    · subst h_q
      rcases ProperTele.cover Γ q with ⟨s, h_s⟩ | ⟨y, h_y⟩
      · refine Or.inl ⟨(ProperTele.inl S) s, ?_⟩
        subst h_s
        have h_weaken :
            ({
              apply := fun {x} p =>
                ProperTele.classify S (Γ ⋈* (S ⋈* T) ∋ x) p
                  (fun t => (ProperTele.inr (Γ ⋈* S)) t)
                  (fun s => (ProperTele.inl (Γ ⋈* S))
                    ((ProperTele.inr Γ) s))
            } : (S ⋈* T) →ʳ Γ ⋈* (S ⋈* T))
              ((ProperTele.inl S) s)
            =
            (ProperTele.inl (Γ ⋈* S)) ((ProperTele.inr Γ) s) :=
          ProperTele.classify_inl S _ s _ _
        exact h_weaken.symm
      · refine Or.inr ⟨y, ?_⟩
        subst h_y
        rfl
  inr_nil_id := fun {_α} x => by
    rcases ProperTele.cover S x with ⟨t, h_t⟩ | ⟨s, h_s⟩
    · subst h_t
      have h_embed :
          ({
            apply := fun {x} p =>
              ProperTele.classify S (Shape.nil ⋈* (S ⋈* T) ∋ x) p
                (fun t => (ProperTele.inr (Shape.nil ⋈* S)) t)
                (fun s => (ProperTele.inl (Shape.nil ⋈* S))
                  ((ProperTele.inr Shape.nil) s))
          } : (S ⋈* T) →ʳ Shape.nil ⋈* (S ⋈* T))
            ((ProperTele.inr S) t)
          =
          (ProperTele.inr (Shape.nil ⋈* S)) t :=
        ProperTele.classify_inr S _ t _ _
      exact h_embed
    · subst h_s
      have h_weaken :
          ({
            apply := fun {x} p =>
              ProperTele.classify S (Shape.nil ⋈* (S ⋈* T) ∋ x) p
                (fun t => (ProperTele.inr (Shape.nil ⋈* S)) t)
                (fun s => (ProperTele.inl (Shape.nil ⋈* S))
                  ((ProperTele.inr Shape.nil) s))
          } : (S ⋈* T) →ʳ Shape.nil ⋈* (S ⋈* T))
            ((ProperTele.inl S) s)
          =
          (ProperTele.inl (Shape.nil ⋈* S))
            ((ProperTele.inr Shape.nil) s) :=
        ProperTele.classify_inl S _ s _ _
      rw [h_weaken]
      rw [ProperTele.inr_nil_id s]
      change (ProperTele.inl S) s = (ProperTele.inl S) s
      rfl

/-- In the composed `ProperTele`, the right injection of a `T`-slot factors
through `S ⋈* T`: `inr` after `inr` is the two-stage right injection. -/
theorem compose_inr_inr {C : Carrier} (S T : Shape C)
    [ProperTele S] [ProperTele T] (Γ : Shape C)
    {α : C.Arity} (x : T ∋ α) :
    letI : ProperTele (S ⋈* T) := ProperTele.compose S T
    (ProperTele.inr Γ : (S ⋈* T) →ʳ Γ ⋈* (S ⋈* T))
      ((ProperTele.inr S : T →ʳ S ⋈* T) x)
      =
    (ProperTele.inr (Γ ⋈* S) : T →ʳ Γ ⋈* S ⋈* T) x := by
  exact ProperTele.classify_inr S _ x _ _

/-- In the composed `ProperTele`, the right injection of an `inl_S`-slot is
the base right injection followed by weakening (`inl`) through `T`. -/
theorem compose_inr_inl {C : Carrier} (S T : Shape C)
    [ProperTele S] [ProperTele T] (Γ : Shape C)
    {α : C.Arity} (x : S ∋ α) :
    letI : ProperTele (S ⋈* T) := ProperTele.compose S T
    (ProperTele.inr Γ : (S ⋈* T) →ʳ Γ ⋈* (S ⋈* T))
      ((ProperTele.inl S : S →ʳ S ⋈* T) x)
      =
    (ProperTele.inl (Γ ⋈* S) : Γ ⋈* S →ʳ Γ ⋈* S ⋈* T)
      ((ProperTele.inr Γ : S →ʳ Γ ⋈* S) x) := by
  exact ProperTele.classify_inl S _ x _ _

/-- Weakening (`inl`) through the composed `ProperTele` is the two-stage
weakening through its factors. -/
theorem compose_inl {C : Carrier} (S T : Shape C)
    [ProperTele S] [ProperTele T] (Γ : Shape C)
    {α : C.Arity} (x : Γ ∋ α) :
    letI : ProperTele (S ⋈* T) := ProperTele.compose S T
    (ProperTele.inl Γ : Γ →ʳ Γ ⋈* (S ⋈* T)) x
      =
    (ProperTele.inl (Γ ⋈* S) : Γ ⋈* S →ʳ Γ ⋈* S ⋈* T)
      ((ProperTele.inl Γ : Γ →ʳ Γ ⋈* S) x) := by
  rfl

end ProperTele
