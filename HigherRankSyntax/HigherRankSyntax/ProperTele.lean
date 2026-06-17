import HigherRankSyntax.Renaming

/-!
# Proper Telescopes

A type class on `Tele C.Arity` exhibiting `Γ ⧺ Δ` as a coproduct, providing the structural
operations needed to dispatch a slot of `Γ ⧺ Δ` between the Γ-side and the Δ-side:

* `inl Γ` — left injection of the base `Γ` into `Γ ⧺ Δ` (weakening).
* `inr Γ` — right injection of the telescope `Δ` into `Γ ⧺ Δ`.
* `classify Γ` — CPS dispatch of a `Γ ⧺ Δ`-slot to either side.
* `classify_inr`, `classify_inl` — reflection lemmas.
* `cover` — every slot of `Γ ⧺ Δ` is in the image of exactly one of `inl`, `inr`
  (the propositional inverse of `classify`, needed to case-split a slot
  into its two possible forms when proving equations).

Two instances are declared:

* `Tele.id` — trivial (no S-slots).
* `Tele.cons a ∘ᵗ T` from `[Proper T]` — extend by one binder.

Tele equality is unchanged by the class — instances live in the
instance slot, not in Tele's data, so the strict-monoid laws on Tele
(`id_comp`, `comp_id`, `comp_assoc`) keep their `rfl` proofs.

## Why a class, and not a propositional equation

A natural alternative would be to impose the propositional equation
`∀ Δ, Γ Δ = Γ.toList ⧺ Δ` (or to bundle it into `Tele` itself) and derive
the structural operations from it.  That suffices *mathematically* — for
left-action telescopes (our convention, with `Γ.toList` prepended to the
input) this equation is exactly what "Γ behaves like a fixed prefix" means.
But slot dispatch then has to fire `Eq.rec` along the equation in order to
turn a `Γ ⧺ Δ ∋ α` into a `Γ.toList ⧺ Δ ∋ α`, and the resulting transports
permeate every `Expr`-rebuilding step downstream.

`Proper` instead exhibits the iso `Γ ⧺ Δ ≅ Γ.toList ⧺ Δ` *structurally*, as
the four maps `inl / inr / classify / cover` with their reflection equations.
Slot dispatch and downstream code then stay transport-free.  For telescopes
built from `Tele.id`, `Tele.cons`, and `∘ᵗ` the equation already holds by
`rfl`, so the class is just naming the structural witness that the standard
generators already supply.

Side note on the cons-induction equation: `Γ (α :: Δ) = α :: Γ Δ` does *not*
characterise the left-action form `Γ Δ = Γ.toList ⧺ Δ` (the inductive step
fails: `α :: (Γ.toList ⧺ Δ') ≠ Γ.toList ⧺ (α :: Δ')` in general).  It
characterises the right-action form `Γ Δ = Δ ⧺ Γ.toList`.  We use left
action because that is what makes `(Γ ∷ α).toList = α :: Γ.toList` reduce by
`rfl`, which the cons-style `ListSlotAt` needs.
-/


/-- A `Proper` instance exhibits `Γ ⧺ S` as a coproduct
(fibrewise per arity): two injection renamings and a classifier, so that
a slot of `Γ ⧺ S` dispatches uniformly between Γ-slots and S-slots. -/
class Proper {C : Carrier} (Γ : Tele C.Arity) : Type 1 where
  /-- Left injection, i.e, weakening Δ ↪ Δ ⧺ S. -/
  inl : (Δ : Shape C) → Δ →ʳ Δ ⧺ Γ
  /-- Right injection: the telescope's own shape `Γ` into `Δ ⧺ Γ`. -/
  inr : (Δ : Shape C) → Γ →ʳ Δ ⧺ Γ
  /-- Classifier (CPS): dispatch a slot of `Δ ⧺ Γ` into either a Δ-slot
  or a Γ-slot. -/
  classify : (Δ : Shape C) → {α : C.Arity} → (X : Type) → Δ ⧺ Γ ∋ α →
             (Γ ∋ α → X) → (Δ ∋ α → X) → X
  /-- Reflection: classifying a right-injected S-slot fires the S-continuation. -/
  classify_inr : ∀ (Δ : Shape C) (X : Type) {α : C.Arity} (x : Γ ∋ α)
                   (f : Γ ∋ α → X) (g : Δ ∋ α → X),
                   classify Δ X (inr Δ x) f g = f x
  /-- Reflection: classifying a left-injected Δ-slot fires the Δ-continuation. -/
  classify_inl : ∀ (Δ : Shape C) (X : Type) {α : C.Arity} (y : Δ ∋ α)
                   (f : Γ ∋ α → X) (g : Δ ∋ α → X),
                   classify Δ X (inl Δ y) f g = g y
  /-- Cover: every slot is in the image of `inr` or `inl`. -/
  cover : ∀ (Δ : Shape C) {α : C.Arity} (p : Δ ⧺ Γ ∋ α),
          (∃ x : Γ ∋ α, p = inr Δ x) ∨ (∃ y : Δ ∋ α, p = inl Δ y)
  /-- The right injection at empty base is the identity renaming. -/
  inr_nil_id : ∀ {α : C.Arity} (x : Γ ∋ α),
    inr .nil x = x

namespace Proper

/-- The identity telescope: empty; the classifier returns everything to Γ. -/
instance instId {C : Carrier} : Proper (Tele.id : Tele C.Arity) where
  inl := fun Γ => Renaming.id Γ
  inr := fun _Γ => ⟨fun {_} p => nomatch p⟩
  classify := fun _Γ _α _X p _f g => g p
  classify_inr := fun _Γ _X _α x _f _g => nomatch x
  classify_inl := fun _Γ _X _α _y _f _g => rfl
  cover := fun _Γ _α p => Or.inr ⟨p, rfl⟩
  inr_nil_id := fun x => nomatch x

/-- Extend a `Proper` by one arity at the top. -/
instance instCons {C : Carrier} (a : C.Arity) (T : Tele C.Arity) [Proper T] :
    Proper (Tele.cons a ∘ᵗ T) where
  inl := fun Γ => ⟨fun {_} p => .there ((Proper.inl Γ) p)⟩
  inr := fun Γ => ⟨fun {_} p =>
    match p with
    | .here i  => .here i
    | .there x => .there ((Proper.inr Γ) x)⟩
  classify := fun Γ _α X p f g =>
    match p with
    | .here i   => f (.here i)
    | .there p' => Proper.classify Γ X p'
                     (fun y => f (.there y)) g
  classify_inr := fun Γ X _α x f g => by
    cases x with
    | here _i  => rfl
    | there x' =>
      exact Proper.classify_inr Γ X x'
              (fun y => f (.there y)) g
  classify_inl := fun Γ X _α y f g => by
    exact Proper.classify_inl Γ X y
            (fun z => f (.there z)) g
  cover := fun Γ _α p => by
    cases p with
    | here i  => exact Or.inl ⟨.here i, rfl⟩
    | there p' =>
      rcases Proper.cover Γ p' with ⟨x, h⟩ | ⟨y, h⟩
      · refine Or.inl ⟨.there x, ?_⟩
        show ListSlotAt.there p' = ListSlotAt.there ((Proper.inr Γ) x)
        congr 1
      · refine Or.inr ⟨y, ?_⟩
        show ListSlotAt.there p' = ListSlotAt.there ((Proper.inl Γ) y)
        congr 1
  inr_nil_id := fun x => by
    cases x with
    | here _i => rfl
    | there x' =>
      show ListSlotAt.there ((Proper.inr Shape.nil) x') = .there x'
      rw [Proper.inr_nil_id x']

/-- A singleton telescope.  Definitionally the same shape as
`Tele.cons a ∘ᵗ Tele.id`; provided directly so instance search finds it
once strict unit reduction has simplified the telescope to `Tele.cons a`. -/
instance instSingleton {C : Carrier} (a : C.Arity) :
    Proper (Tele.cons a : Tele C.Arity) :=
  inferInstanceAs (Proper (Tele.cons a ∘ᵗ (Tele.id : Tele C.Arity)))

/-- Extend an already proper telescope by a concrete list of binders.  Unlike
`compose`, this recurses over the list, so extension by one more binder is
definitionally the `instCons` instance needed by recursive expression proofs. -/
@[reducible]
def extendList {C : Carrier} (S : Shape C) [Proper S] :
    (ρ : List C.Arity) → Proper (S ⧺ Tele.ofList ρ)
  | [] => inferInstanceAs (Proper S)
  | β :: rest =>
      letI : Proper (S ⧺ Tele.ofList rest) := extendList S rest
      inferInstanceAs (Proper ((S ⧺ Tele.ofList rest) ∷ β))

/-- A concrete list of binders is a proper telescope. -/
@[reducible]
def ofList {C : Carrier} (ρ : List C.Arity) :
    Proper (Tele.ofList ρ : Shape C) :=
  extendList (Shape.nil : Shape C) ρ

/-- Instance form of `extendList` so typeclass synthesis can supply
`Proper (Γ ⧺ Tele.ofList ρ)` automatically whenever `Γ` is already a proper
telescope. -/
@[reducible]
instance instExtendList {C : Carrier} (Γ : Shape C) [Proper Γ]
    (ρ : List C.Arity) :
    Proper (Γ ⧺ Tele.ofList ρ) :=
  extendList Γ ρ

/-- Instance form of `ofList` so typeclass synthesis can supply
`Proper (Tele.ofList ρ)` automatically. -/
@[reducible]
instance instOfList {C : Carrier} (ρ : List C.Arity) :
    Proper (Tele.ofList ρ : Shape C) :=
  ofList ρ

/-- In a concrete list extension, the right injection of a list-side slot is
the same as first injecting it into `S ⧺ Tele.ofList ρ` and then injecting the
composite. -/
theorem extendList_inr_inr {C : Carrier} (S : Shape C) [Proper S]
    (ρ : List C.Arity) (Γ : Shape C)
    {α : C.Arity} (x : Tele.ofList ρ ∋ α) :
    (Proper.inr Γ : S ⧺ Tele.ofList ρ →ʳ Γ ⧺ (S ⧺ Tele.ofList ρ))
      ((Proper.inr S : Tele.ofList ρ →ʳ S ⧺ Tele.ofList ρ) x)
      =
    (Proper.inr (Γ ⧺ S) : Tele.ofList ρ →ʳ Γ ⧺ S ⧺ Tele.ofList ρ) x := by
  induction ρ with
  | nil => exact nomatch x
  | cons β rest ih =>
      cases x with
      | here i => rfl
      | there x' =>
          change
            ListSlotAt.there
              ((Proper.inr Γ : S ⧺ Tele.ofList rest →ʳ
                Γ ⧺ (S ⧺ Tele.ofList rest))
                ((Proper.inr S : Tele.ofList rest →ʳ
                  S ⧺ Tele.ofList rest) x'))
            =
            ListSlotAt.there
              ((Proper.inr (Γ ⧺ S) : Tele.ofList rest →ʳ
                Γ ⧺ S ⧺ Tele.ofList rest) x')
          congr 1
          exact ih x'

/-- In a concrete list extension, the right injection of an `S`-slot into the
composite is the same as injecting it into the base and then weakening through
the list. -/
theorem extendList_inr_inl {C : Carrier} (S : Shape C) [Proper S]
    (ρ : List C.Arity) (Γ : Shape C)
    {α : C.Arity} (x : S ∋ α) :
    (Proper.inr Γ : S ⧺ Tele.ofList ρ →ʳ Γ ⧺ (S ⧺ Tele.ofList ρ))
      ((Proper.inl S : S →ʳ S ⧺ Tele.ofList ρ) x)
      =
    (Proper.inl (Γ ⧺ S) : Γ ⧺ S →ʳ Γ ⧺ S ⧺ Tele.ofList ρ)
      ((Proper.inr Γ : S →ʳ Γ ⧺ S) x) := by
  induction ρ with
  | nil =>
      change (Proper.inr Γ) x = (Proper.inr Γ) x
      rfl
  | cons β rest ih =>
      change
        ListSlotAt.there
          ((Proper.inr Γ : S ⧺ Tele.ofList rest →ʳ
            Γ ⧺ (S ⧺ Tele.ofList rest))
            ((Proper.inl S : S →ʳ S ⧺ Tele.ofList rest) x))
        =
        ListSlotAt.there
          ((Proper.inl (Γ ⧺ S) : Γ ⧺ S →ʳ
            Γ ⧺ S ⧺ Tele.ofList rest)
            ((Proper.inr Γ : S →ʳ Γ ⧺ S) x))
      congr 1

/-- Weakening through a concrete list extension is the iterated weakening
through that list. -/
theorem extendList_inl {C : Carrier} (S : Shape C) [Proper S]
    (ρ : List C.Arity) (Γ : Shape C)
    {α : C.Arity} (x : Γ ∋ α) :
    (Proper.inl Γ : Γ →ʳ Γ ⧺ (S ⧺ Tele.ofList ρ)) x
      =
    (Proper.inl (Γ ⧺ S) : Γ ⧺ S →ʳ Γ ⧺ S ⧺ Tele.ofList ρ)
      ((Proper.inl Γ : Γ →ʳ Γ ⧺ S) x) := by
  induction ρ with
  | nil => rfl
  | cons β rest ih =>
      change
        ListSlotAt.there
          ((Proper.inl Γ : Γ →ʳ Γ ⧺ (S ⧺ Tele.ofList rest)) x)
        =
        ListSlotAt.there
          ((Proper.inl (Γ ⧺ S) : Γ ⧺ S →ʳ
            Γ ⧺ S ⧺ Tele.ofList rest)
            ((Proper.inl Γ : Γ →ʳ Γ ⧺ S) x))
      congr 1

/-- Compose two proper telescopes, keeping the structural operations coherent
with the two-stage view of `Γ ⧺ S ⧺ T`.  This is deliberately a named
constructor rather than a global instance, to avoid making typeclass search
try arbitrary telescope decompositions. -/
@[reducible]
def compose {C : Carrier} (S T : Shape C) [Proper S] [Proper T] :
    Proper (S ⧺ T) where
  inl := fun Γ =>
    (Proper.inl (Γ ⧺ S) : Γ ⧺ S →ʳ Γ ⧺ S ⧺ T) ∘ʳʳ
      (Proper.inl Γ : Γ →ʳ Γ ⧺ S)
  inr := fun Γ => ⟨fun {_} p =>
    Proper.classify S _ p
      (fun t => (Proper.inr (Γ ⧺ S)) t)
      (fun s => (Proper.inl (Γ ⧺ S))
        ((Proper.inr Γ) s))⟩
  classify := fun Γ _α X p f g =>
    Proper.classify (Γ ⧺ S) X p
      (fun t => f ((Proper.inr S) t))
      (fun q => Proper.classify Γ X q
        (fun s => f ((Proper.inl S) s))
        g)
  classify_inr := fun Γ X _α x f g => by
    rcases Proper.cover S x with ⟨t, h_t⟩ | ⟨s, h_s⟩
    · subst h_t
      have h_embed :
          ({
            apply := fun {x} p =>
              Proper.classify S (Γ ⧺ (S ⧺ T) ∋ x) p
                (fun t => (Proper.inr (Γ ⧺ S)) t)
                (fun s => (Proper.inl (Γ ⧺ S))
                  ((Proper.inr Γ) s))
          } : (S ⧺ T) →ʳ Γ ⧺ (S ⧺ T))
            ((Proper.inr S) t)
          =
          (Proper.inr (Γ ⧺ S)) t :=
        Proper.classify_inr S _ t _ _
      rw [h_embed]
      rw [Proper.classify_inr (Γ ⧺ S)]
    · subst h_s
      have h_weaken :
          ({
            apply := fun {x} p =>
              Proper.classify S (Γ ⧺ (S ⧺ T) ∋ x) p
                (fun t => (Proper.inr (Γ ⧺ S)) t)
                (fun s => (Proper.inl (Γ ⧺ S))
                  ((Proper.inr Γ) s))
          } : (S ⧺ T) →ʳ Γ ⧺ (S ⧺ T))
            ((Proper.inl S) s)
          =
          (Proper.inl (Γ ⧺ S)) ((Proper.inr Γ) s) :=
        Proper.classify_inl S _ s _ _
      rw [h_weaken]
      rw [Proper.classify_inl (Γ ⧺ S)]
      rw [Proper.classify_inr Γ]
  classify_inl := fun Γ X _α y f g => by
    change
      Proper.classify (Γ ⧺ S) X
        ((Proper.inl (Γ ⧺ S)) ((Proper.inl Γ) y))
        (fun t => f ((Proper.inr S) t))
        (fun q => Proper.classify Γ X q
          (fun s => f ((Proper.inl S) s)) g)
      =
      g y
    rw [Proper.classify_inl (Γ ⧺ S)]
    rw [Proper.classify_inl Γ]
  cover := fun Γ _α p => by
    rcases Proper.cover (Γ ⧺ S) p with ⟨t, h_t⟩ | ⟨q, h_q⟩
    · refine Or.inl ⟨(Proper.inr S) t, ?_⟩
      subst h_t
      have h_embed :
          ({
            apply := fun {x} p =>
              Proper.classify S (Γ ⧺ (S ⧺ T) ∋ x) p
                (fun t => (Proper.inr (Γ ⧺ S)) t)
                (fun s => (Proper.inl (Γ ⧺ S))
                  ((Proper.inr Γ) s))
          } : (S ⧺ T) →ʳ Γ ⧺ (S ⧺ T))
            ((Proper.inr S) t)
          =
          (Proper.inr (Γ ⧺ S)) t :=
        Proper.classify_inr S _ t _ _
      exact h_embed.symm
    · subst h_q
      rcases Proper.cover Γ q with ⟨s, h_s⟩ | ⟨y, h_y⟩
      · refine Or.inl ⟨(Proper.inl S) s, ?_⟩
        subst h_s
        have h_weaken :
            ({
              apply := fun {x} p =>
                Proper.classify S (Γ ⧺ (S ⧺ T) ∋ x) p
                  (fun t => (Proper.inr (Γ ⧺ S)) t)
                  (fun s => (Proper.inl (Γ ⧺ S))
                    ((Proper.inr Γ) s))
            } : (S ⧺ T) →ʳ Γ ⧺ (S ⧺ T))
              ((Proper.inl S) s)
            =
            (Proper.inl (Γ ⧺ S)) ((Proper.inr Γ) s) :=
          Proper.classify_inl S _ s _ _
        exact h_weaken.symm
      · refine Or.inr ⟨y, ?_⟩
        subst h_y
        rfl
  inr_nil_id := fun {_α} x => by
    rcases Proper.cover S x with ⟨t, h_t⟩ | ⟨s, h_s⟩
    · subst h_t
      have h_embed :
          ({
            apply := fun {x} p =>
              Proper.classify S (Shape.nil ⧺ (S ⧺ T) ∋ x) p
                (fun t => (Proper.inr (Shape.nil ⧺ S)) t)
                (fun s => (Proper.inl (Shape.nil ⧺ S))
                  ((Proper.inr Shape.nil) s))
          } : (S ⧺ T) →ʳ Shape.nil ⧺ (S ⧺ T))
            ((Proper.inr S) t)
          =
          (Proper.inr (Shape.nil ⧺ S)) t :=
        Proper.classify_inr S _ t _ _
      exact h_embed
    · subst h_s
      have h_weaken :
          ({
            apply := fun {x} p =>
              Proper.classify S (Shape.nil ⧺ (S ⧺ T) ∋ x) p
                (fun t => (Proper.inr (Shape.nil ⧺ S)) t)
                (fun s => (Proper.inl (Shape.nil ⧺ S))
                  ((Proper.inr Shape.nil) s))
          } : (S ⧺ T) →ʳ Shape.nil ⧺ (S ⧺ T))
            ((Proper.inl S) s)
          =
          (Proper.inl (Shape.nil ⧺ S))
            ((Proper.inr Shape.nil) s) :=
        Proper.classify_inl S _ s _ _
      rw [h_weaken]
      rw [Proper.inr_nil_id s]
      change (Proper.inl S) s = (Proper.inl S) s
      rfl

/-- In the composed `Proper`, the right injection of a `T`-slot factors
through `S ⧺ T`: `inr` after `inr` is the two-stage right injection. -/
theorem compose_inr_inr {C : Carrier} (S T : Shape C)
    [Proper S] [Proper T] (Γ : Shape C)
    {α : C.Arity} (x : T ∋ α) :
    letI : Proper (S ⧺ T) := Proper.compose S T
    (Proper.inr Γ : (S ⧺ T) →ʳ Γ ⧺ (S ⧺ T))
      ((Proper.inr S : T →ʳ S ⧺ T) x)
      =
    (Proper.inr (Γ ⧺ S) : T →ʳ Γ ⧺ S ⧺ T) x := by
  exact Proper.classify_inr S _ x _ _

/-- In the composed `Proper`, the right injection of an `inl_S`-slot is
the base right injection followed by weakening (`inl`) through `T`. -/
theorem compose_inr_inl {C : Carrier} (S T : Shape C)
    [Proper S] [Proper T] (Γ : Shape C)
    {α : C.Arity} (x : S ∋ α) :
    letI : Proper (S ⧺ T) := Proper.compose S T
    (Proper.inr Γ : (S ⧺ T) →ʳ Γ ⧺ (S ⧺ T))
      ((Proper.inl S : S →ʳ S ⧺ T) x)
      =
    (Proper.inl (Γ ⧺ S) : Γ ⧺ S →ʳ Γ ⧺ S ⧺ T)
      ((Proper.inr Γ : S →ʳ Γ ⧺ S) x) := by
  exact Proper.classify_inl S _ x _ _

/-- Weakening (`inl`) through the composed `Proper` is the two-stage
weakening through its factors. -/
theorem compose_inl {C : Carrier} (S T : Shape C)
    [Proper S] [Proper T] (Γ : Shape C)
    {α : C.Arity} (x : Γ ∋ α) :
    letI : Proper (S ⧺ T) := Proper.compose S T
    (Proper.inl Γ : Γ →ʳ Γ ⧺ (S ⧺ T)) x
      =
    (Proper.inl (Γ ⧺ S) : Γ ⧺ S →ʳ Γ ⧺ S ⧺ T)
      ((Proper.inl Γ : Γ →ʳ Γ ⧺ S) x) := by
  rfl

end Proper

/-! ## Canonical proper spines

`Proper` is a typeclass witness that a telescope behaves like a finite prefix.
That is convenient for existing code, but typeclass search can construct
different proof-relevant witnesses for the same telescope.  `ProperSpine Γ`
records the prefix structure canonically.  Its operations recurse on the
spine, so injection coherence for composite telescopes becomes ordinary
structural computation.
-/

/-- A canonical finite-prefix witness for a telescope. -/
inductive ProperSpine {C : Carrier} : Shape C → Type where
  | nil : ProperSpine (Shape.nil : Shape C)
  | cons {Γ : Shape C} : ProperSpine Γ → (α : C.Arity) → ProperSpine (Γ ∷ α)

namespace ProperSpine

/-- Left injection: weaken a base context through the spine. -/
def inl {C : Carrier} {S : Shape C} (p : ProperSpine S) (Γ : Shape C) :
    Γ →ʳ Γ ⧺ S :=
  match p with
  | .nil => 𝟙ʳ
  | .cons p α => ⟨fun x => .there (inl p Γ x)⟩

/-- Right injection: embed the spine's own slots over a base context. -/
def inr {C : Carrier} {S : Shape C} (p : ProperSpine S) (Γ : Shape C) :
    S →ʳ Γ ⧺ S :=
  match p with
  | .nil => ⟨fun x => nomatch x⟩
  | .cons p α => ⟨fun
      | .here i => .here i
      | .there x => .there (inr p Γ x)⟩

/-- Dispatch a slot of `Γ ⧺ S` into either the spine side or the base side. -/
def classify {C : Carrier} {S : Shape C} (p : ProperSpine S)
    (Γ : Shape C) {α : C.Arity} (X : Type)
    (x : Γ ⧺ S ∋ α) (right : S ∋ α → X) (left : Γ ∋ α → X) : X :=
  match p with
  | .nil => left x
  | .cons p β =>
      match x with
      | .here i => right (.here i)
      | .there x => classify p Γ X x (fun y => right (.there y)) left

/-- Cover a slot of `Γ ⧺ S` by one of the two canonical injections. -/
def cover {C : Carrier} : {S : Shape C} → (p : ProperSpine S) →
    (Γ : Shape C) → {α : C.Arity} → (x : Γ ⧺ S ∋ α) →
    (S ∋ α) ⊕ (Γ ∋ α)
  | _, .nil, _Γ, _, x => Sum.inr x
  | _, .cons _p _β, Γ, _, .here i => Sum.inl (.here i)
  | _, .cons p _β, Γ, _, .there x =>
      match cover p Γ x with
      | Sum.inl y => Sum.inl (.there y)
      | Sum.inr y => Sum.inr y

/-- Proof-carrying cover for the canonical spine injections. -/
theorem coverEq {C : Carrier} :
    {S : Shape C} → (p : ProperSpine S) → (Γ : Shape C) →
    {α : C.Arity} → (x : Γ ⧺ S ∋ α) →
    (∃ y : S ∋ α, x = inr p Γ y) ∨
      (∃ y : Γ ∋ α, x = inl p Γ y)
  | _, .nil, _Γ, _, x => Or.inr ⟨x, rfl⟩
  | _, .cons _p _β, Γ, _, .here i => Or.inl ⟨.here i, rfl⟩
  | _, .cons p _β, Γ, _, .there x =>
      match coverEq p Γ x with
      | Or.inl ⟨y, h⟩ =>
          Or.inl ⟨.there y, by rw [h]; rfl⟩
      | Or.inr ⟨y, h⟩ =>
          Or.inr ⟨y, by rw [h]; rfl⟩

/-- Canonical append of spines.  Recursing on the right spine makes
`append p (.cons q α)` compute to `.cons (append p q) α`, matching binder
descent through `Γ ⧺ (Δ ∷ α)`. -/
def append {C : Carrier} {S T : Shape C}
    (pS : ProperSpine S) (pT : ProperSpine T) :
    ProperSpine (S ⧺ T) :=
  match pT with
  | .nil => pS
  | .cons pT α => .cons (append pS pT) α

/-- A concrete list of arities as a canonical spine. -/
def ofList {C : Carrier} : (ρ : List C.Arity) →
    ProperSpine (Tele.ofList ρ : Shape C)
  | [] => .nil
  | α :: ρ => .cons (ofList ρ) α

/-- Extend a canonical spine by a concrete list of top binders. -/
def extendList {C : Carrier} {S : Shape C} (pS : ProperSpine S) :
    (ρ : List C.Arity) → ProperSpine (S ⧺ Tele.ofList ρ)
  | [] => pS
  | α :: ρ => .cons (extendList pS ρ) α

@[simp] theorem inl_nil {C : Carrier} (Γ : Shape C) :
    inl .nil Γ = (𝟙ʳ : Γ →ʳ Γ) := rfl

theorem inr_nil {C : Carrier} (Γ : Shape C) {α : C.Arity}
    (x : (Shape.nil : Shape C) ∋ α) :
    inr .nil Γ x = nomatch x := by
  cases x

@[simp] theorem inl_cons {C : Carrier} {S : Shape C}
    (p : ProperSpine S) (β : C.Arity) (Γ : Shape C)
    {α : C.Arity} (x : Γ ∋ α) :
    inl (.cons p β) Γ x = .there (inl p Γ x) := rfl

@[simp] theorem inr_cons_here {C : Carrier} {S : Shape C}
    (p : ProperSpine S) (β : C.Arity) (Γ : Shape C)
    (i : C.Binder β) :
    inr (.cons p β) Γ (.here i) = .here i := rfl

@[simp] theorem inr_cons_there {C : Carrier} {S : Shape C}
    (p : ProperSpine S) (β : C.Arity) (Γ : Shape C)
    {α : C.Arity} (x : S ∋ α) :
    inr (.cons p β) Γ (.there x) = .there (inr p Γ x) := rfl

@[simp] theorem classify_inr {C : Carrier} {S : Shape C}
    (p : ProperSpine S) (Γ : Shape C) (X : Type)
    {α : C.Arity} (x : S ∋ α)
    (right : S ∋ α → X) (left : Γ ∋ α → X) :
    classify p Γ X (inr p Γ x) right left = right x := by
  induction p generalizing Γ X α with
  | nil => cases x
  | cons p β ih =>
      cases x with
      | here i => rfl
      | there x =>
          exact ih Γ X x (fun y => right (.there y)) left

@[simp] theorem classify_inl {C : Carrier} {S : Shape C}
    (p : ProperSpine S) (Γ : Shape C) (X : Type)
    {α : C.Arity} (x : Γ ∋ α)
    (right : S ∋ α → X) (left : Γ ∋ α → X) :
    classify p Γ X (inl p Γ x) right left = left x := by
  induction p generalizing Γ X α with
  | nil => rfl
  | cons p β ih =>
      exact ih Γ X x (fun y => right (.there y)) left

@[simp] theorem classify_cons_here {C : Carrier} {S Γ : Shape C}
    (p : ProperSpine S) (β : C.Arity) (X : Type)
    (i : C.Binder β)
    (right : S ∷ β ∋ i.arity → X) (left : Γ ∋ i.arity → X) :
    classify (.cons p β) Γ X (.here i) right left = right (.here i) := rfl

@[simp] theorem classify_cons_there {C : Carrier} {S Γ : Shape C}
    (p : ProperSpine S) (β : C.Arity) (X : Type)
    {α : C.Arity} (x : Γ ⧺ S ∋ α)
    (right : S ∷ β ∋ α → X) (left : Γ ∋ α → X) :
    classify (.cons p β) Γ X (.there x) right left =
      classify p Γ X x (fun y => right (.there y)) left := rfl

theorem classify_weaken {C : Carrier} {S Γ Δ : Shape C}
    (p : ProperSpine S) (β : C.Arity)
    {α : C.Arity} (x : Γ ⧺ S ∋ α)
    (right : S ∋ α → Δ ∋ α) (left : Γ ∋ α → Δ ∋ α) :
    classify p Γ (Δ ∷ β ∋ α) x
        (fun y => .there (right y))
        (fun y => .there (left y)) =
      .there (classify p Γ (Δ ∋ α) x right left) := by
  induction p generalizing Γ Δ α with
  | nil => rfl
  | cons p γ ih =>
      cases x with
      | here i => rfl
      | there x =>
          exact ih x (fun y => right (.there y)) left

theorem cover_inr {C : Carrier} :
    {S : Shape C} → (p : ProperSpine S) → (Γ : Shape C) →
    {α : C.Arity} → (x : S ∋ α) →
    ∃ y : S ∋ α, inr p Γ x = inr p Γ y
  | _, _p, _Γ, _, x => ⟨x, rfl⟩

theorem cover_inl {C : Carrier} :
    {S : Shape C} → (p : ProperSpine S) → (Γ : Shape C) →
    {α : C.Arity} → (x : Γ ∋ α) →
    ∃ y : Γ ∋ α, inl p Γ x = inl p Γ y
  | _, _p, _Γ, _, x => ⟨x, rfl⟩

@[simp] theorem append_nil {C : Carrier} {S : Shape C}
    (pS : ProperSpine S) :
    append pS .nil = pS := rfl

@[simp] theorem append_cons {C : Carrier} {S T : Shape C}
    (pS : ProperSpine S) (pT : ProperSpine T) (α : C.Arity) :
    append pS (.cons pT α) = .cons (append pS pT) α := rfl

theorem append_inl {C : Carrier} {S T : Shape C}
    (pS : ProperSpine S) (pT : ProperSpine T)
    (Γ : Shape C) {α : C.Arity} (x : Γ ∋ α) :
    inl (append pS pT) Γ x =
      inl pT (Γ ⧺ S) (inl pS Γ x) := by
  induction pT generalizing Γ α x with
  | nil => rfl
  | cons pT β ih =>
      exact congrArg ListSlotAt.there (ih Γ x)

theorem append_inr_inl {C : Carrier} {S T : Shape C}
    (pS : ProperSpine S) (pT : ProperSpine T)
    (Γ : Shape C) {α : C.Arity} (x : S ∋ α) :
    inr (append pS pT) Γ (inl pT S x) =
      inl pT (Γ ⧺ S) (inr pS Γ x) := by
  induction pT generalizing Γ α x with
  | nil => rfl
  | cons pT β ih =>
      exact congrArg ListSlotAt.there (ih Γ x)

theorem append_inr_inr {C : Carrier} {S T : Shape C}
    (pS : ProperSpine S) (pT : ProperSpine T)
    (Γ : Shape C) {α : C.Arity} (x : T ∋ α) :
    inr (append pS pT) Γ (inr pT S x) =
      inr pT (Γ ⧺ S) x := by
  induction pT generalizing Γ α with
  | nil => cases x
  | cons pT β ih =>
      cases x with
      | here i => rfl
      | there x =>
          exact congrArg ListSlotAt.there (ih Γ x)

/-- Turn a canonical spine into the existing compatibility `Proper` witness. -/
@[reducible]
def toProper {C : Carrier} {S : Shape C} :
    ProperSpine S → Proper S
  | .nil => Proper.instId
  | .cons p α =>
      letI : Proper _ := toProper p
      Proper.instCons α _

end ProperSpine

@[inherit_doc Proper.inl]
notation:max "ι₁ " x:max => Proper.inl _ x

@[inherit_doc Proper.inr]
notation:max "ι₂ " x:max => Proper.inr _ x
