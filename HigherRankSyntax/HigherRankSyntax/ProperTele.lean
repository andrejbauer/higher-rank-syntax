import HigherRankSyntax.Renaming

/-!
# Proper Telescopes

A type class on `Tele C.Arity` exhibiting `Γ ⋈ Δ` as a coproduct, providing the structural
operations needed to dispatch a slot of `Γ ⋈ Δ` between the Γ-side and the Δ-side:

* `inl Γ` — left injection of the base `Γ` into `Γ ⋈ Δ` (weakening).
* `inr Γ` — right injection of the telescope `Δ` into `Γ ⋈ Δ`.
* `classify Γ` — CPS dispatch of a `Γ ⋈ Δ`-slot to either side.
* `classify_inr`, `classify_inl` — reflection lemmas.
* `cover` — every slot of `Γ ⋈ Δ` is in the image of exactly one of `inl`, `inr`
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
`∀ Δ, Γ Δ = Γ.toList ⋈ Δ` (or to bundle it into `Tele` itself) and derive
the structural operations from it.  That suffices *mathematically* — for
left-action telescopes (our convention, with `Γ.toList` prepended to the
input) this equation is exactly what "Γ behaves like a fixed prefix" means.
But slot dispatch then has to fire `Eq.rec` along the equation in order to
turn a `Γ ⋈ Δ ∋ α` into a `Γ.toList ⋈ Δ ∋ α`, and the resulting transports
permeate every `Expr`-rebuilding step downstream.

`Proper` instead exhibits the iso `Γ ⋈ Δ ≅ Γ.toList ⋈ Δ` *structurally*, as
the four maps `inl / inr / classify / cover` with their reflection equations.
Slot dispatch and downstream code then stay transport-free.  For telescopes
built from `Tele.id`, `Tele.cons`, and `∘ᵗ` the equation already holds by
`rfl`, so the class is just naming the structural witness that the standard
generators already supply.

Side note on the cons-induction equation: `Γ (α :: Δ) = α :: Γ Δ` does *not*
characterise the left-action form `Γ Δ = Γ.toList ⋈ Δ` (the inductive step
fails: `α :: (Γ.toList ⋈ Δ') ≠ Γ.toList ⋈ (α :: Δ')` in general).  It
characterises the right-action form `Γ Δ = Δ ⋈ Γ.toList`.  We use left
action because that is what makes `(Γ ∷ α).toList = α :: Γ.toList` reduce by
`rfl`, which the cons-style `ListSlotAt` needs.
-/


/-- A `Proper` instance exhibits `Γ ⋈ S` as a coproduct
(fibrewise per arity): two injection renamings and a classifier, so that
a slot of `Γ ⋈ S` dispatches uniformly between Γ-slots and S-slots. -/
class Proper {C : Carrier} (Γ : Tele C.Arity) : Type 1 where
  /-- Left injection, i.e, weakening Δ ↪ Δ ⋈ S. -/
  inl : (Δ : Shape C) → Δ →ʳ (Δ ⋈ Γ)
  /-- Right injection: the telescope's own shape `Γ` into `Δ ⋈ Γ`. -/
  inr : (Δ : Shape C) → Γ →ʳ (Δ ⋈ Γ)
  /-- Classifier (CPS): dispatch a slot of `Δ ⋈ Γ` into either a Δ-slot
  or a Γ-slot. -/
  -- TODO: reverse the order of arguments, it's stupid to take in the right one first
  classify : (Δ : Shape C) → {α : C.Arity} → (X : Type) → (Δ ⋈ Γ) ∋ α →
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
  cover : ∀ (Δ : Shape C) {α : C.Arity} (p : (Δ ⋈ Γ) ∋ α),
          (∃ x : Γ ∋ α, p = inr Δ x) ∨ (∃ y : Δ ∋ α, p = inl Δ y)
  /-- The right injection at empty base is the identity renaming. -/
  inr_nil_id : ∀ {α : C.Arity} (x : Γ ∋ α),
    inr .nil x = x

namespace Proper

/-- The identity telescope: empty; the classifier returns everything to Γ. -/
instance instId {C : Carrier} : Proper (Tele.id : Tele C.Arity) where
  inl := fun Γ => Renaming.id Γ
  inr := fun _ {_} x => nomatch x
  classify := fun _Γ _α _X p _f g => g p
  classify_inr := fun _Γ _X _α x _f _g => nomatch x
  classify_inl := fun _Γ _X _α _y _f _g => rfl
  cover := fun _Γ _α p => Or.inr ⟨p, rfl⟩
  inr_nil_id := fun x => nomatch x

/-- Extend a `Proper` by one arity at the top. -/
instance instCons {C : Carrier} (a : C.Arity) (T : Tele C.Arity) [Proper T] :
    Proper (Tele.cons a ∘ᵗ T) where
  inl := fun Γ {_} x => .there (Proper.inl Γ x)
  inr := fun Γ {_} x =>
    match x with
    | .here i  => .here i
    | .there x => .there (Proper.inr Γ x)
  classify := fun Γ _α X p f g =>
    match p with
    | .here i   => f (.here i)
    | .there p' => Proper.classify Γ X p' (fun y => f (.there y)) g
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
    (ρ : List C.Arity) → Proper (S ⋈ Tele.ofList ρ)
  | [] => inferInstanceAs (Proper S)
  | β :: rest =>
      letI : Proper (S ⋈ Tele.ofList rest) := extendList S rest
      inferInstanceAs (Proper ((S ⋈ Tele.ofList rest) ∷ β))

/-- A concrete list of binders is a proper telescope. -/
@[reducible]
def ofList {C : Carrier} (ρ : List C.Arity) :
    Proper (Tele.ofList ρ : Shape C) :=
  extendList (Shape.nil : Shape C) ρ

/-- Instance form of `extendList` so typeclass synthesis can supply
`Proper (Γ ⋈ Tele.ofList ρ)` automatically whenever `Γ` is already a proper
telescope. -/
@[reducible]
instance instExtendList {C : Carrier} (Γ : Shape C) [Proper Γ]
    (ρ : List C.Arity) :
    Proper (Γ ⋈ Tele.ofList ρ) :=
  extendList Γ ρ

/-- Instance form of `ofList` so typeclass synthesis can supply
`Proper (Tele.ofList ρ)` automatically. -/
@[reducible]
instance instOfList {C : Carrier} (ρ : List C.Arity) :
    Proper (Tele.ofList ρ : Shape C) :=
  ofList ρ

/-- In a concrete list extension, the right injection of a list-side slot is
the same as first injecting it into `S ⋈ Tele.ofList ρ` and then injecting the
composite. -/
theorem extendList_inr_inr {C : Carrier} (S : Shape C) [Proper S]
    (ρ : List C.Arity) (Γ : Shape C)
    {α : C.Arity} (x : Tele.ofList ρ ∋ α) :
  Proper.inr Γ (Proper.inr S x) = Proper.inr (Γ ⋈ S) x
  := by
  induction ρ with
  | nil => exact nomatch x
  | cons β rest ih =>
      cases x with
      | here i => rfl
      | there x' =>
          change
            ListSlotAt.there
              ((Proper.inr Γ : S ⋈ Tele.ofList rest →ʳ
                Γ ⋈ (S ⋈ Tele.ofList rest))
                ((Proper.inr S : Tele.ofList rest →ʳ
                  S ⋈ Tele.ofList rest) x'))
            =
            ListSlotAt.there
              ((Proper.inr (Γ ⋈ S) : Tele.ofList rest →ʳ
                (Γ ⋈ S) ⋈ Tele.ofList rest) x')
          congr 1
          exact ih x'

/-- In a concrete list extension, the right injection of an `S`-slot into the
composite is the same as injecting it into the base and then weakening through
the list. -/
theorem extendList_inr_inl {C : Carrier} (S : Shape C) [Proper S]
    (ρ : List C.Arity) (Γ : Shape C)
    {α : C.Arity} (x : S ∋ α) :
  Proper.inr Γ (Proper.inl (Γ := Tele.ofList ρ) S x) = Proper.inl (Γ ⋈ S) (Proper.inr Γ x)
  := by
  induction ρ with
  | nil =>
      change (Proper.inr Γ) x = (Proper.inr Γ) x
      rfl
  | cons β rest ih =>
      change
        ListSlotAt.there
          ((Proper.inr Γ : S ⋈ Tele.ofList rest →ʳ
            Γ ⋈ (S ⋈ Tele.ofList rest))
            ((Proper.inl S : S →ʳ S ⋈ Tele.ofList rest) x))
        =
        ListSlotAt.there
          ((Proper.inl (Γ ⋈ S) : Γ ⋈ S →ʳ
            (Γ ⋈ S) ⋈ Tele.ofList rest)
            ((Proper.inr Γ : S →ʳ Γ ⋈ S) x))
      congr 1

/-- Weakening through a concrete list extension is the iterated weakening
through that list. -/
theorem extendList_inl
    {C : Carrier} (S : Shape C) [Proper S]
    (ρ : List C.Arity) (Γ : Shape C)
    {α : C.Arity} (x : Γ ∋ α) :
  Proper.inl (Γ := S ⋈ Tele.ofList ρ) Γ x = Proper.inl (Γ ⋈ S) (Proper.inl Γ x)
  := by
  induction ρ with
  | nil => rfl
  | cons β rest ih =>
      change
        ListSlotAt.there
          ((Proper.inl Γ : Γ →ʳ Γ ⋈ (S ⋈ Tele.ofList rest)) x)
        =
        ListSlotAt.there
          ((Proper.inl (Γ ⋈ S) : Γ ⋈ S →ʳ
            (Γ ⋈ S) ⋈ Tele.ofList rest)
            ((Proper.inl Γ : Γ →ʳ Γ ⋈ S) x))
      congr 1

/-- Compose two proper telescopes, keeping the structural operations coherent
with the two-stage view of `(Γ ⋈ S) ⋈ T`.  This is deliberately a named
constructor rather than a global instance, to avoid making typeclass search
try arbitrary telescope decompositions. -/
@[reducible]
def compose {C : Carrier} (S T : Shape C) [Proper S] [Proper T] :
    Proper (S ⋈ T) where

  inl := fun Γ =>
    (Proper.inl (Γ ⋈ S) : Γ ⋈ S →ʳ (Γ ⋈ S) ⋈ T) ∘ʳʳ
      (Proper.inl Γ : Γ →ʳ Γ ⋈ S)

  inr := fun Γ {_} p =>
    Proper.classify S _ p
      (fun t => Proper.inr (Γ ⋈ S) t)
      (fun s => Proper.inl (Γ ⋈ S) (Proper.inr Γ s))

  classify := fun Γ _α X p f g =>
    Proper.classify (Γ ⋈ S) X p
      (fun t => f (Proper.inr S t))
      (fun q => Proper.classify Γ X q
        (fun s => f (Proper.inl S s))
        g)

  classify_inr := fun Γ X _α x f g => by
    rcases Proper.cover S x with ⟨t, h_t⟩ | ⟨s, h_s⟩
    · subst h_t
      simp only [Proper.classify_inr]
    · subst h_s
      simp only [Proper.classify_inl, Proper.classify_inr]

  classify_inl := fun Γ X _α y f g => by
    change
      Proper.classify (Γ ⋈ S) X
        ((Proper.inl (Γ ⋈ S)) ((Proper.inl Γ) y))
        (fun t => f ((Proper.inr S) t))
        (fun q => Proper.classify Γ X q
          (fun s => f ((Proper.inl S) s)) g)
      =
      g y
    rw [Proper.classify_inl (Γ ⋈ S)]
    rw [Proper.classify_inl Γ]
  cover := fun Γ _α p => by
    rcases Proper.cover (Γ ⋈ S) p with ⟨t, h_t⟩ | ⟨q, h_q⟩
    · refine Or.inl ⟨(Proper.inr S) t, ?_⟩
      subst h_t
      simp only [Proper.classify_inr]
    · subst h_q
      rcases Proper.cover Γ q with ⟨s, h_s⟩ | ⟨y, h_y⟩
      · refine Or.inl ⟨(Proper.inl S) s, ?_⟩
        subst h_s
        simp only [Proper.classify_inl]
      · refine Or.inr ⟨y, ?_⟩
        subst h_y
        rfl
  inr_nil_id := fun {_α} x => by
    rcases Proper.cover S x with ⟨t, h_t⟩ | ⟨s, h_s⟩
    · subst h_t
      simp only [Proper.classify_inr]
      rfl
    · subst h_s
      simp only [Proper.classify_inl, Proper.inr_nil_id]
      rfl

/-- In the composed `Proper`, the right injection of a `T`-slot factors
through `S ⋈ T`: `inr` after `inr` is the two-stage right injection. -/
theorem compose_inr_inr {C : Carrier} (S T : Shape C)
    [Proper S] [Proper T] (Γ : Shape C)
    {α : C.Arity} (x : T ∋ α) :
    letI : Proper (S ⋈ T) := Proper.compose S T
    (Proper.inr Γ : (S ⋈ T) →ʳ Γ ⋈ (S ⋈ T))
      ((Proper.inr S : T →ʳ S ⋈ T) x)
      =
    (Proper.inr (Γ ⋈ S) : T →ʳ (Γ ⋈ S) ⋈ T) x := by
  exact Proper.classify_inr S _ x _ _

/-- In the composed `Proper`, the right injection of an `inl_S`-slot is
the base right injection followed by weakening (`inl`) through `T`. -/
theorem compose_inr_inl {C : Carrier} (S T : Shape C)
    [Proper S] [Proper T] (Γ : Shape C)
    {α : C.Arity} (x : S ∋ α) :
    letI : Proper (S ⋈ T) := Proper.compose S T
    (Proper.inr Γ : (S ⋈ T) →ʳ Γ ⋈ (S ⋈ T))
      ((Proper.inl S : S →ʳ S ⋈ T) x)
      =
    (Proper.inl (Γ ⋈ S) : Γ ⋈ S →ʳ (Γ ⋈ S) ⋈ T)
      ((Proper.inr Γ : S →ʳ Γ ⋈ S) x) := by
  exact Proper.classify_inl S _ x _ _

/-- Weakening (`inl`) through the composed `Proper` is the two-stage
weakening through its factors. -/
theorem compose_inl {C : Carrier} (S T : Shape C)
    [Proper S] [Proper T] (Γ : Shape C)
    {α : C.Arity} (x : Γ ∋ α) :
    letI : Proper (S ⋈ T) := Proper.compose S T
    (Proper.inl Γ : Γ →ʳ Γ ⋈ (S ⋈ T)) x
      =
    (Proper.inl (Γ ⋈ S) : Γ ⋈ S →ʳ (Γ ⋈ S) ⋈ T)
      ((Proper.inl Γ : Γ →ʳ Γ ⋈ S) x) := by
  rfl

/-- Coherence data for a chosen `Proper (S ⋈ T)` witness.

This is proof-facing infrastructure for code that must use a specific
composite witness instead of letting typeclass search pick an extensionally
equal one.  The three fields say how the chosen witness's injections agree
with the two-step view through `S` and then `T`.
-/
structure AppendCoherence {C : Carrier} {S T : Shape C}
    [hS : Proper S] [hT : Proper T] (hST : Proper (S ⋈ T)) where
  /-- A right-side `T` head agrees with the two-stage right injection. -/
  inr_right : ∀ (Γ : Shape C) {α : C.Arity} (x : T ∋ α),
    (@Proper.inr C (S ⋈ T) hST Γ)
      ((@Proper.inr C T hT S) x)
    =
    (@Proper.inr C T hT (Γ ⋈ S)) x
  /-- A left-side `S` head agrees with right injection into `S`, then left
  injection through `T`. -/
  inr_left : ∀ (Γ : Shape C) {α : C.Arity} (x : S ∋ α),
    (@Proper.inr C (S ⋈ T) hST Γ)
      ((@Proper.inl C T hT S) x)
    =
    (@Proper.inl C T hT (Γ ⋈ S))
      ((@Proper.inr C S hS Γ) x)
  /-- External prefix weakening through the composite agrees with weakening in
  two stages. -/
  inl : ∀ (Γ : Shape C) {α : C.Arity} (x : Γ ∋ α),
    (@Proper.inl C (S ⋈ T) hST Γ) x
    =
    (@Proper.inl C T hT (Γ ⋈ S))
      ((@Proper.inl C S hS Γ) x)

/-- Extend a chosen composite witness through a concrete argument list. -/
abbrev underList {C : Carrier} {S T : Shape C}
    (hST : Proper (S ⋈ T)) (υ : List C.Arity) :
    Proper ((S ⋈ T) ⋈ Tele.ofList υ) :=
  @Proper.extendList C (S ⋈ T) hST υ

/-- Extend a chosen composite witness under one fresh application argument. -/
abbrev underBinder {C : Carrier} {S T : Shape C}
    (hST : Proper (S ⋈ T)) (β : C.Arity) :
    Proper ((S ⋈ T) ∷ β) :=
  @Proper.instCons C β (S ⋈ T) hST

/-- Append coherence for the ordinary `Proper.compose` witness. -/
abbrev AppendCoherence.compose {C : Carrier}
    (S T : Shape C) [hS : Proper S] [hT : Proper T] :
    AppendCoherence (Proper.compose S T) where
  inr_right := Proper.compose_inr_inr S T
  inr_left := Proper.compose_inr_inl S T
  inl := Proper.compose_inl S T

/-- Append coherence for `Shape.nil ⋈ T`, where the composite witness is just
the right-hand witness. -/
abbrev AppendCoherence.nil {C : Carrier}
    (T : Shape C) [hT : Proper T] :
    AppendCoherence (S := Shape.nil) (T := T) hT where
  inr_right := by
    intro Γ α x
    rw [Proper.inr_nil_id x]
    rfl
  inr_left := by
    intro Γ α x
    nomatch x
  inl := by
    intro Γ α x
    rfl

/-- Append coherence for concrete-list extension. -/
abbrev AppendCoherence.extendList {C : Carrier}
    (S : Shape C) [hS : Proper S] (ρ : List C.Arity) :
    AppendCoherence (Proper.extendList S ρ) where
  inr_right := Proper.extendList_inr_inr S ρ
  inr_left := Proper.extendList_inr_inl S ρ
  inl := Proper.extendList_inl S ρ

/-- Append coherence for appending a singleton binder with the computation rule
used by application-argument recursion. -/
abbrev AppendCoherence.singleton {C : Carrier}
    (S : Shape C) [hS : Proper S] (β : C.Arity) :
    AppendCoherence (@Proper.instCons C β S hS) where
  inr_right := by
    intro Γ α x
    cases x with
    | here i => rfl
    | there z => nomatch z
  inr_left := by
    intro Γ α x
    rfl
  inl := by
    intro Γ α x
    rfl

end Proper

@[inherit_doc Proper.inl]
notation:max "ι₁ " x:max => Proper.inl _ x

@[inherit_doc Proper.inr]
notation:max "ι₂ " x:max => Proper.inr _ x
