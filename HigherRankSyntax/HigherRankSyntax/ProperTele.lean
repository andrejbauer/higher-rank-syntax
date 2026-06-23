import HigherRankSyntax.Renaming

/-!
# Proper Telescopes

A type class on `Shape C` exhibiting `Γ ⋈ Δ` as a coproduct, providing the structural
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
* `Tele.cons a ∘ᵗ T` from `[Proper T]` — extend by one position.

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
class Proper {C : Carrier} (Γ : Shape C) : Type 1 where
  /-- Left injection, i.e, weakening Δ ↪ Δ ⋈ S. -/
  inl : (Δ : Shape C) → Δ →ʳ (Δ ⋈ Γ)
  /-- Right injection: the telescope's own shape `Γ` into `Δ ⋈ Γ`. -/
  inr : (Δ : Shape C) → Γ →ʳ (Δ ⋈ Γ)
  /-- Classifier (CPS): dispatch a slot of `Δ ⋈ Γ` into either a Δ-slot
  or a Γ-slot. -/
  classify : (Δ : Shape C) → {α : C.Arity} → (X : Type) → (Δ ⋈ Γ) ∋ α →
             (Δ ∋ α → X) → (Γ ∋ α → X) → X
  /-- Reflection: classifying a right-injected S-slot fires the S-continuation. -/
  classify_inr : ∀ (Δ : Shape C) (X : Type) {α : C.Arity} (x : Γ ∋ α)
                   (g : Δ ∋ α → X) (f : Γ ∋ α → X),
                   classify Δ X (inr Δ x) g f = f x
  /-- Reflection: classifying a left-injected Δ-slot fires the Δ-continuation. -/
  classify_inl : ∀ (Δ : Shape C) (X : Type) {α : C.Arity} (y : Δ ∋ α)
                   (g : Δ ∋ α → X) (f : Γ ∋ α → X),
                   classify Δ X (inl Δ y) g f = g y
  /-- Cover: every slot is in the image of `inr` or `inl`. -/
  cover : ∀ (Δ : Shape C) {α : C.Arity} (p : (Δ ⋈ Γ) ∋ α),
          (∃ x : Γ ∋ α, p = inr Δ x) ∨ (∃ y : Δ ∋ α, p = inl Δ y)
  /-- The right injection at empty base is the identity renaming. -/
  inr_nil_id : ∀ {α : C.Arity} (x : Γ ∋ α),
    inr .nil x = x
  /-- `inr` injects `Γ`-slots into the prefix, preserving position. -/
  inr_idx : ∀ (Δ : Shape C) {α : C.Arity} (x : Γ ∋ α),
    (inr Δ x).idx = x.idx
  /-- `inr` preserves the position a slot picks out. -/
  inr_tag : ∀ (Δ : Shape C) {α : C.Arity} (x : Γ ∋ α),
    (inr Δ x).tag = x.tag
  /-- `inl` weakens `Δ`-slots past the `Γ`-prefix, shifting position. -/
  inl_idx : ∀ (Δ : Shape C) {α : C.Arity} (y : Δ ∋ α),
    (inl Δ y).idx = Γ.toList.length + y.idx
  /-- `inl` preserves the position a slot picks out. -/
  inl_tag : ∀ (Δ : Shape C) {α : C.Arity} (y : Δ ∋ α),
    (inl Δ y).tag = y.tag

namespace Proper

/-- Two `Proper` witnesses on the same shape agree once their data fields do;
the propositional fields are irrelevant. -/
theorem ext_data {C : Carrier} {Γ : Shape C} (P Q : Proper Γ)
    (hl : P.inl = Q.inl) (hr : P.inr = Q.inr) (hc : P.classify = Q.classify) : P = Q := by
  cases P; cases Q
  subst hl; subst hr; subst hc
  rfl

/-- `Proper Γ` is a subsingleton: the pin fields force the injections, the
reflection laws then force the classifier, and the remaining fields are `Prop`. -/
instance subsingleton {C : Carrier} (Γ : Shape C) : Subsingleton (Proper Γ)
  := by
    constructor ; intro P Q
    have hl : P.inl = Q.inl := by
      funext Δ; ext α y
      apply ListSlotAt.ext
      · rw [P.inl_idx, Q.inl_idx]
      · rw [P.inl_tag, Q.inl_tag]
    have hr : P.inr = Q.inr := by
      funext Δ; ext α x
      apply ListSlotAt.ext
      · rw [P.inr_idx, Q.inr_idx]
      · rw [P.inr_tag, Q.inr_tag]
    have hc : P.classify = Q.classify := by
      funext Δ α X p g f
      rcases P.cover Δ p with ⟨x, rfl⟩ | ⟨y, rfl⟩
      · rw [P.classify_inr, hr, Q.classify_inr]
      · rw [P.classify_inl, hl, Q.classify_inl]
    exact ext_data P Q hl hr hc

/-- The identity telescope: empty; the classifier returns everything to Γ. -/
instance instId {C : Carrier} : Proper (Tele.id C.Arity) where
  inl := fun Γ => Renaming.id Γ
  inr := fun _ {_} x => nomatch x
  classify := fun _Γ _α _X p g _f => g p
  classify_inr := fun _Γ _X _α x _g _f => nomatch x
  classify_inl := fun _Γ _X _α _y _g _f => rfl
  cover := fun _Γ _α p => Or.inr ⟨p, rfl⟩
  inr_nil_id := fun x => nomatch x
  inr_idx := fun _ => nofun
  inr_tag := fun _ => nofun
  inl_idx := fun _ _ y => (Nat.zero_add y.idx).symm
  inl_tag := fun _ _ _ => rfl

/-- Extend a `Proper` by one arity at the top. -/
instance instCons {C : Carrier} (a : C.Arity) (T : Shape C) [Proper T] :
    Proper (Tele.cons a ∘ᵗ T) where
  inl := fun Γ {_} x => .there (Proper.inl Γ x)
  inr := fun Γ {_} x =>
    match x with
    | .here i  => .here i
    | .there x => .there (Proper.inr Γ x)
  classify := fun Γ _α X p g f =>
    match p with
    | .here i   => f (.here i)
    | .there p' => Proper.classify Γ X p' g (fun y => f (.there y))
  classify_inr := fun Γ X _α x g f => by
    cases x with
    | here _i  => rfl
    | there x' =>
      exact Proper.classify_inr Γ X x'
              g (fun y => f (.there y))
  classify_inl := fun Γ X _α y g f => by
    exact Proper.classify_inl Γ X y
            g (fun z => f (.there z))
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
  inr_idx := fun Δ _ x => by
    cases x with
    | here i => rfl
    | there x' => exact congrArg (· + 1) (Proper.inr_idx Δ x')
  inr_tag := fun Δ _ x => by
    cases x with
    | here i => rfl
    | there x' => exact Proper.inr_tag Δ x'
  inl_idx := fun Δ _ y =>
    (congrArg (· + 1) (Proper.inl_idx (Γ := T) Δ y)).trans (Nat.add_right_comm _ _ 1)
  inl_tag := fun Δ _ y => Proper.inl_tag Δ y

/-- Compose two proper telescopes, keeping the structural operations coherent
with the two-stage view of `(Γ ⋈ S) ⋈ T`.  This is deliberately a named
constructor rather than a global instance, to avoid making typeclass search
try arbitrary telescope decompositions. -/
@[reducible]
def compose {C : Carrier} (S T : Shape C) [Proper S] [Proper T] :
    Proper (S ⋈ T) where

  inl Γ := inl (Γ ⋈ S) ∘ʳ inl Γ

  inr Γ {_} x :=
    classify S _ x
      (fun y => inl (Γ ⋈ S) (inr Γ y))
      (fun z => inr (Γ ⋈ S) z)

  classify Γ _ X x g f :=
    classify (Γ ⋈ S) X x
      (fun y => classify Γ X y g (fun w => f (inl S w)))
      (fun z => f (inr S z))

  classify_inr Γ X _ x g f := by
    rcases cover S x with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · simp only [classify_inr]
    · simp only [classify_inl, classify_inr]

  classify_inl := fun Γ X _α y g f =>
    (classify_inl (Γ ⋈ S) X ((inl Γ) y) _ _).trans
      (classify_inl Γ X y g _)

  cover Γ {_} p := by
    rcases cover (Γ ⋈ S) p with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · left ; exists (inr _ x) ; simp only [classify_inr]
    · rcases cover Γ y with ⟨y, rfl⟩ | ⟨z, rfl⟩
      · left
        exists (inl _ y)
        simp only [classify_inl]
      · right ; exists z

  inr_nil_id {_α} x := by
    rcases cover S x with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · simp only [classify_inr] ; rfl
    · simp only [classify_inl, inr_nil_id] ; rfl

  inr_idx Δ _ p := by
    rcases cover (Γ := T) S p with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · rw [classify_inr]
      apply Eq.trans
      · apply inr_idx
      · symm ; apply inr_idx
    · rw [classify_inl]
      calc ((inl (Δ ⋈ S)) ((inr Δ) y)).idx
          = _  := by rw [inl_idx, inr_idx]
        _ = _  := by symm ; apply inl_idx

  inr_tag Δ _ p := by
    rcases cover (Γ := T) S p with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · rw [classify_inr]
      apply Eq.trans
      · apply inr_tag
      · symm ; apply inr_tag
    · rw [classify_inl]
      calc ((inl (Δ ⋈ S)) ((inr Δ) y)).tag
          = _      := by rw [inl_tag, inr_tag]
        _ = _      := by symm ; apply inl_tag

  inl_idx Δ _ y :=
    calc ((inl (Δ ⋈ S)) ((inl Δ) y)).idx
        = _ := by apply inl_idx
      _ = _ := by rw [inl_idx Δ y]
      _ = _ := by rw [Shape.extList_toList, List.length_append] ; symm ; apply Nat.add_assoc

  inl_tag Δ _ y := by apply Eq.trans <;> apply inl_tag

/-- `Proper.compose`'s right injection of a `Ξ`-slot factors through `Δ ⋈ Ξ`. -/
theorem inr_inr {C : Carrier} (Δ Ξ : Shape C) [Proper Δ] [Proper Ξ]
    (Γ : Shape C) {α : C.Arity} (x : Ξ ∋ α) :
  (Proper.compose Δ Ξ).inr Γ (Proper.inr Δ x) = Proper.inr (Γ ⋈ Δ) x
  := Proper.classify_inr Δ _ x _ _

/-- In the composed `Proper`, the right injection of an `inl_Δ`-slot is
the base right injection followed by weakening (`inl`) through `Ξ`. -/
theorem inr_inl {C : Carrier} (Δ Ξ : Shape C)
    [Proper Δ] [Proper Ξ] (Γ : Shape C)
    {α : C.Arity} (x : Δ ∋ α) :
    (Proper.compose Δ Ξ).inr Γ (Proper.inl Δ x)
      = Proper.inl (Γ ⋈ Δ) (Proper.inr Γ x)
  := Proper.classify_inl Δ _ x _ _

/-- Weakening (`inl`) through the composed `Proper` is the two-stage
weakening through its factors. -/
theorem inl_inl {C : Carrier} (Δ Ξ : Shape C)
    [Proper Δ] [Proper Ξ] (Γ : Shape C)
    {α : C.Arity} (x : Γ ∋ α) :
    (Proper.compose Δ Ξ).inl Γ x = Proper.inl (Γ ⋈ Δ) (Proper.inl Γ x)
  := rfl

end Proper

@[inherit_doc Proper.inl]
notation:max "ι₁ " x:max => Proper.inl _ x

@[inherit_doc Proper.inr]
notation:max "ι₂ " x:max => Proper.inr _ x
