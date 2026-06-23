open import Agda.Primitive
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Induction.WellFounded

-- This is the same as Induction.WellFounded.Fixpoint, but works for any
-- relation that is preserved by the recursor, instead of just ≡

module FixPointRel
  {a r e} {A : Set a}
  {_<_ : Rel A r} (wf : WellFounded _<_) ℓ
  (P : Pred A ℓ) (f : WfRec _<_ P ⊆′ P)
  (_≈_ : ∀ {x : A} → Rel (P x) e)
  (f-ext : (x : A) {IH IH′ : WfRec _<_ P x} → (∀ {y} y<x → IH y y<x ≈ IH′ y y<x) → f x IH ≈ f x IH′)
  where

  some-wfRec-irrelevant : ∀ x → (q q′ : Acc _<_ x) → Some.wfRec P f x q ≈ Some.wfRec P f x q′
  some-wfRec-irrelevant =
    All.wfRec wf _
      (λ x → (q q′ : Acc _<_ x) → Some.wfRec P f x q ≈ Some.wfRec P f x q′)
      (λ { x IH (acc rs) (acc rs′) → f-ext x (λ y<x → IH _ y<x (rs _ y<x) (rs′ _ y<x)) })

  open All wf ℓ
  wfRecBuilder-wfRec : ∀ {x y} y<x → wfRecBuilder P f x y y<x ≈ wfRec P f y
  wfRecBuilder-wfRec {x} {y} y<x with wf x
  ... | acc rs = some-wfRec-irrelevant y (rs y y<x) (wf y)

  unfold-wfRec : ∀ {x} → wfRec P f x ≈ f x (λ y _ → wfRec P f y)
  unfold-wfRec {x} = f-ext x wfRecBuilder-wfRec
