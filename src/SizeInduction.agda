open import Agda.Primitive
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Induction.WellFounded

-- Recursive definitions in which recursive calls reduce well-founded size

module SizeInduction
  {ℓs ℓr ℓa}
  {S : Set ℓs} -- size
  {_<_ : S → S → Set ℓr} (wf-< : WellFounded _<_) -- well-founded size order
  {A : Set ℓa}
  (size : A → S) {ℓp}
  (P : A → Set ℓp)
  (f : ∀ x → (∀ y → size y < size x → P y) → P x)
  where

  open All wf-< (ℓs ⊔ ℓa ⊔ ℓp)

  -- We actually carry out well-founded induction on Q
  Q : S → Set (ℓs ⊔ ℓa ⊔ ℓp)
  Q = (λ s → ∀ x → size x ≡ s → P x)

  -- The recursive builder
  q : ∀ (s : S) (r : ∀ t → t < s → Q t) (x : A) (ξ : size x ≡ s) → P x
  q s r x ξ = f x (λ y p → r (size y) (subst (λ t → size y < t) ξ p) y refl)

  -- The recursive construction
  sizeRec : ∀ x → P x
  sizeRec x = wfRec Q q (size x) x refl

  -- The desired fixed-point equation with respect to any binary relation
  module SizeFixPoint
    {ℓe} (_≈_ : ∀ {x : A} → P x → P x → Set ℓe)
    (f-ext : ∀ x {r₁ r₂ : ∀ y → size y < size x → P y} → (∀ {y} p₁ p₂ → r₁ y p₁ ≈ r₂ y p₂) → f x r₁ ≈ f x r₂)
    where

    -- the derived relation, suitable for q

    _≈'_ : ∀ {s : S} (g₁ g₂ : ∀ (x : A) (ξ : size x ≡ s) → P x) → Set (ℓs ⊔ ℓa ⊔ ℓe)
    g₁ ≈' g₂ = ∀ (x : A) (ξ : size x ≡ _) → g₁ x ξ ≈ g₂ x ξ

    -- the rest is adapted from WellFounded.FixPoint

    some-wfRec-irrelevant : ∀ s → (u₁ u₂ : Acc _<_ s) → Some.wfRec Q q s u₁ ≈' Some.wfRec Q q s u₂
    some-wfRec-irrelevant =
      All.wfRec wf-< _
        (λ s → (u₁ u₂ : Acc _<_ s) → Some.wfRec Q q s u₁ ≈' Some.wfRec Q q s u₂)
        (λ { s IH (acc us₁) (acc us₂) →
           λ x ξ → f-ext x λ p₁ p₂ → IH _ (subst (λ t → _ < t) ξ p₁) (us₁ _ _) (us₂ _ _) _ refl})

    wfRecBuilder-wfRec : ∀ {x y} y<x → wfRecBuilder Q q x y y<x ≈' wfRec Q q y
    wfRecBuilder-wfRec {x} {y} y<x with wf-< x
    ... | acc rs = some-wfRec-irrelevant y (rs y y<x) (wf-< y)

    -- the fixed point equation

    unfold-sizeRec : ∀ x → sizeRec x ≈ f x λ y _ → sizeRec y
    unfold-sizeRec x = f-ext x (λ p₁ p₂ → wfRecBuilder-wfRec p₁ _ refl)
