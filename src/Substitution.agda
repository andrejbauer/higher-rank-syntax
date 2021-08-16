open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

import Syntax
import Renaming

module Substitution (Class : Set) where

  open Syntax Class
  open Renaming Class

  -- the set of substitutions

  infix 5 _→ˢ_

  _→ˢ_ : Shape → Shape → Set
  _→ˢ_ Γ Δ = ∀ {Θ : Shape} {A} (x : [ Θ , A ]∈ Γ) → Expr (Δ ⊕ Θ) A

  -- equality of substitutions

  infix 4 _≈ˢ_

  _≈ˢ_ : ∀ {Γ : Shape} {Δ : Shape} (f g : Γ →ˢ Δ) → Set
  _≈ˢ_ {Γ = Γ} f g = ∀ {Θ : Shape} {A} (x : [ Θ , A ]∈ Γ) → f x ≈ g x

  -- equality of substitutions is an equivalence relation

  ≈ˢ-refl : ∀ {Γ : Shape} {Δ : Shape} {f : Γ →ˢ Δ} → f ≈ˢ f
  ≈ˢ-refl x = ≈-refl

  ≈ˢ-sym : ∀ {Γ : Shape} {Δ : Shape} {f g : Γ →ˢ Δ} → f ≈ˢ g → g ≈ˢ f
  ≈ˢ-sym ξ x = ≈-sym (ξ x)

  ≈ˢ-trans : ∀ {Γ : Shape} {Δ : Shape} {f g h : Γ →ˢ Δ} → f ≈ˢ g → g ≈ˢ h → f ≈ˢ h
  ≈ˢ-trans ζ ξ x = ≈-trans (ζ x) (ξ x)

  -- identity substitution

  2-3 : ∀ {Γ Δ Θ} → Γ ⊕ Θ →ʳ (Γ ⊕ Δ) ⊕ Θ
  2-3 (var-left x) = var-left (var-left x)
  2-3 (var-right y) = var-right y

  shift : ∀ {Γ : Shape} {Δ : Shape} {Θ : Shape} → Δ ⊕ Θ →ʳ (Γ ⊕ Δ) ⊕ Θ
  shift (var-left x) = var-left (var-right x)
  shift (var-right y) = var-right y

  -- 𝟙ˢ : ∀ {Γ : Shape} {Θ : Shape} {A} → [ Θ , A ]∈ Γ → Expr (Γ ⊕ Θ) A
  -- 𝟙ˢ {Γ} {Θ} {A} x = var-left x ` (λ { y → [ shift ]ʳ 𝟙ˢ {!!} })

  -- -- substitution extension

  -- ⇑ˢ : ∀ {Γ Δ Θ} → Γ →ˢ Δ → Γ ⊕ Θ →ˢ Δ ⊕ Θ
  -- ⇑ˢ f (var-left x) =  [ 2-3 ]ʳ f x
  -- ⇑ˢ f (var-right y) =  [ shift ]ʳ  𝟙ˢ y
