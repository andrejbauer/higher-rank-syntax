open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

import Syntax
import Renaming

module Substitution (Class : Set) where

  open Syntax Class
  open Renaming Class

  -- the set of substitutions

  infix 5 _→ˢ_

  _→ˢ_ : Shape → Shape → Set
  _→ˢ_ Γ Δ = ∀ {Θ} {A} (x : [ Θ , A ]∈ Γ) → Expr (Δ ⊕ Θ) A

  -- equality of substitutions

  infix 4 _≈ˢ_

  _≈ˢ_ : ∀ {Γ} {Δ} (f g : Γ →ˢ Δ) → Set
  _≈ˢ_ {Γ = Γ} f g = ∀ {Θ} {A} (x : [ Θ , A ]∈ Γ) → f x ≈ g x

  -- equality of substitutions is an equivalence relation

  ≈ˢ-refl : ∀ {Γ} {Δ} {f : Γ →ˢ Δ} → f ≈ˢ f
  ≈ˢ-refl x = ≈-refl

  ≈ˢ-sym : ∀ {Γ} {Δ} {f g : Γ →ˢ Δ} → f ≈ˢ g → g ≈ˢ f
  ≈ˢ-sym ξ x = ≈-sym (ξ x)

  ≈ˢ-trans : ∀ {Γ} {Δ} {f g h : Γ →ˢ Δ} → f ≈ˢ g → g ≈ˢ h → f ≈ˢ h
  ≈ˢ-trans ζ ξ x = ≈-trans (ζ x) (ξ x)
  -- identity substitution

  𝟙ˢ : ∀ {Γ} → Γ →ˢ Γ
  𝟙ˢ {𝟘} ()
  𝟙ˢ {[ Γ , A ]} var-here = var-left var-here ` λ y →  [ 2-to-3-right ]ʳ 𝟙ˢ y
  𝟙ˢ {Γ Syntax.⊕ Δ} (var-left x) =  [ 2-to-3 ]ʳ 𝟙ˢ x
  𝟙ˢ {Γ Syntax.⊕ Δ} (var-right y) = [ 2-to-3-right ]ʳ 𝟙ˢ y

  -- substitution extension

  ⇑ˢ : ∀ {Γ Δ Θ} → Γ →ˢ Δ → Γ ⊕ Θ →ˢ Δ ⊕ Θ
  ⇑ˢ f (var-left x) =  [ 2-to-3 ]ʳ f x
  ⇑ˢ f (var-right y) =  [ 2-to-3-right ]ʳ 𝟙ˢ y
