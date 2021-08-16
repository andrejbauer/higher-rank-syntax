{-# OPTIONS --sized-types #-}

open import Size
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

import Syntax
import Renaming

module Substitution (Class : Set) where

  open Syntax Class
  open Renaming Class

  -- the set of substitutions

  infix 5 _→ˢ_

  _→ˢ_ : ∀ {j} {i : Size< ↑ j} → Shape i → Shape j → Set
  _→ˢ_ {i = i} Γ Δ = ∀ {m : Size< i} {Θ : Shape m} {A} (x : [ Θ , A ]∈ Γ) → Expr (Δ ⊕ Θ) A

  -- equality of substitutions

  infix 4 _≈ˢ_

  _≈ˢ_ : ∀ {j} {i : Size< ↑ j} {Γ : Shape i} {Δ : Shape j} (f g : Γ →ˢ Δ) → Set
  _≈ˢ_ {i = i} {Γ = Γ} f g = ∀ {k : Size< i} {Θ : Shape k} {A} (x : [ Θ , A ]∈ Γ) → f x ≈ g x

  -- equality of substitutions is an equivalence relation

  ≈ˢ-refl : ∀ {j} {i : Size< ↑ j} {Γ : Shape i} {Δ : Shape j} {f : Γ →ˢ Δ} → f ≈ˢ f
  ≈ˢ-refl x = ≈-refl

  ≈ˢ-sym : ∀ {j} {i : Size< ↑ j} {Γ : Shape i} {Δ : Shape j} {f g : Γ →ˢ Δ} → f ≈ˢ g → g ≈ˢ f
  ≈ˢ-sym ξ x = ≈-sym (ξ x)

  ≈ˢ-trans : ∀ {j} {i : Size< ↑ j} {Γ : Shape i} {Δ : Shape j} {f g h : Γ →ˢ Δ} → f ≈ˢ g → g ≈ˢ h → f ≈ˢ h
  ≈ˢ-trans ζ ξ x = ≈-trans (ζ x) (ξ x)

  -- identity substitution

  2-3 : ∀ {Γ Δ Θ} → Γ ⊕ Θ →ʳ (Γ ⊕ Δ) ⊕ Θ
  2-3 (var-left x) = var-left (var-left x)
  2-3 (var-right y) = var-right y

  shift : ∀ {i j k} {Γ : Shape i} {Δ : Shape j} {Θ : Shape k} → Δ ⊕ Θ →ʳ (Γ ⊕ Δ) ⊕ Θ
  shift (var-left x) = var-left (var-right x)
  shift (var-right y) = var-right y

  𝟙ˢ : ∀ i {Γ : Shape i} {m : Size< i} {Θ : Shape m} {A} → [ Θ , A ]∈ Γ → Expr (Γ ⊕ Θ) A
  𝟙ˢ i {Γ} {m} {Θ} {A} x = var-left x ` (λ { y → [ shift ]ʳ 𝟙ˢ m y })
     where generic-args : {k : Size< m} {Δ : Shape k} {B : Class} → [ Δ , B ]∈ Θ → Expr (Γ ⊕ Θ ⊕ Θ) B
           generic-args {k} {Δ} {B} y =  [ {!!} ]ʳ 𝟙ˢ m y

  -- -- substitution extension

  -- ⇑ˢ : ∀ {Γ Δ Θ} → Γ →ˢ Δ → Γ ⊕ Θ →ˢ Δ ⊕ Θ
  -- ⇑ˢ f (var-left x) =  [ 2-3 ]ʳ f x
  -- ⇑ˢ f (var-right y) =  [ shift ]ʳ  𝟙ˢ y
