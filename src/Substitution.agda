open import Agda.Primitive
open import Relation.Unary hiding (_∈_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

import Syntax
import Renaming


module Substitution (Class : Set) where

  open Syntax Class
  open Renaming Class

  -- lifting a renaming to a substitution

  lift : ∀ {γ δ} → (γ →ʳ δ) → (γ →ˢ δ)
  lift 𝟘 = 𝟘
  lift [ x ] = [ var-left x ` lift (map var-right 𝟙ʳ) ]
  lift (ρ₁ ⊕ ρ₂) = lift ρ₁ ⊕ lift ρ₂

  -- identity substitution

  𝟙ˢ : ∀ {γ} → γ →ˢ γ
  𝟙ˢ = lift 𝟙ʳ

  -- substitution extension

  ⇑ˢ : ∀ {γ δ θ} → γ →ˢ δ → γ ⊕ θ →ˢ δ ⊕ θ
  ⇑ˢ {θ = θ} f =  map (λ t →  [ ⇑ʳ (tabulate var-left) ]ʳ t) f  ⊕ lift (tabulate var-right)

  -- action of substitution
  infix 6 [_]ˢ_
  infix 6 _∘ˢ_

  [_]ˢ_ : ∀ {γ δ cl} (f : γ →ˢ δ) → ∀ {θ} → Expr (γ ⊕ θ) cl → Expr (δ ⊕ θ) cl
  _∘ˢ_ : ∀ {γ δ θ} (g : δ →ˢ θ) (f : γ →ˢ δ) → γ →ˢ θ

  [ f ]ˢ var-left x ` ts = {!!}
  [ f ]ˢ var-right x ` ts = var-right x ` tabulate (λ y → {! [ f ]ˢ (ts ∙ y)!})

  g ∘ˢ f = tabulate (λ x → {!!})
