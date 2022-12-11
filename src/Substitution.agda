open import Agda.Primitive
open import Relation.Unary hiding (_∈_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_,_)

open ≡-Reasoning

import Syntax
import Renaming


module Substitution (Class : Set) where

  open Syntax Class
  open Renaming Class

  -- Lifting a renaming to a substitution

  lift : ∀ {γ δ} → (γ →ʳ δ) → (γ →ˢ δ)
  lift 𝟘 = 𝟘
  lift [ x ] = [ var-left x ` lift (map var-right 𝟙ʳ) ]
  lift (ρ₁ ⊕ ρ₂) = lift ρ₁ ⊕ lift ρ₂

  -- Identity substitution

  𝟙ˢ : ∀ {γ} → γ →ˢ γ
  𝟙ˢ = lift 𝟙ʳ

  -- Substitution extension

  ⇑ˢ : ∀ {γ δ θ} → γ →ˢ δ → γ ⊕ θ →ˢ δ ⊕ θ
  ⇑ˢ {θ = θ} f =  map (λ t →  [ ⇑ʳ (tabulate var-left) ]ʳ t) f  ⊕ lift (tabulate var-right)

  -- Action of substitution
  infix 6 [_]ˢ_
  infix 6 _∘ˢ_

  -- -- The naive definition, which Agda does not see as terminating
  -- [_]ˢ_ : ∀ {γ δ cl} (f : γ →ˢ δ) → Expr γ cl → Expr δ cl
  -- _∘ˢ_ : ∀ {γ δ θ} (g : δ →ˢ θ) (f : γ →ˢ δ) → γ →ˢ θ
  -- [ f ]ˢ x ` ts = [ 𝟙ˢ ⊕ (f ∘ˢ ts) ]ˢ (f ∙ x)
  -- g ∘ˢ f = tabulate (λ x → [ ⇑ˢ g ]ˢ f ∙ x)

  -- Instead we use the Bove-Cappreta method, whereby we define the support of [_]ˢ_ and _∘ˢ_, then we define the maps
  -- as partial maps defined on the support, and finally show that the supports are the entire domains.
  -- See doi:10.1017/S0960129505004822

  data defined-[]ˢ : ∀ {γ δ cl} (f : γ →ˢ δ) → Expr γ cl → Set

  data defined-∘ˢ : ∀ {γ δ θ} (g : δ →ˢ θ) (f : γ →ˢ δ) → Set

  actˢ : ∀ {γ δ cl} (f : γ →ˢ δ) (e : Expr γ cl) → defined-[]ˢ f e → Expr δ cl
  compˢ : ∀ {γ δ θ} (g : δ →ˢ θ) (f : γ →ˢ δ) → defined-∘ˢ g f → (γ →ˢ θ)

  data defined-[]ˢ where
    def-[]ˢ : ∀ {γ γ' δ cl} {f : γ →ˢ δ} {x : (γ' , cl) ∈ γ} {ts : γ' →ˢ γ} (D : defined-∘ˢ f ts) →
                defined-[]ˢ (𝟙ˢ ⊕ (compˢ f ts D)) (f ∙ x) →
                defined-[]ˢ f (x ` ts)

  data defined-∘ˢ where
    def-∘ˢ :  ∀ {γ δ θ} {g : δ →ˢ θ} {f : γ →ˢ δ} →
              (∀ {γ' cl} (x : (γ' , cl) ∈ γ) → defined-[]ˢ (⇑ˢ g) (f ∙ x)) → defined-∘ˢ g f

  actˢ f (x ` ts) (def-[]ˢ D E) = actˢ (𝟙ˢ ⊕ (compˢ f ts D)) (f ∙ x) E

  compˢ g f (def-∘ˢ D) = tabulate (λ x → actˢ (⇑ˢ g) (f ∙ x) (D x))

  total-actˢ : ∀ {γ δ cl} (f : γ →ˢ δ) (e : Expr γ cl) → defined-[]ˢ f e
  total-compˢ : ∀ {γ δ θ} (g : δ →ˢ θ) (f : γ →ˢ δ) → defined-∘ˢ g f

  total-actˢ f (x ` ts) = def-[]ˢ (total-compˢ f ts) {!!}

  total-compˢ {γ = γ} f g = def-∘ˢ λ {γ' cl} (x : (γ' , cl) ∈ γ) → {!!}


  -- Finally, the definitions we wanted to get

  [_]ˢ_ : ∀ {γ δ cl} (f : γ →ˢ δ) → Expr γ cl → Expr δ cl
  [ f ]ˢ e = actˢ f e (total-actˢ f e)

  _∘ˢ_ : ∀ {γ δ θ} (g : δ →ˢ θ) (f : γ →ˢ δ) → γ →ˢ θ
  g ∘ˢ f = compˢ g f (total-compˢ g f)
