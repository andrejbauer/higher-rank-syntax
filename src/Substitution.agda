open import Agda.Primitive
open import Relation.Unary hiding (_∈_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_,_; _×_)
open import Function using (_∘_)
open import Data.List hiding ([_]; tabulate; map)

open ≡-Reasoning

import Syntax
import Renaming


module Substitution (Class : Set) where

  open Syntax Class
  open Renaming Class

  -- Lifting of renamings to substitutions, and of variables to expressions

  lift : ∀ {γ δ} → (γ →ʳ δ) → (γ →ˢ δ)

  η : ∀ {γ a} (x : a ∈ γ) → Arg γ a

  lift 𝟘 = 𝟘
  lift [ x ] = [ η x ]
  lift (ρ₁ ⊕ ρ₂) = lift ρ₁ ⊕ lift ρ₂

  η x = var-left x ` lift (tabulate var-right)

  -- Ideally we would like the following to be the definition of lift,
  -- but Agda termination gets in the way

  lift-map-η : ∀ {γ δ} (ρ : γ →ʳ δ) → lift ρ ≡ map η ρ
  lift-map-η 𝟘 = refl
  lift-map-η [ x ] = refl
  lift-map-η (ρ₁ ⊕ ρ₂) = cong₂ _⊕_ (lift-map-η ρ₁) (lift-map-η ρ₂)

  lift-𝟙ʳ : ∀ {γ} → lift 𝟙ʳ ≡ tabulate (η {γ = γ})
  lift-𝟙ʳ = trans (lift-map-η 𝟙ʳ) map-tabulate

  -- Identity substitution

  𝟙ˢ : ∀ {γ} → γ →ˢ γ
  𝟙ˢ = lift 𝟙ʳ

  -- Substitution extension

  ⇑ˢ : ∀ {γ δ θ} → γ →ˢ δ → γ ⊕ θ →ˢ δ ⊕ θ
  ⇑ˢ {θ = θ} f =  map [ ⇑ʳ (tabulate var-left) ]ʳ_ f ⊕ lift (tabulate var-right)

  -- The interaction of lifting with various operations

  lift-∙ : ∀ {γ δ} (ρ : γ →ʳ δ) {a} (x : a ∈ γ) →
           lift ρ ∙ x ≡ η (ρ ∙ x)
  lift-∙ [ _ ] var-here = refl
  lift-∙ (ρ₁ ⊕ ρ₂) (var-left x) = lift-∙ ρ₁ x
  lift-∙ (ρ₁ ⊕ ρ₂) (var-right y) = lift-∙ ρ₂ y

  𝟙ˢ-∙ : ∀ {γ a} {x : a ∈ γ} → 𝟙ˢ ∙ x ≡ η x
  𝟙ˢ-∙ {x = x} = trans (lift-∙ 𝟙ʳ x) (cong η 𝟙ʳ-≡)

  lift-tabulate : ∀ {γ δ} (f : ∀ {α} → α ∈ γ → α ∈ δ) {a} (x : a ∈ γ) →
                  lift (tabulate f) ∙ x ≡ η (f x)
  lift-tabulate f var-here = refl
  lift-tabulate f (var-left x) = lift-tabulate (λ z → f (var-left z)) x
  lift-tabulate f (var-right y) = lift-tabulate (λ z → f (var-right z)) y

  ∘ʳ-lift : ∀ {γ δ θ} (ρ : γ →ʳ δ) (τ : δ →ʳ θ) {a} (x : a ∈ γ) →
             lift (τ ∘ʳ ρ) ∙ x ≡  lift τ ∙ (ρ ∙ x)
  ∘ʳ-lift [ x ] τ var-here = sym (lift-∙ τ x)
  ∘ʳ-lift (ρ₁ ⊕ ρ₂) τ (var-left x) = ∘ʳ-lift ρ₁ τ x
  ∘ʳ-lift (ρ₁ ⊕ ρ₂) τ (var-right y) = ∘ʳ-lift ρ₂ τ y

  []ʳ-lift : ∀ {γ δ θ} (ρ : γ →ʳ δ) (τ : δ →ʳ θ) {a} (x : a ∈ γ) → [ ⇑ʳ τ ]ʳ (lift ρ ∙ x) ≡  lift (τ ∘ʳ ρ) ∙ x
  []ʳ-η : ∀ {γ δ} (ρ : γ →ʳ δ) {a} (x : a ∈ γ) → [ ⇑ʳ ρ ]ʳ η x ≡ η (ρ ∙ x)

  []ʳ-lift [ x ] τ var-here = []ʳ-η τ x
  []ʳ-lift (ρ₁ ⊕ ρ₂) τ (var-left x) = []ʳ-lift ρ₁ τ x
  []ʳ-lift (ρ₁ ⊕ ρ₂) τ (var-right x) = []ʳ-lift ρ₂ τ x

  ⇑ʳ-∘ʳ-tabulate-var-right : ∀ {γ δ θ} (ρ : γ →ʳ δ) →
                             (⇑ʳ {θ = θ} ρ ∘ʳ tabulate var-right) ≡ tabulate var-right
  ⇑ʳ-∘ʳ-tabulate-var-right {θ = θ} ρ = shape-≡ ξ
    where ξ : ∀ {a} (x : a ∈ θ) → (⇑ʳ ρ ∘ʳ tabulate var-right) ∙ x ≡ tabulate var-right ∙ x
          ξ x = trans
                  (trans
                      (∘ʳ-∙  {ρ = ⇑ʳ ρ} {τ = tabulate var-right} {x = x})
                      (trans (cong (⇑ʳ ρ ∙_) (tabulate-∙ var-right)) (tabulate-∙ var-right)))
                  (sym (tabulate-∙ var-right))

  [⇑ʳ]-lift-var-right : ∀ {γ δ θ} (ρ : γ →ʳ δ) {a} (x : a ∈ θ) →
                        [ ⇑ʳ (⇑ʳ ρ) ]ʳ lift (tabulate var-right) ∙ x  ≡ lift (tabulate var-right) ∙ x
  [⇑ʳ]-lift-var-right ρ x = trans ([]ʳ-lift (tabulate var-right) (⇑ʳ ρ) x) (cong (λ τ → lift τ ∙ x) (⇑ʳ-∘ʳ-tabulate-var-right ρ))

  ʳ∘ˢ-lift-var-right : ∀ {γ δ θ} (ρ : γ →ʳ δ) {a} (x : a ∈ θ) →
                       ((⇑ʳ {θ = θ} ρ) ʳ∘ˢ lift (tabulate var-right)) ∙ x ≡ lift (tabulate var-right) ∙ x
  ʳ∘ˢ-lift-var-right ρ x =
    trans
      (ʳ∘ˢ-∙ {ρ = ⇑ʳ ρ} {ts = lift (tabulate var-right)})
      ([⇑ʳ]-lift-var-right ρ x)

  []ʳ-η ρ x = ≡-` (map-∙ {f = var-left} {ps = ρ}) (λ z → ʳ∘ˢ-lift-var-right ρ z)


  ʳ∘ˢ-lift : ∀ {γ δ θ} (ρ : γ →ʳ δ) (τ : δ →ʳ θ) {a} (x : a ∈ γ) →
             (τ ʳ∘ˢ lift ρ) ∙ x ≡ lift (τ ∘ʳ ρ) ∙ x
  ʳ∘ˢ-lift [ x ] τ var-here = ≡-` ( map-∙ {f = var-left} {ps = τ}) λ z → ʳ∘ˢ-lift-var-right τ z
  ʳ∘ˢ-lift (ρ₁ ⊕ ρ₂) τ (var-left x) = ʳ∘ˢ-lift ρ₁ τ x
  ʳ∘ˢ-lift (ρ₁ ⊕ ρ₂) τ (var-right x) = ʳ∘ˢ-lift ρ₂ τ x

  lift-map : ∀ {γ δ θ} (f : ∀ {α} → α ∈ γ → α ∈ δ) (ρ : θ →ʳ γ) →
             lift (map f ρ) ≡ map [ ⇑ʳ (tabulate f) ]ʳ_ (lift ρ)
  lift-map f 𝟘 = refl
  lift-map f [ x ] = cong [_] (trans (cong η (sym (tabulate-∙ f))) (sym ([]ʳ-η (tabulate f) x)))
  lift-map f (ρ₁ ⊕ ρ₂) = cong₂ _⊕_ (lift-map f ρ₁) (lift-map f ρ₂)

  ⇑ˢ-lift : ∀ {γ δ θ} (ρ : γ →ʳ δ) → ⇑ˢ {θ = θ} (lift ρ) ≡ lift (⇑ʳ ρ)
  ⇑ˢ-lift ρ = cong₂ _⊕_ (sym (lift-map var-left ρ)) refl

  infix 6 [_]ˢ_
  infix 6 _∘ˢ_

  -- We tell Agda to take termination of substutition on faith.
  {-# TERMINATING #-}
  [_]ˢ_ : ∀ {γ δ cl} (f : γ →ˢ δ) → Expr γ cl → Expr δ cl

  -- Composition of substiutions
  _∘ˢ_ : ∀ {γ δ θ} (g : δ →ˢ θ) (f : γ →ˢ δ) → γ →ˢ θ

  -- Mutual definition of the substitution action and composition
  [ f ]ˢ x ` ts = [ 𝟙ˢ ⊕ (f ∘ˢ ts) ]ˢ (f ∙ x)
  g ∘ˢ f = tabulate (λ x → [ ⇑ˢ g ]ˢ f ∙ x)

  -- Basic properties of substitution
  [lift]ˢ : ∀ {γ δ cl} (ρ : γ →ʳ δ) (e : Expr γ cl) → [ lift ρ ]ˢ e ≡ [ ρ ]ʳ e
  [lift]ˢ ρ (x ` ts) =
     trans
       (cong [ 𝟙ˢ ⊕ lift ρ ∘ˢ ts ]ˢ_ (lift-∙ ρ x))
       {!!}

  [𝟙]ˢ : ∀ {γ cl} {e : Expr γ cl} → [ 𝟙ˢ ]ˢ e ≡ e
  [𝟙]ˢ {e = x ` ts} = trans (cong [ 𝟙ˢ ⊕ (𝟙ˢ ∘ˢ ts) ]ˢ_ 𝟙ˢ-∙) {!!}
