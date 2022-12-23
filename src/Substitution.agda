open import Agda.Primitive
open import Relation.Unary hiding (_∈_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_,_)
open import Function using (_∘_)

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

  -- Showing that actˢ and compˢ are total requires several steps.

  is-total-[]ˢ : ∀ {γ δ} (f : γ →ˢ δ) → Set
  is-total-[]ˢ {γ = γ} f = ∀ {cl} (e : Expr γ cl) → defined-[]ˢ f e

  ⊕-total-[]ˢ : ∀ {γ δ θ} {f : γ →ˢ θ} {g : δ →ˢ θ} → is-total-[]ˢ f → is-total-[]ˢ g → is-total-[]ˢ (f ⊕ g)

  ⊕-total-∘ˢ : ∀ {χ γ δ θ} {h : χ →ˢ γ ⊕ δ} {f : γ →ˢ θ} {g : δ →ˢ θ} →
                 is-total-[]ˢ f → is-total-[]ˢ g → is-total-[]ˢ h → defined-∘ˢ (f ⊕ g) h

  ⊕-total-[]ˢ ft gt (var-left x ` ts) = def-[]ˢ (⊕-total-∘ˢ ft gt {!!}) {!!}
  ⊕-total-[]ˢ ft gt (var-right y ` ts) = {!!}

  ⊕-total-∘ˢ ft gt ht = {!!}

  []ˢ-lift-total : ∀ {γ δ cl} (ρ : γ →ʳ δ) (e : Expr γ cl) → defined-[]ˢ (lift ρ) e
  []ˢ-lift-total ρ (x ` ts) =
    def-[]ˢ
      (def-∘ˢ (λ y → subst (λ τ → defined-[]ˢ τ (ts ∙ y)) (sym (⇑ˢ-lift ρ)) {!!}))
      {!!}


  -- The identity substitution is total
  []-𝟙ˢ-total : ∀ {γ cl} (e : Expr γ cl) → defined-[]ˢ 𝟙ˢ e
  []-𝟙ˢ-total (x ` ts) = def-[]ˢ (def-∘ˢ (λ y → {!!})) {!!}


  total-actˢ : ∀ {γ δ cl} (f : γ →ˢ δ) (e : Expr γ cl) → defined-[]ˢ f e
  total-compˢ : ∀ {γ δ θ} (g : δ →ˢ θ) (f : γ →ˢ δ) → defined-∘ˢ g f

  total-actˢ f (x ` ts) = def-[]ˢ (total-compˢ f ts) {!!}

  total-compˢ {γ = γ} f g = def-∘ˢ λ {γ' cl} (x : (γ' , cl) ∈ γ) → {!!}


  -- Finally, the definitions we wanted to get

  [_]ˢ_ : ∀ {γ δ cl} (f : γ →ˢ δ) → Expr γ cl → Expr δ cl
  [ f ]ˢ e = actˢ f e (total-actˢ f e)

  _∘ˢ_ : ∀ {γ δ θ} (g : δ →ˢ θ) (f : γ →ˢ δ) → γ →ˢ θ
  g ∘ˢ f = compˢ g f (total-compˢ g f)
