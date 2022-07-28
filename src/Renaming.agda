open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Product hiding (map)
open import Function using (_∘_)

import Categories.Category
import Syntax


module Renaming (Sort : Set) where

  open Syntax Sort

  -- identity renaming

  𝟙ʳ : ∀ {γ} → γ →ʳ γ
  𝟙ʳ = tabulate (λ x → x)

  -- 𝟙ʳ is the identity
  𝟙ʳ-≡ : ∀ {γ} {α} {x : α ∈ γ} → (𝟙ʳ ∙ x) ≡ x
  𝟙ʳ-≡ = tabulate-∙ (λ x → x)

  -- composition of renamings

  infixl 7 _∘ʳ_

  _∘ʳ_ : ∀ {γ} {δ} {θ} → (δ →ʳ θ) → (γ →ʳ δ) → (γ →ʳ θ)
  (ρ ∘ʳ τ) = tabulate (λ x → ρ ∙ (τ ∙ x))

  ∘ʳ-∙ : ∀ {γ δ θ} {ρ : δ →ʳ θ} {τ : γ →ʳ δ} {α} {x : α ∈ γ} → (ρ ∘ʳ τ) ∙ x ≡ ρ ∙ (τ ∙ x)
  ∘ʳ-∙ {ρ = ρ} {τ = τ} = tabulate-∙ (λ x → ρ ∙ (τ ∙ x))


  -- renaming extension

  ⇑ʳ : ∀ {γ} {δ} {θ} → (γ →ʳ δ) → (γ ⊕ θ →ʳ δ ⊕ θ)
  ⇑ʳ ρ = map var-left ρ ⊕ tabulate var-right

  -- extension respects identity

  ⇑ʳ-resp-𝟙ʳ : ∀ {γ} {δ} → ⇑ʳ {θ = δ} (𝟙ʳ {γ = γ}) ≡ 𝟙ʳ
  ⇑ʳ-resp-𝟙ʳ = cong₂ _⊕_ map-tabulate refl

  -- extension commutes with composition

  ⇑ʳ-resp-∘ʳ : ∀ {γ δ η θ} {ρ : γ →ʳ δ} {τ : δ →ʳ η} → ⇑ʳ {θ = θ} (τ ∘ʳ ρ) ≡ ⇑ʳ τ ∘ʳ ⇑ʳ ρ
  ⇑ʳ-resp-∘ʳ {γ = γ} {θ = θ} {ρ = ρ} {τ = τ} =
    cong₂ _⊕_
     (trans map-tabulate (tabulate-ext ξ₁))
     (tabulate-ext ξ₂)
    where
      open ≡-Reasoning

      ξ₁ : ∀ {α : Arity} {x : α ∈ γ} → var-left (τ ∙ (ρ ∙ x)) ≡ ⇑ʳ τ ∙ (map var-left ρ ∙ x)
      ξ₁ {x = x} =
        begin
          var-left (τ ∙ (ρ ∙ x))
             ≡⟨ sym (map-∙ {ps = τ}) ⟩
          ⇑ʳ τ ∙ var-left (ρ ∙ x)
             ≡⟨ cong-∙ {f = ⇑ʳ τ} {y = map var-left ρ ∙ x} refl (sym (map-∙ {ps = ρ})) ⟩
          ⇑ʳ τ ∙ (map var-left ρ ∙ x)
          ∎

      ξ₂ : ∀ {α : Arity} {x : α ∈ θ} → var-right x ≡ ⇑ʳ τ ∙ (tabulate var-right ∙ x)
      ξ₂ {x = x} =
        begin
          var-right x
            ≡⟨ sym (tabulate-∙ var-right) ⟩
          ⇑ʳ τ ∙ var-right x
            ≡⟨  sym (cong (⇑ʳ τ ∙_) (tabulate-∙ var-right)) ⟩
          ⇑ʳ τ ∙ (tabulate var-right ∙ x)
          ∎

  -- the action of a renaming on an expression

  infixr 6 [_]ʳ_
  infixl 7 _ʳ∘ˢ_

  [_]ʳ_ : ∀ {γ δ cl} → γ →ʳ δ → Expr γ cl → Expr δ cl
  _ʳ∘ˢ_ : ∀ {γ δ η} → δ →ʳ η → γ →ˢ δ → γ →ˢ η

  [ ρ ]ʳ (x ` ts) = ρ ∙ x ` (ρ ʳ∘ˢ ts)

  ρ ʳ∘ˢ 𝟘 = 𝟘
  ρ ʳ∘ˢ [ t ] = [ [ map var-left ρ ⊕ tabulate var-right ]ʳ t ]
  ρ ʳ∘ˢ (ts₁ ⊕ ts₂) = (ρ ʳ∘ˢ ts₁) ⊕ (ρ ʳ∘ˢ ts₂)

  𝟙ʳ-ʳ∘ˢ : ∀ {γ δ} → {ts : γ →ˢ δ} → 𝟙ʳ ʳ∘ˢ ts ≡ ts
  [𝟙ʳ] : ∀ {γ cl} {t : Expr γ cl} → [ 𝟙ʳ ]ʳ t ≡ t

  𝟙ʳ-ʳ∘ˢ {ts = 𝟘} = refl
  𝟙ʳ-ʳ∘ˢ {ts = [ x ]} = cong [_] (trans (cong₂ [_]ʳ_ (cong₂ _⊕_ map-tabulate refl) refl) [𝟙ʳ])
  𝟙ʳ-ʳ∘ˢ {ts = ts ⊕ ts₁} = cong₂ _⊕_ 𝟙ʳ-ʳ∘ˢ 𝟙ʳ-ʳ∘ˢ

  [𝟙ʳ] {t = x ` ts} = ≡-` 𝟙ʳ-≡ λ z → cong-∙ {f = 𝟙ʳ ʳ∘ˢ ts} 𝟙ʳ-ʳ∘ˢ refl

  -- -- the action is functorial

  ∘ʳ-ʳ∘ˢ : ∀ {γ δ θ η} {ρ : γ →ʳ δ} {τ : δ →ʳ θ} {σ : η →ˢ γ}  → τ ∘ʳ ρ ʳ∘ˢ σ ≡ τ ʳ∘ˢ (ρ ʳ∘ˢ σ)
  [∘ʳ] : ∀ {γ δ θ cl} {ρ : γ →ʳ δ} {τ : δ →ʳ θ} (t : Expr γ cl) → [ τ ∘ʳ ρ ]ʳ t ≡ [ τ ]ʳ [ ρ ]ʳ t

  ∘ʳ-ʳ∘ˢ {σ = 𝟘} = refl
  ∘ʳ-ʳ∘ˢ {ρ = ρ} {τ = τ} {σ = [ t ]} = cong [_] (trans (cong (λ η → [ η ]ʳ t) (⇑ʳ-resp-∘ʳ {ρ = ρ} {τ = τ})) ([∘ʳ] t))
  ∘ʳ-ʳ∘ˢ {σ = σ₁ ⊕ σ₂} = cong₂ _⊕_ ∘ʳ-ʳ∘ˢ ∘ʳ-ʳ∘ˢ

  [∘ʳ] {ρ = ρ} {τ = τ} (x ` ts) = ≡-` (tabulate-∙ (λ z → τ ∙ (ρ ∙ z))) λ z → cong (_∙ z) (∘ʳ-ʳ∘ˢ {σ = ts})

  -- -- the categorical structure of shapes and renamings

  ∘ʳ-assoc : {γ δ θ η : Shape} {f : γ →ʳ δ} {g : δ →ʳ θ} {h : θ →ʳ η} → h ∘ʳ g ∘ʳ f ≡ h ∘ʳ (g ∘ʳ f)
  ∘ʳ-assoc {f = f} {g = g} {h = h} =
    tabulate-ext (trans (tabulate-∙ (λ x → h ∙ (g ∙ x))) (cong (h ∙_) (sym (tabulate-∙ (λ x → g ∙ (f ∙ x))))))

  module _ where
    open Categories.Category

    Renamings : Category lzero lzero lzero
    Renamings =
     record
       { Obj = Shape
       ; _⇒_ = _→ʳ_
       ; _≈_ = _≡_
       ; id = 𝟙ʳ
       ; _∘_ = _∘ʳ_
       ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → ∘ʳ-assoc {f = f} {g = g} {h = h}
       ; sym-assoc = λ {_} {_} {_} {_} {f} {g} {h} → sym (∘ʳ-assoc {f = f} {g = g} {h = h})
       ; identityˡ = λ {γ} {_} {ρ} → shape-≡ (λ x → trans (∘ʳ-∙ {ρ = 𝟙ʳ} {τ = ρ}) 𝟙ʳ-≡)
       ; identityʳ = λ {_} {_} {ρ} → shape-≡ (λ x → trans ((∘ʳ-∙ {ρ = ρ} {τ = 𝟙ʳ})) (cong (ρ ∙_) 𝟙ʳ-≡))
       ; identity² = tabulate-ext (trans 𝟙ʳ-≡ 𝟙ʳ-≡)
       ; equiv = record { refl = refl ; sym = sym ; trans = trans }
       ; ∘-resp-≈ = λ ζ ξ → cong₂ _∘ʳ_ ζ ξ
       }

  -- assoc-right : ∀ {γ δ η} → (γ ⊕ δ) ⊕ η →ʳ γ ⊕ (δ ⊕ η)
  -- assoc-right (var-left (var-left x)) = var-left x
  -- assoc-right (var-left (var-right y)) = var-right (var-left y)
  -- assoc-right (var-right z) = var-right (var-right z)

  -- assoc-left : ∀ {γ δ η} → γ ⊕ (δ ⊕ η) →ʳ (γ ⊕ δ) ⊕ η
  -- assoc-left (var-left x) = var-left (var-left x)
  -- assoc-left (var-right (var-left y)) = var-left (var-right y)
  -- assoc-left (var-right (var-right z)) = var-right z
