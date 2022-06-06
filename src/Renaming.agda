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


  -- join of renamings

  infix 6 [_,_]ʳ

  [_,_]ʳ : ∀ {γ δ θ} → (γ →ʳ θ) → (δ →ʳ θ) → (γ ⊕ δ →ʳ θ)
  [ ρ , τ ]ʳ = ρ ⊕ τ

  -- renaming extension

  ⇑ʳ : ∀ {γ} {δ} {θ} → (γ →ʳ δ) → (γ ⊕ θ →ʳ δ ⊕ θ)
  ⇑ʳ ρ = map var-left ρ ⊕ map var-right 𝟙ʳ

  -- extension respects identity

  ⇑ʳ-resp-𝟙ʳ : ∀ {γ} {δ} → ⇑ʳ {θ = δ} (𝟙ʳ {γ = γ}) ≡ 𝟙ʳ
  ⇑ʳ-resp-𝟙ʳ = cong₂ _⊕_ map-tabulate map-tabulate

  -- extension commutes with composition

  ⇑ʳ-resp-∘ʳ : ∀ {γ δ η θ} {ρ : γ →ʳ δ} {τ : δ →ʳ η} → ⇑ʳ {θ = θ} (τ ∘ʳ ρ) ≡ ⇑ʳ τ ∘ʳ ⇑ʳ ρ
  ⇑ʳ-resp-∘ʳ {γ = γ} {θ = θ} {ρ = ρ} {τ = τ} =
    cong₂ _⊕_
     (trans map-tabulate (tabulate-ext ξ₁))
     (trans map-tabulate (tabulate-ext ξ₂))
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

      ξ₂ : ∀ {α : Arity} {x : α ∈ θ} → var-right x ≡ ⇑ʳ τ ∙ (map var-right 𝟙ʳ ∙ x)
      ξ₂ {x = x} =
        begin
          var-right x
            ≡⟨ cong var-right (sym 𝟙ʳ-≡) ⟩
          var-right (𝟙ʳ ∙ x)
            ≡⟨ cong var-right (sym 𝟙ʳ-≡) ⟩
          var-right (𝟙ʳ ∙ (𝟙ʳ ∙ x))
            ≡⟨  sym (map-∙ {f = var-right} {ps = 𝟙ʳ})  ⟩
          ⇑ʳ τ ∙ var-right (𝟙ʳ ∙ x)
            ≡⟨ cong-∙ {f = ⇑ʳ τ} {y = map var-right 𝟙ʳ ∙ x} refl (sym (map-∙ {f = var-right} {ps = 𝟙ʳ})) ⟩
          ⇑ʳ τ ∙ (map var-right 𝟙ʳ ∙ x)
          ∎

  -- ⇑ʳ-resp-∘ʳ {γ = γ} {θ = θ} {ρ = ρ} {τ = τ} = cong₂ _⊕_ (tabulate-ext ξ₁) (tabulate-ext ξ₂)
  --   where
  --     open ≡-Reasoning

  --     ξ₂ :  {α : Arity} {x : α ∈ θ} → var-right x ≡ ⇑ʳ τ ∙ (tabulate var-right ∙ x)
  --     ξ₂ {x = x} =
  --       begin
  --         var-right x
  --           ≡⟨ sym (tabulate-∙ var-right) ⟩
  --         ⇑ʳ τ ∙ (var-right x)
  --           ≡⟨ sym (cong (⇑ʳ τ ∙_) (tabulate-∙ var-right)) ⟩
  --         ⇑ʳ τ ∙ (tabulate var-right ∙ x)
  --       ∎

  --     ξ₁ : {α : Arity} {x : α ∈ γ} → var-left ((τ ∘ʳ ρ) ∙ x) ≡ ⇑ʳ τ ∙ (tabulate (λ y → var-left (ρ ∙ y)) ∙ x)
  --     ξ₁ {x = x} =
  --       begin
  --         var-left ((τ ∘ʳ ρ) ∙ x)
  --           ≡⟨ cong var-left (tabulate-∙ (λ y → τ ∙ (ρ ∙ y))) ⟩
  --         var-left (τ ∙ (ρ ∙ x))
  --           ≡⟨ sym (tabulate-∙ (λ y → var-left (τ ∙ y))) ⟩
  --         ⇑ʳ τ ∙ var-left (ρ ∙ x)
  --           ≡⟨ sym (cong (⇑ʳ τ ∙_) (tabulate-∙ (λ y → var-left (ρ ∙ y)))) ⟩
  --         ⇑ʳ τ ∙ (tabulate (λ y → var-left (ρ ∙ y)) ∙ x)
  --       ∎

  -- the action of a renaming on an expression

  infixr 6 [_]ʳ_
  infixl 7 _ʳ∘ˢ_

  [_]ʳ_ : ∀ {γ δ cl} → γ →ʳ δ → Expr γ cl → Expr δ cl
  _ʳ∘ˢ_ : ∀ {γ δ η} → δ →ʳ η → γ →ˢ δ → γ →ˢ η

  [ ρ ]ʳ (x ` ts) = ρ ∙ x ` (ρ ʳ∘ˢ ts)

  ρ ʳ∘ˢ 𝟘 = 𝟘
  ρ ʳ∘ˢ [ t ] = [ [ map var-left ρ ⊕ map var-right 𝟙ʳ ]ʳ t ]
  ρ ʳ∘ˢ (ts₁ ⊕ ts₂) = (ρ ʳ∘ˢ ts₁) ⊕ (ρ ʳ∘ˢ ts₂)

  𝟙ʳ-ʳ∘ˢ : ∀ {γ δ} → {ts : γ →ˢ δ} → 𝟙ʳ ʳ∘ˢ ts ≡ ts
  𝟙ʳ-ʳ∘ˢ = {!!}

  -- -- -- the action respects equality of renamings and equality of terms

  -- []ʳ-resp-≡ : ∀ {γ} {δ} {cl} {ρ : γ →ʳ δ} {t u : Expr (γ , cl)} →
  --              t ≡ u → [ ρ ]ʳ t ≡ [ ρ ]ʳ u
  -- []ʳ-resp-≡ refl = refl

  -- []ʳ-resp-≡ : ∀ {γ} {δ} {cl} {ρ τ : γ →ʳ δ} (t : Expr (γ , cl)) →
  --               ρ ≡ τ → [ ρ ]ʳ t ≡ [ τ ]ʳ t
  -- []ʳ-resp-≡ (x ` ts) ξ = cong₂ _`_ (ξ x) (shape-≡ (λ y → []ʳ-resp-≡ (ts y) (⇑ʳ-resp-≡ ξ)))

  -- []ʳ-resp-≡-≡ : ∀ {γ} {δ} {cl}
  --                   {ρ τ : γ →ʳ δ} {t u : Expr (γ , cl)} → ρ ≡ τ → t ≡ u → [ ρ ]ʳ t ≡ [ τ ]ʳ u
  -- []ʳ-resp-≡-≡ ζ ξ = trans ([]ʳ-resp-≡ _ ζ) ([]ʳ-resp-≡ ξ)

  -- -- the action is functorial

  [𝟙ʳ] : ∀ {γ cl} {t : Expr γ cl} → [ 𝟙ʳ ]ʳ t ≡ t
  [𝟙ʳ] {t = x ` ts} = ≡-` 𝟙ʳ-≡ λ z → cong-∙ {f = 𝟙ʳ ʳ∘ˢ ts} 𝟙ʳ-ʳ∘ˢ refl

  [∘ʳ] : ∀ {γ δ θ cl} {ρ : γ →ʳ δ} {τ : δ →ʳ θ} (t : Expr γ  cl) → [ τ ∘ʳ ρ ]ʳ t ≡ [ τ ]ʳ [ ρ ]ʳ t
  [∘ʳ] (x ` ts) = ≡-` ∘ʳ-∙ {!!}
  -- [∘ʳ] (x ` ts) = ≡-` (λ { y → trans ([]ʳ-resp-≡ (ts y) ⇑ʳ-resp-∘ʳ) ([∘ʳ] (ts y)) })

  -- -- if a renaming equals identity then it acts as identity

  -- []ʳ-𝟙ʳ : ∀ {γ cl} {ρ : γ →ʳ γ} {t : Expr (γ , cl)} → ρ ≡ 𝟙ʳ → [ ρ ]ʳ t ≡ t
  -- []ʳ-𝟙ʳ ξ = trans ([]ʳ-resp-≡ _ ξ) [𝟙ʳ]

  -- -- the categorical structure of shapes and renamings

  -- module _ where
  --   open Categories.Category

  --   Renamings : Category lzero lzero lzero
  --   Renamings =
  --    record
  --      { Obj = Shape
  --      ; _⇒_ = _→ʳ_
  --      ; _≈_ = _≡_
  --      ; id = 𝟙ʳ
  --      ; _∘_ = _∘ʳ_
  --      ; assoc = λ { _ → refl }
  --      ; sym-assoc = λ { _ → refl }
  --      ; identityˡ = λ { _ → refl }
  --      ; identityʳ = λ { _ → refl }
  --      ; identity² = λ { _ → refl }
  --      ; equiv = record { refl = λ { _ → refl } ; sym = ≡-sym ; trans = ≡-trans }
  --      ; ∘-resp-≈ = λ {_} {_} {_} {ρ} {_} {_} {τ} ζ ξ → λ { x → trans (cong ρ (ξ x)) (ζ (τ x)) }
  --      }

  -- assoc-right : ∀ {γ δ η} → (γ ⊕ δ) ⊕ η →ʳ γ ⊕ (δ ⊕ η)
  -- assoc-right (var-left (var-left x)) = var-left x
  -- assoc-right (var-left (var-right y)) = var-right (var-left y)
  -- assoc-right (var-right z) = var-right (var-right z)

  -- assoc-left : ∀ {γ δ η} → γ ⊕ (δ ⊕ η) →ʳ (γ ⊕ δ) ⊕ η
  -- assoc-left (var-left x) = var-left (var-left x)
  -- assoc-left (var-right (var-left y)) = var-left (var-right y)
  -- assoc-left (var-right (var-right z)) = var-right z
