open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Product

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

  _∘ʳ_ : ∀ {γ} {δ} {Θ} → (δ →ʳ Θ) → (γ →ʳ δ) → (γ →ʳ Θ)
  (ρ ∘ʳ τ) = tabulate (λ x → ρ ∙ (τ ∙ x))

  -- join of renamings

  infix 6 [_,_]ʳ

  [_,_]ʳ : ∀ {γ δ Θ} → (γ →ʳ Θ) → (δ →ʳ Θ) → (γ ⊕ δ →ʳ Θ)
  [ ρ , τ ]ʳ = ρ ⊕ τ

  -- renaming extension

  ⇑ʳ : ∀ {γ} {δ} {Θ} → (γ →ʳ δ) → (γ ⊕ Θ →ʳ δ ⊕ Θ)
  ⇑ʳ ρ = tabulate (λ { (var-left x) → var-left (ρ ∙ x) ; (var-right y) → var-right y })

  -- extension respects identity

  ⇑ʳ-resp-𝟙ʳ : ∀ {γ} {δ} → ⇑ʳ {Θ = δ} (𝟙ʳ {γ = γ}) ≡ 𝟙ʳ
  ⇑ʳ-resp-𝟙ʳ = cong₂ _⊕_ (tabulate-ext (cong var-left 𝟙ʳ-≡)) refl

  -- extension commutes with composition

  ⇑ʳ-resp-∘ʳ : ∀ {B γ δ Θ} {ρ : B →ʳ γ} {τ : γ →ʳ δ} → ⇑ʳ {Θ = Θ} (τ ∘ʳ ρ) ≡ ⇑ʳ τ ∘ʳ ⇑ʳ ρ
  ⇑ʳ-resp-∘ʳ = cong₂ _⊕_ (tabulate-ext {!!}) (tabulate-ext {!!})

  -- -- the action of a renaming on an expression

  -- infixr 6 [_]ʳ_

  -- [_]ʳ_ : ∀ {γ} {cl} {δ} (ρ : γ →ʳ δ) → Expr (γ , cl) → Expr (δ , cl)
  -- [ ρ ]ʳ (x ` ts) = ρ x ` λ { y → [ ⇑ʳ ρ ]ʳ ts y }

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

  -- [𝟙ʳ] : ∀ {α} {t : Expr α} → [ 𝟙ʳ ]ʳ t ≡ t
  -- [𝟙ʳ] {t = x ` ts} = ≡-` λ y → trans ([]ʳ-resp-≡ (ts y) ⇑ʳ-resp-𝟙ʳ) [𝟙ʳ]

  -- [∘ʳ] : ∀ {γ δ Θ cl} {ρ : γ →ʳ δ} {τ : δ →ʳ Θ} (t : Expr (γ , cl)) → [ τ ∘ʳ ρ ]ʳ t ≡ [ τ ]ʳ [ ρ ]ʳ t
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
