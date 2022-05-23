open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Product

import Categories.Category
import Syntax


module Renaming (Sort : Set) where

  open Syntax Sort

  -- equality of renamings
  infix 5 _≡ʳ_

  _≡ʳ_ : ∀ {γ} {δ} → (ρ : γ →ʳ δ) → (τ : γ →ʳ δ) → Set
  ρ ≡ʳ τ = ∀ {αˣ} (x :  αˣ ∈ _) → ρ x ≡ τ x

  -- equality is an equivalence relation

  ≡ʳ-refl : ∀ {γ} {δ} → {ρ : γ →ʳ δ} → ρ ≡ʳ ρ
  ≡ʳ-refl x = refl

  ≡ʳ-sym : ∀ {γ} {δ} → {ρ τ : γ →ʳ δ} → ρ ≡ʳ τ → τ ≡ʳ ρ
  ≡ʳ-sym ξ x = sym (ξ x)

  ≡ʳ-trans : ∀ {γ} {δ} → {ρ τ χ : γ →ʳ δ} → ρ ≡ʳ τ → τ ≡ʳ χ → ρ ≡ʳ χ
  ≡ʳ-trans ζ ξ x = trans (ζ x) (ξ x)

  -- identity renaming

  𝟙ʳ : ∀ {γ} → γ →ʳ γ
  𝟙ʳ x = x

  -- 𝟘 is the weakly initial shape

  𝟘-initial : ∀ {γ} → 𝟘 →ʳ γ
  𝟘-initial ()

  -- composition of renamings

  infixl 7 _∘ʳ_

  _∘ʳ_ : ∀ {γ} {δ} {Θ} → (δ →ʳ Θ) → (γ →ʳ δ) → (γ →ʳ Θ)
  (ρ ∘ʳ τ) x =  ρ (τ x)

  -- join of renamings

  infix 6 [_,_]ʳ

  [_,_]ʳ : ∀ {γ δ Θ} → (γ →ʳ Θ) → (δ →ʳ Θ) → (γ ⊕ δ →ʳ Θ)
  [ ρ , τ ]ʳ (var-left x) = ρ x
  [ ρ , τ ]ʳ (var-right y) = τ y

  -- renaming extension

  ⇑ʳ : ∀ {γ} {δ} {Θ} → (γ →ʳ δ) → (γ ⊕ Θ →ʳ δ ⊕ Θ)
  ⇑ʳ ρ (var-left x) =  var-left (ρ x)
  ⇑ʳ ρ (var-right y) = var-right y

  -- extension preserves equality

  ⇑ʳ-resp-≡ʳ : ∀ {γ} {δ} {Θ} {ρ τ : γ →ʳ δ} → ρ ≡ʳ τ → (⇑ʳ {Θ = Θ} ρ) ≡ʳ ⇑ʳ τ
  ⇑ʳ-resp-≡ʳ ξ (var-left x) = cong var-left (ξ x)
  ⇑ʳ-resp-≡ʳ ξ (var-right y) = cong var-right refl

  -- extension respects identity

  ⇑ʳ-resp-𝟙ʳ : ∀ {γ} {δ} → ⇑ʳ {Θ = δ} (𝟙ʳ {γ = γ}) ≡ʳ 𝟙ʳ
  ⇑ʳ-resp-𝟙ʳ (var-left x) = refl
  ⇑ʳ-resp-𝟙ʳ (var-right y) = refl

  -- extension commutes with composition

  ⇑ʳ-resp-∘ʳ : ∀ {B γ δ Θ} {ρ : B →ʳ γ} {τ : γ →ʳ δ} → ⇑ʳ {Θ = Θ} (τ ∘ʳ ρ) ≡ʳ ⇑ʳ τ ∘ʳ ⇑ʳ ρ
  ⇑ʳ-resp-∘ʳ (var-left x) = refl
  ⇑ʳ-resp-∘ʳ (var-right y) = refl

  -- the action of a renaming on an expression

  infixr 6 [_]ʳ_

  [_]ʳ_ : ∀ {γ} {cl} {δ} (ρ : γ →ʳ δ) → Expr (γ , cl) → Expr (δ , cl)
  [ ρ ]ʳ (x ` ts) = ρ x ` λ { y → [ ⇑ʳ ρ ]ʳ ts y }

  -- -- the action respects equality of renamings and equality of terms

  []ʳ-resp-≡ : ∀ {γ} {δ} {cl} {ρ : γ →ʳ δ} {t u : Expr (γ , cl)} →
               t ≡ u → [ ρ ]ʳ t ≡ [ ρ ]ʳ u
  []ʳ-resp-≡ refl = refl

  []ʳ-resp-≡ʳ : ∀ {γ} {δ} {cl} {ρ τ : γ →ʳ δ} (t : Expr (γ , cl)) →
                ρ ≡ʳ τ → [ ρ ]ʳ t ≡ [ τ ]ʳ t
  []ʳ-resp-≡ʳ (x ` ts) ξ = cong₂ _`_ (ξ x) (argext (λ y → []ʳ-resp-≡ʳ (ts y) (⇑ʳ-resp-≡ʳ ξ)))

  []ʳ-resp-≡ʳ-≡ : ∀ {γ} {δ} {cl}
                    {ρ τ : γ →ʳ δ} {t u : Expr (γ , cl)} → ρ ≡ʳ τ → t ≡ u → [ ρ ]ʳ t ≡ [ τ ]ʳ u
  []ʳ-resp-≡ʳ-≡ ζ ξ = trans ([]ʳ-resp-≡ʳ _ ζ) ([]ʳ-resp-≡ ξ)

  -- the action is functorial

  [𝟙ʳ] : ∀ {α} {t : Expr α} → [ 𝟙ʳ ]ʳ t ≡ t
  [𝟙ʳ] {t = x ` ts} = ≡-` λ y → trans ([]ʳ-resp-≡ʳ (ts y) ⇑ʳ-resp-𝟙ʳ) [𝟙ʳ]

  [∘ʳ] : ∀ {γ δ Θ cl} {ρ : γ →ʳ δ} {τ : δ →ʳ Θ} (t : Expr (γ , cl)) → [ τ ∘ʳ ρ ]ʳ t ≡ [ τ ]ʳ [ ρ ]ʳ t
  [∘ʳ] (x ` ts) = ≡-` (λ { y → trans ([]ʳ-resp-≡ʳ (ts y) ⇑ʳ-resp-∘ʳ) ([∘ʳ] (ts y)) })

  -- if a renaming equals identity then it acts as identity

  []ʳ-𝟙ʳ : ∀ {γ cl} {ρ : γ →ʳ γ} {t : Expr (γ , cl)} → ρ ≡ʳ 𝟙ʳ → [ ρ ]ʳ t ≡ t
  []ʳ-𝟙ʳ ξ = trans ([]ʳ-resp-≡ʳ _ ξ) [𝟙ʳ]

  -- the categorical structure of shapes and renamings

  module _ where
    open Categories.Category

    Renamings : Category lzero lzero lzero
    Renamings =
     record
       { Obj = Shape
       ; _⇒_ = _→ʳ_
       ; _≈_ = _≡ʳ_
       ; id = 𝟙ʳ
       ; _∘_ = _∘ʳ_
       ; assoc = λ { _ → refl }
       ; sym-assoc = λ { _ → refl }
       ; identityˡ = λ { _ → refl }
       ; identityʳ = λ { _ → refl }
       ; identity² = λ { _ → refl }
       ; equiv = record { refl = λ { _ → refl } ; sym = ≡ʳ-sym ; trans = ≡ʳ-trans }
       ; ∘-resp-≈ = λ {_} {_} {_} {ρ} {_} {_} {τ} ζ ξ → λ { x → trans (cong ρ (ξ x)) (ζ (τ x)) }
       }

  assoc-right : ∀ {γ δ η} → (γ ⊕ δ) ⊕ η →ʳ γ ⊕ (δ ⊕ η)
  assoc-right (var-left (var-left x)) = var-left x
  assoc-right (var-left (var-right y)) = var-right (var-left y)
  assoc-right (var-right z) = var-right (var-right z)

  assoc-left : ∀ {γ δ η} → γ ⊕ (δ ⊕ η) →ʳ (γ ⊕ δ) ⊕ η
  assoc-left (var-left x) = var-left (var-left x)
  assoc-left (var-right (var-left y)) = var-left (var-right y)
  assoc-left (var-right (var-right z)) = var-right z
