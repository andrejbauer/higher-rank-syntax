{-# OPTIONS --sized-types #-}

open import Level
open import Size
open import Relation.Binary.PropositionalEquality
import Categories.Category
import Syntax

module Renaming (Sort : Set) where

  open Syntax Sort

  infix 5 _→ʳ_

  _→ʳ_ : ∀ {j} {i : Size< ↑ j} → Shape i → Shape j → Set
  _→ʳ_ {i = i} Γ Δ = ∀ {k : Size< i} {Ξ : Shape k} {A} (x : [ Ξ , A ]∈ Γ) → [ Ξ , A ]∈ Δ

  -- equality of renamings
  infix 5 _≡ʳ_

  _≡ʳ_ : ∀ {j} {i : Size< ↑ j} {Γ : Shape i} {Δ : Shape j} → (ρ : Γ →ʳ Δ) → (τ : Γ →ʳ Δ) → Set
  _≡ʳ_ {i = i} {Γ = Γ} ρ τ = ∀ {k : Size< i} {Ξ : Shape k} {A} (x : [ Ξ , A ]∈ Γ) → ρ x ≡ τ x

  -- equality is an equivalence relation

  ≡ʳ-refl : ∀ {j} {i : Size< ↑ j} {Γ : Shape i} {Δ : Shape j} → {ρ : Γ →ʳ Δ} → ρ ≡ʳ ρ
  ≡ʳ-refl x = refl

  ≡ʳ-sym : ∀ {j} {i : Size< ↑ j} {Γ : Shape i} {Δ : Shape j} → {ρ τ : Γ →ʳ Δ} → ρ ≡ʳ τ → τ ≡ʳ ρ
  ≡ʳ-sym ξ x = sym (ξ x)

  ≡ʳ-trans : ∀ {j} {i : Size< ↑ j} {Γ : Shape i} {Δ : Shape j} → {ρ τ χ : Γ →ʳ Δ} → ρ ≡ʳ τ → τ ≡ʳ χ → ρ ≡ʳ χ
  ≡ʳ-trans ζ ξ x = trans (ζ x) (ξ x)

  -- identity renaming

  𝟙ʳ : ∀ {i} {Γ : Shape i} → Γ →ʳ Γ
  𝟙ʳ x = x

  -- 𝟘 is the weakly initial shape

  𝟘-initial : ∀ {i} {Γ : Shape i} → 𝟘 →ʳ Γ
  𝟘-initial ()

  -- composition of renamings

  infixl 7 _∘ʳ_

  _∘ʳ_ : ∀ {k} {j : Size< ↑ k} {i : Size< ↑ j} {Γ : Shape i} {Δ : Shape j} {Θ : Shape k} →
           (Δ →ʳ Θ) → (Γ →ʳ Δ) → (Γ →ʳ Θ)
  (ρ ∘ʳ τ) x =  ρ (τ x)

  -- join of renamings

  infix 6 [_,_]ʳ

  [_,_]ʳ : ∀ {γ δ η} → (γ →ʳ η) → (δ →ʳ η) → (γ ⊕ δ →ʳ η)
  [ ρ , τ ]ʳ (var-left x) = ρ x
  [ ρ , τ ]ʳ (var-right y) = τ y

  -- renaming extension

  ⇑ʳ : ∀ {j k} {i : Size< ↑ j} {Γ : Shape i} {Δ : Shape j} {Θ : Shape k} → (Γ →ʳ Δ) → (Γ ⊕ Θ →ʳ Δ ⊕ Θ)
  ⇑ʳ ρ (var-left x) =  var-left (ρ x)
  ⇑ʳ ρ (var-right y) = var-right y

  -- extension preserves equality

  ⇑ʳ-resp-≡ʳ : ∀ {j k} {i : Size< ↑ j} {Γ : Shape i} {Δ : Shape j} {Θ : Shape k} {ρ τ : Γ →ʳ Δ} → ρ ≡ʳ τ → ⇑ʳ {Θ = Θ} ρ ≡ʳ ⇑ʳ τ
  ⇑ʳ-resp-≡ʳ ξ (var-left x) = cong var-left (ξ x)
  ⇑ʳ-resp-≡ʳ ξ (var-right y) = refl

  -- extension respects identity

  ⇑ʳ-resp-𝟙ʳ : ∀ {i j} {Γ : Shape i} {Δ : Shape j} → ⇑ʳ {Θ = Δ} (𝟙ʳ {Γ = Γ})  ≡ʳ 𝟙ʳ
  ⇑ʳ-resp-𝟙ʳ (var-left x) = refl
  ⇑ʳ-resp-𝟙ʳ (var-right x) = refl

  -- extension commutes with composition

  ⇑ʳ-resp-∘ʳ : ∀ {k l} {j : Size< ↑ k} {i : Size< ↑ j} {B : Shape i} {Γ : Shape j} {Δ : Shape k} {Θ : Shape l}
                 {ρ : B →ʳ Γ} {τ : Γ →ʳ Δ} → ⇑ʳ {Θ = Θ} (τ ∘ʳ ρ) ≡ʳ ⇑ʳ τ ∘ʳ ⇑ʳ ρ
  ⇑ʳ-resp-∘ʳ (var-left x) = refl
  ⇑ʳ-resp-∘ʳ (var-right y) = refl

  -- the action of a renaming on an expression

  infixr 6 [_]ʳ_

  [_]ʳ_ : ∀ {j} {i : Size< ↑ j} {Γ : Shape i} {Δ : Shape j} {A} (ρ : Γ →ʳ Δ) → Expr Γ A → Expr Δ A
  [ ρ ]ʳ (x ` ts) = ρ x ` λ { y → [ ⇑ʳ ρ ]ʳ ts y }

  -- the action respects equality of renamings and equality of terms

  []ʳ-resp-≈ : ∀ {j} {i : Size< ↑ j} {Γ : Shape i} {Δ : Shape j} {A} (ρ : Γ →ʳ Δ) {t u : Expr Γ A} →
               t ≈ u → [ ρ ]ʳ t ≈ [ ρ ]ʳ u
  []ʳ-resp-≈ ρ (≈-≡ ξ) = ≈-≡ (cong ([ ρ ]ʳ_) ξ)
  []ʳ-resp-≈ ρ (≈-` ξ) = ≈-` (λ {y → []ʳ-resp-≈ (⇑ʳ ρ) (ξ y)})

  []ʳ-resp-≡ʳ : ∀ {j} {i : Size< ↑ j} {Γ : Shape i} {Δ : Shape j} {A} {ρ τ : Γ →ʳ Δ} (t : Expr Γ A) →
                ρ ≡ʳ τ → [ ρ ]ʳ t ≈ [ τ ]ʳ t
  []ʳ-resp-≡ʳ (x ` ts) ξ = ≈-trans (≈-≡ (cong (_` _) (ξ x))) (≈-` (λ { y → []ʳ-resp-≡ʳ (ts y) (⇑ʳ-resp-≡ʳ ξ) }))

  []ʳ-resp-≡ʳ-≈ : ∀ {j} {i : Size< ↑ j} {Γ : Shape i} {Δ : Shape j} {A}
                    {ρ τ : Γ →ʳ Δ} {t u : Expr Γ A} → ρ ≡ʳ τ → t ≈ u → [ ρ ]ʳ t ≈ [ τ ]ʳ u
  []ʳ-resp-≡ʳ-≈ ζ ξ = ≈-trans ([]ʳ-resp-≡ʳ _ ζ) ([]ʳ-resp-≈ _ ξ)

  -- the action is functorial

  [𝟙ʳ] : ∀ {i} {Γ : Shape i} {A} {t : Expr Γ A} → [ 𝟙ʳ ]ʳ t ≈ t
  [𝟙ʳ] {t = x ` ts} = ≈-` (λ { y → ≈-trans ([]ʳ-resp-≡ʳ (ts y) ⇑ʳ-resp-𝟙ʳ ) [𝟙ʳ] })

  [∘ʳ] : ∀ {Γ Δ Θ A} {ρ : Γ →ʳ Δ} {τ : Δ →ʳ Θ} (t : Expr Γ A) → [ τ ∘ʳ ρ ]ʳ t ≈ [ τ ]ʳ [ ρ ]ʳ t
  [∘ʳ] (x ` ts) = ≈-` (λ { y → ≈-trans ([]ʳ-resp-≡ʳ (ts y) ⇑ʳ-resp-∘ʳ) ([∘ʳ] (ts y)) })

  -- if a renaming equals identity then it acts as identity

  []ʳ-𝟙ʳ : ∀ {Γ A} {ρ : Γ →ʳ Γ} {t : Expr Γ A} → ρ ≡ʳ 𝟙ʳ → [ ρ ]ʳ t ≈ t
  []ʳ-𝟙ʳ ξ = ≈-trans ([]ʳ-resp-≡ʳ _ ξ) [𝟙ʳ]

  -- the categorical structure of shapes and renamings

  module _ where
    open Categories.Category

    Renamings : ∀ {i : Size} → Category zero zero zero
    Renamings {i} =
     record
       { Obj = Shape i
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
