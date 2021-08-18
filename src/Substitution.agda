open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

import Syntax
import Renaming

module Substitution (Class : Set) where

  open Syntax Class
  open Renaming Class

  -- the set of substitutions

  infix 5 _→ˢ_

  _→ˢ_ : Shape → Shape → Set
  Γ →ˢ Δ = ∀ {Θ} {A} (x : [ Θ , A ]∈ Γ) → Arg Δ Θ A

  -- equality of substitutions

  infix 4 _≈ˢ_

  _≈ˢ_ : ∀ {Γ} {Δ} (f g : Γ →ˢ Δ) → Set
  f ≈ˢ g = ∀ {Θ} {A} (x : [ Θ , A ]∈ _) → f x ≈ g x

  -- equality of substitutions is an equivalence relation

  ≈ˢ-refl : ∀ {Γ} {Δ} {f : Γ →ˢ Δ} → f ≈ˢ f
  ≈ˢ-refl x = ≈-refl

  ≈ˢ-sym : ∀ {Γ} {Δ} {f g : Γ →ˢ Δ} → f ≈ˢ g → g ≈ˢ f
  ≈ˢ-sym ξ x = ≈-sym (ξ x)

  ≈ˢ-trans : ∀ {Γ} {Δ} {f g h : Γ →ˢ Δ} → f ≈ˢ g → g ≈ˢ h → f ≈ˢ h
  ≈ˢ-trans ζ ξ x = ≈-trans (ζ x) (ξ x)

  -- identity substitution

  -- {-# TERMINATING #-}
  -- 𝟙ˢ : ∀ {Γ} → Γ →ˢ Γ
  -- 𝟙ˢ x =  var-left x ` λ y →  [ 2-to-3-right ]ʳ 𝟙ˢ y

  -- definition of identity substitution which does not require any magic
  𝟙ˢ : ∀ {Γ} → Γ →ˢ Γ
  𝟙ˢ {𝟘} ()
  𝟙ˢ {[ Γ , A ]} var-here = var-left var-here ` λ y →  [ ⇑ʳ var-right ]ʳ 𝟙ˢ y
  𝟙ˢ {Γ Syntax.⊕ Δ} (var-left x) =  [ ⇑ʳ var-left ]ʳ 𝟙ˢ x
  𝟙ˢ {Γ Syntax.⊕ Δ} (var-right y) = [ ⇑ʳ var-right ]ʳ 𝟙ˢ y

  𝟙ˢ-≈ : ∀ {Γ Δ A} (x : [ Δ , A ]∈ Γ) → 𝟙ˢ x ≈ var-left x ` λ y → [ ⇑ʳ var-right ]ʳ 𝟙ˢ y
  𝟙ˢ-≈ {Γ = [ Γ , A ]} var-here = ≈-refl
  𝟙ˢ-≈ {Γ = Γ ⊕ Δ} (var-left x) = {!!}
  𝟙ˢ-≈ {Γ = Γ ⊕ Δ} (var-right y) = {!!}

  -- substitution sum

  [_,_]ˢ : ∀ {Γ Δ Θ} (f : Γ →ˢ Θ) (g : Δ →ˢ Θ) → Γ ⊕ Δ →ˢ Θ
  [ f , g ]ˢ (var-left x) = f x
  [ f , g ]ˢ (var-right y) = g y

  -- substiutions sum respects equality

  [,]ˢ-resp-≈ˢ : ∀ {Γ Δ Θ} {f₁ f₂ : Γ →ˢ Θ} {g₁ g₂ : Δ →ˢ Θ} → f₁ ≈ˢ f₂ → g₁ ≈ˢ g₂ → [ f₁ , g₁ ]ˢ ≈ˢ [ f₂ , g₂ ]ˢ
  [,]ˢ-resp-≈ˢ ζ ξ (var-left x) = ζ x
  [,]ˢ-resp-≈ˢ ζ ξ (var-right y) = ξ y

  -- substitution extension

  ⇑ˢ : ∀ {Γ Δ Θ} → Γ →ˢ Δ → Γ ⊕ Θ →ˢ Δ ⊕ Θ
  ⇑ˢ f (var-left x) =  [ ⇑ʳ var-left ]ʳ f x
  ⇑ˢ f (var-right y) =  [ ⇑ʳ var-right ]ʳ 𝟙ˢ y

  -- substitution respects equality

  ⇑ˢ-resp-≈ˢ : ∀ {Γ Δ Θ} {f g : Γ →ˢ Δ} → f ≈ˢ g → ⇑ˢ {Θ = Θ} f ≈ˢ ⇑ˢ g
  ⇑ˢ-resp-≈ˢ ξ (var-left x) = []ʳ-resp-≈ _ (ξ x)
  ⇑ˢ-resp-≈ˢ ξ (var-right y) = ≈-refl

  -- the action of a substitution on an expression

  infix 6 [_]ˢ_

  {-# TERMINATING #-}
  [_]ˢ_ : ∀ {Γ Δ B} (f : Γ →ˢ Δ) → Expr Γ B → Expr Δ B
  [ f ]ˢ x ` ts =  [ [ 𝟙ˢ , (λ z → [ ⇑ˢ f ]ˢ ts z) ]ˢ ]ˢ f x

  -- substitution respects equality

  {-# TERMINATING #-}
  []ˢ-resp-≈ : ∀ {Γ Δ A} (f : Γ →ˢ Δ) {t u : Expr Γ A} → t ≈ u → [ f ]ˢ t ≈ [ f ]ˢ u

  []ˢ-resp-≈ˢ : ∀ {Γ Δ A} {f g : Γ →ˢ Δ} (t : Expr Γ A) → f ≈ˢ g → [ f ]ˢ t ≈ [ g ]ˢ t

  []ˢ-resp-≈-≈ˢ : ∀ {Γ Δ A} {f g : Γ →ˢ Δ} {t u : Expr Γ A} → f ≈ˢ g → t ≈ u → [ f ]ˢ t ≈ [ g ]ˢ u

  []ˢ-resp-≈ f (≈-≡ ξ) = ≈-≡ (cong ( [ f ]ˢ_) ξ)
  []ˢ-resp-≈ f (≈-` ξ) = []ˢ-resp-≈ˢ (f _) ([,]ˢ-resp-≈ˢ (λ y → ≈-refl) (λ y → []ˢ-resp-≈ (⇑ˢ f) (ξ y)))

  []ˢ-resp-≈ˢ (x ` ts) ξ = []ˢ-resp-≈-≈ˢ
                             ([,]ˢ-resp-≈ˢ (λ x → ≈-refl) λ y → []ˢ-resp-≈ˢ (ts y) ((⇑ˢ-resp-≈ˢ ξ)))
                             (ξ x)

  []ˢ-resp-≈-≈ˢ {g = g} {t = t} ζ ξ = ≈-trans ([]ˢ-resp-≈ˢ t ζ) ([]ˢ-resp-≈ g ξ)

  -- composition of substitutitions

  infixl 7 _∘ˢ_

  _∘ˢ_ : ∀ {Γ Δ Θ} (g : Δ →ˢ Θ) (f : Γ →ˢ Δ) → Γ →ˢ Θ
  (g ∘ˢ f) x =  [ ⇑ˢ g ]ˢ f x

  -- composition of a renaming and a substitutition

  infixl 7 _ˢ∘ʳ_

  _ˢ∘ʳ_ :  ∀ {Γ Δ Θ} (f : Δ →ˢ Θ) (ρ : Γ →ʳ Δ) → Γ →ˢ Θ
  (f ˢ∘ʳ ρ) x = f (ρ x)

  infixl 7 _ʳ∘ˢ_

  _ʳ∘ˢ_ : ∀ {Γ Δ Θ} (ρ : Δ →ʳ Θ) (f : Γ →ˢ Δ) → Γ →ˢ Θ
  (ρ ʳ∘ˢ f) x = [ ⇑ʳ ρ ]ʳ f x

  -- extension respects composition

  ⇑ˢ-resp-ˢ∘ʳ : ∀ {Γ Δ Ξ Θ} {f : Δ →ˢ Ξ} {ρ : Γ →ʳ Δ} →
                ⇑ˢ {Θ = Θ} (f ˢ∘ʳ ρ) ≈ˢ ⇑ˢ f ˢ∘ʳ ⇑ʳ ρ
  ⇑ˢ-resp-ˢ∘ʳ {f = f} (var-left x) = ≈-refl
  ⇑ˢ-resp-ˢ∘ʳ {f = f} (var-right y) = ≈-refl

  ⇑ˢ-resp-ʳ∘ˢ : ∀ {Γ Δ Ξ Θ} {ρ : Δ →ʳ Ξ} {f : Γ →ˢ Δ} →
                ⇑ˢ {Θ = Θ} (ρ ʳ∘ˢ f) ≈ˢ ⇑ʳ ρ ʳ∘ˢ ⇑ˢ f

  ⇑ˢ-resp-ʳ∘ˢ {f = f} (var-left x) =
    ≈-trans
      (≈-sym ([∘ʳ] (f x)))
      (≈-trans
        ([]ʳ-resp-≡ʳ (f x) (λ { (var-left y) → refl ; (var-right z) → refl}))
        ([∘ʳ] (f x)))
  ⇑ˢ-resp-ʳ∘ˢ {ρ = ρ} {f = f} (var-right y) =
    ≈-trans
      ([]ʳ-resp-≡ʳ (𝟙ˢ y) (λ { (var-left _) → refl ; (var-right _) → refl}))
      ([∘ʳ] (𝟙ˢ y))

  -- composition of a renaming and a substitution respects equality

  [ˢ∘ʳ] : ∀ {Γ Δ Θ A} {f : Δ →ˢ Θ} {ρ : Γ →ʳ Δ} → (t : Expr Γ A) →
          [ f ˢ∘ʳ ρ ]ˢ t ≈ [ f ]ˢ [ ρ ]ʳ t
  [ˢ∘ʳ] {f = f} {ρ = ρ} (x ` ts) =
    []ˢ-resp-≈ˢ
      (f (ρ x))
      (λ { (var-left _) → ≈-refl
         ; (var-right y) → ≈-trans
                             ([]ˢ-resp-≈ˢ (ts y) (λ { (var-left _) → ≈-refl ; (var-right _) → ≈-refl}))
                             ([ˢ∘ʳ] (ts y))})

  {-# TERMINATING #-}
  [ʳ∘ˢ] : ∀ {Γ Δ Θ A} {ρ : Δ →ʳ Θ} {f : Γ →ˢ Δ} (t : Expr Γ A) →
          [ ρ ʳ∘ˢ f ]ˢ t ≈ [ ρ ]ʳ [ f ]ˢ t
  [ʳ∘ˢ] {ρ = ρ} {f = f} (x ` ts) =
    ≈-trans
      (≈-trans
         (≈-sym ([ˢ∘ʳ] (f x)))
         ([]ˢ-resp-≈ˢ (f x) (λ { (var-left y) → {!!}
                               ; (var-right y) → ≈-trans ([]ˢ-resp-≈ˢ (ts y) ⇑ˢ-resp-ʳ∘ˢ) ([ʳ∘ˢ] (ts y))})))
      ([ʳ∘ˢ] (f x))
