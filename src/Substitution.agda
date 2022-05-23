open import Agda.Primitive
open import Relation.Unary hiding (_∈_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Agda.Builtin.Sigma
open import Induction.WellFounded

open ≡-Reasoning

import Syntax
import Renaming

module Substitution (Class : Set) where

  open Syntax Class
  open Renaming Class

  -- equality of substitutions

  infix 4 _≡ˢ_

  _≡ˢ_ : ∀ {γ} {δ} (f g : γ →ˢ δ) → Set
  f ≡ˢ g = ∀ {αˣ} (x : αˣ ∈ _) → f x ≡ g x

  -- equality of substitutions is an equivalence relation

  ≡ˢ-refl : ∀ {γ} {δ} {f : γ →ˢ δ} → f ≡ˢ f
  ≡ˢ-refl x = refl

  ≡ˢ-sym : ∀ {γ} {δ} {f g : γ →ˢ δ} → f ≡ˢ g → g ≡ˢ f
  ≡ˢ-sym ξ x = sym (ξ x)

  ≡ˢ-trans : ∀ {γ} {δ} {f g h : γ →ˢ δ} → f ≡ˢ g → g ≡ˢ h → f ≡ˢ h
  ≡ˢ-trans ζ ξ x = trans (ζ x) (ξ x)

  -- identity substitution

  𝟙ˢ : ∀ {γ} → γ →ˢ γ
  𝟙ˢ var-here = (var-left var-here) ` λ x →  [ ⇑ʳ var-right ]ʳ 𝟙ˢ x
  𝟙ˢ (var-left x) =  [ ⇑ʳ var-left ]ʳ 𝟙ˢ x
  𝟙ˢ (var-right y) = [ ⇑ʳ var-right ]ʳ 𝟙ˢ y

  -- reqcursive equational for identity substitution

  unfold-𝟙ˢ : ∀ {γ} {αˣ} (x : αˣ ∈ γ) → 𝟙ˢ x ≡ var-left x ` (λ y → [ ⇑ʳ var-right ]ʳ 𝟙ˢ y)
  unfold-𝟙ˢ var-here = refl
  unfold-𝟙ˢ (var-left x) =
    begin
      𝟙ˢ (var-left x)
        ≡⟨ cong₂ [_]ʳ_ refl (unfold-𝟙ˢ x) ⟩
      [ ⇑ʳ var-left ]ʳ (var-left x ` (λ y → [ ⇑ʳ var-right ]ʳ 𝟙ˢ y))
        ≡⟨ ≡-` (λ y → sym ([∘ʳ] (𝟙ˢ y))) ⟩
      ⇑ʳ var-left (var-left x) ` (λ y → [ ⇑ʳ (⇑ʳ var-left) ∘ʳ ⇑ʳ var-right ]ʳ 𝟙ˢ y)
        ≡⟨ ≡-` (λ y → []ʳ-resp-≡ʳ (𝟙ˢ y) λ { (var-left _) → refl ; (var-right _) → refl}) ⟩
      var-left (var-left x) ` (λ y → [ ⇑ʳ var-right ]ʳ 𝟙ˢ y) ∎
  unfold-𝟙ˢ (var-right x) =
    begin
      𝟙ˢ (var-right x)
        ≡⟨  cong₂ [_]ʳ_ refl (unfold-𝟙ˢ x) ⟩
      [ ⇑ʳ var-right ]ʳ var-left x ` (λ y → [ ⇑ʳ var-right ]ʳ 𝟙ˢ y)
        ≡⟨ ≡-` (λ y → sym ([∘ʳ] (𝟙ˢ y))) ⟩
      var-left (var-right x) ` (λ y → [ ⇑ʳ (⇑ʳ var-right) ∘ʳ ⇑ʳ var-right ]ʳ 𝟙ˢ y)
        ≡⟨ ≡-` (λ y → []ʳ-resp-≡ʳ (𝟙ˢ y) λ { (var-left _) → refl ; (var-right _) → refl}) ⟩
      var-left (var-right x) ` (λ y → [ ⇑ʳ var-right ]ʳ 𝟙ˢ y) ∎

  -- substitution sum

  [_,_]ˢ : ∀ {γ δ Θ} (f : γ →ˢ Θ) (g : δ →ˢ Θ) → γ ⊕ δ →ˢ Θ
  [ f , g ]ˢ (var-left x) = f x
  [ f , g ]ˢ (var-right y) = g y

  -- substiutions sum respects equality

  [,]ˢ-resp-≡ˢ : ∀ {γ δ Θ} {f₁ f₂ : γ →ˢ Θ} {g₁ g₂ : δ →ˢ Θ} → f₁ ≡ˢ f₂ → g₁ ≡ˢ g₂ → [ f₁ , g₁ ]ˢ ≡ˢ [ f₂ , g₂ ]ˢ
  [,]ˢ-resp-≡ˢ ζ ξ (var-left x) = ζ x
  [,]ˢ-resp-≡ˢ ζ ξ (var-right y) = ξ y

  -- substitution extension

  ⇑ˢ : ∀ {γ δ Θ} → γ →ˢ δ → γ ⊕ Θ →ˢ δ ⊕ Θ
  ⇑ˢ f (var-left x) =  [ ⇑ʳ var-left ]ʳ f x
  ⇑ˢ f (var-right y) =  [ ⇑ʳ var-right ]ʳ 𝟙ˢ y

  -- substitution respects equality

  ⇑ˢ-resp-≡ˢ : ∀ {γ δ Θ} {f g : γ →ˢ δ} → f ≡ˢ g → ⇑ˢ {Θ = Θ} f ≡ˢ ⇑ˢ g
  ⇑ˢ-resp-≡ˢ ξ (var-left x) = []ʳ-resp-≡ (ξ x)
  ⇑ˢ-resp-≡ˢ ξ (var-right y) = refl

  infixl 7 _ʳ∘ˢ_

  _ʳ∘ˢ_ : ∀ {γ δ Θ} (ρ : δ →ʳ Θ) (f : γ →ˢ δ) → γ →ˢ Θ
  (ρ ʳ∘ˢ f) x = [ ⇑ʳ ρ ]ʳ f x

  -- action of substitution on an expression
  infix 6 [_]ˢ_
  [_]ˢ_ : ∀ {γ δ cl} (f : γ →ˢ δ) → Expr (γ , cl) → Expr (δ , cl)
  [ f ]ˢ var-here ` ts =  [ [ 𝟙ˢ , (λ y →  [ ⇑ˢ f ]ˢ ts y) ]ˢ ]ˢ f var-here
  [ f ]ˢ var-left x ` ts = {!!}
  [ f ]ˢ var-right x ` ts = {!!}


  -- unfold-[]ˢ : ∀ {γ δ cl} (f : γ →ˢ δ) → Expr (γ , cl) → Expr (δ , cl)
  -- [ f ]ˢ (x ` ts) ≡  [  [ 𝟙ˢ , (λ y →  [ ⇑ˢ f ]ˢ ts y) ]ˢ ]ˢ f x

  --     -- composition of substitutions
  --     infixl 7 _∘ˢ_
  --     _∘ˢ_ : ∀ {γ δ Θ} (g : δ →ˢ Θ) (f : γ →ˢ δ) → γ →ˢ Θ
  --     (g ∘ˢ f) x =  [ ⇑ˢ g ]ˢ f x

  --   -- In a formalism that accepts suspicious recursion, the action of substitution a one-liner:
  --   -- {-# TERMINATING #-}
  --   -- [_]ˢ_ : ∀ {γ δ A} (f : γ →ˢ δ) → Expr γ A → Expr δ A
  --   -- [ f ]ˢ x ` ts = [ [ 𝟙ˢ , f ∘ˢ ts ]ˢ ]ˢ f x

  --   -- We can still show that the equation holds, after some preparation

  -- --   inst-resp-≡ : ∀ {γ δ A} {f : γ →ˢ δ} {e₁ e₂ : Arg δ γ A} → e₁ ≡ e₂ → inst f e₁ ≡ inst f e₂
  -- --   inst-resp-≡ ξ = {!!}

  -- --   inst-resp-≡ˢ : ∀ {γ δ A} {f g : γ →ˢ δ} {e : Arg δ γ A} → f ≡ˢ g → inst f e ≡ inst g e
  -- --   inst-resp-≡ˢ ξ = {!!}

  --   -- mutual

  --   --   unfold-inst : ∀ {γ δ A} {f : γ →ˢ δ} {e : Arg δ γ A} → inst f e ≡ [ [ 𝟙ˢ , f ]ˢ ]ˢ e
  --   --   unfold-inst {f = f} {e = var-left x ` ts} =
  --   --      trans
  --   --        (unfold-inst-left {ts = ts})
  --   --        (≡-` (λ y → {!!}))
  --   --   unfold-inst {f = f} {e = var-right x ` ts} = {!!}
  --   --     -- ≈-trans
  --   --     --   (unfold-inst-right {f = f} {x = x} {ts = ts})
  --   --     --   (inst-resp-≡ˢ {e = f x} λ y → {!!})

  -- -- --     unfold-[]ˢ : ∀ {γ δ} {f : γ →ˢ δ} {Θ A} {x : [ Θ , A ]∈ γ} {ts : Θ →ˢ γ} →
  -- -- --                  [ f ]ˢ x ` ts ≈ [ [ 𝟙ˢ , f ∘ˢ ts ]ˢ ]ˢ f x
  -- -- --     unfold-[]ˢ {f = f} {x = x} {ts = ts} = unfold-inst {f = f ∘ˢ ts} {e = f x}

  -- -- -- -- -- -- composition of a substitutition and a renaming
  -- -- -- -- -- infixl 7 _ˢ∘ʳ_

  -- -- -- -- -- _ˢ∘ʳ_ :  ∀ {γ δ Θ} (f : δ →ˢ Θ) (ρ : γ →ʳ δ) → γ →ˢ Θ
  -- -- -- -- -- (f ˢ∘ʳ ρ) x = f (ρ x)

  -- -- -- -- -- -- [_]ˢ_ : ∀ {γ δ B} (f : γ →ˢ δ) → Expr γ B → Expr δ B
  -- -- -- -- -- -- [_]ˢ_ {γ = 𝟘} f (() ` _)
  -- -- -- -- -- -- [_]ˢ_ {γ = [ γ , A ]} f (var-here ` ts) =  [ {!!} ]ˢ f var-here
  -- -- -- -- -- -- [_]ˢ_ {γ = γ ⊕ δ} f (var-left x ` ts) = {! f (var-left x)!}
  -- -- -- -- -- -- [_]ˢ_ {γ = γ ⊕ δ} f (var-right y ` ts) = {!!}

  -- -- -- -- -- -- -- substitution respects equality

  -- -- -- -- -- -- []ˢ-resp-≈ : ∀ {γ δ A} (f : γ →ˢ δ) {t u : Expr γ A} → t ≈ u → [ f ]ˢ t ≈ [ f ]ˢ u

  -- -- -- -- -- -- []ˢ-resp-≡ˢ : ∀ {γ δ A} {f g : γ →ˢ δ} (t : Expr γ A) → f ≡ˢ g → [ f ]ˢ t ≈ [ g ]ˢ t

  -- -- -- -- -- -- []ˢ-resp-≈-≡ˢ : ∀ {γ δ A} {f g : γ →ˢ δ} {t u : Expr γ A} → f ≡ˢ g → t ≈ u → [ f ]ˢ t ≈ [ g ]ˢ u

  -- -- -- -- -- -- []ˢ-resp-≈ f (≈-≡ ξ) = ≈-≡ (cong ( [ f ]ˢ_) ξ)
  -- -- -- -- -- -- []ˢ-resp-≈ f (≈-` ξ) = ?

  -- -- -- -- -- -- []ˢ-resp-≡ˢ (x ` ts) ξ = []ˢ-resp-≈-≡ˢ
  -- -- -- -- -- --                            ([,]ˢ-resp-≡ˢ (λ x → ≈-refl) λ y → []ˢ-resp-≡ˢ (ts y) ((⇑ˢ-resp-≡ˢ ξ)))
  -- -- -- -- -- --                            (ξ x)

  -- -- -- -- -- -- []ˢ-resp-≈-≡ˢ {g = g} {t = t} ζ ξ = ≈-trans ([]ˢ-resp-≡ˢ t ζ) ([]ˢ-resp-≈ g ξ)

  -- -- -- -- -- -- -- composition of substitutitions

  -- -- -- -- -- -- infixl 7 _∘ˢ_

  -- -- -- -- -- -- _∘ˢ_ : ∀ {γ δ Θ} (g : δ →ˢ Θ) (f : γ →ˢ δ) → γ →ˢ Θ
  -- -- -- -- -- -- (g ∘ˢ f) x =  [ ⇑ˢ g ]ˢ f x

  -- -- -- -- -- -- -- composition of a renaming and a substitutition

  -- -- -- -- -- -- infixl 7 _ˢ∘ʳ_

  -- -- -- -- -- -- _ˢ∘ʳ_ :  ∀ {γ δ Θ} (f : δ →ˢ Θ) (ρ : γ →ʳ δ) → γ →ˢ Θ
  -- -- -- -- -- -- (f ˢ∘ʳ ρ) x = f (ρ x)

  -- -- -- -- -- -- -- extension respects identity

  -- -- -- -- -- -- ⇑ˢ-resp-𝟙ˢ : ∀ {γ Θ} → ⇑ˢ {Θ = Θ} (𝟙ˢ {γ = γ}) ≡ˢ 𝟙ˢ
  -- -- -- -- -- -- ⇑ˢ-resp-𝟙ˢ {γ = γ} (var-left x) = ≈-refl
  -- -- -- -- -- -- ⇑ˢ-resp-𝟙ˢ {γ = γ} (var-right y) = ≈-refl

  -- -- -- -- -- -- -- extension of a substitutition and a renaming respects composition

  -- -- -- -- -- -- ⇑ˢ-resp-ˢ∘ʳ : ∀ {γ δ Ξ Θ} {f : δ →ˢ Ξ} {ρ : γ →ʳ δ} →
  -- -- -- -- -- --               ⇑ˢ {Θ = Θ} (f ˢ∘ʳ ρ) ≡ˢ ⇑ˢ f ˢ∘ʳ ⇑ʳ ρ
  -- -- -- -- -- -- ⇑ˢ-resp-ˢ∘ʳ {f = f} (var-left x) = ≈-refl
  -- -- -- -- -- -- ⇑ˢ-resp-ˢ∘ʳ {f = f} (var-right y) = ≈-refl

  -- -- -- -- -- -- ⇑ˢ-resp-ʳ∘ˢ : ∀ {γ δ Ξ Θ} {ρ : δ →ʳ Ξ} {f : γ →ˢ δ} →
  -- -- -- -- -- --               ⇑ˢ {Θ = Θ} (ρ ʳ∘ˢ f) ≡ˢ ⇑ʳ ρ ʳ∘ˢ ⇑ˢ f

  -- -- -- -- -- -- ⇑ˢ-resp-ʳ∘ˢ {f = f} (var-left x) =
  -- -- -- -- -- --   ≈-trans
  -- -- -- -- -- --     (≈-sym ([∘ʳ] (f x)))
  -- -- -- -- -- --     (≈-trans
  -- -- -- -- -- --       ([]ʳ-resp-≡ʳ (f x) (λ { (var-left y) → refl ; (var-right z) → refl}))
  -- -- -- -- -- --       ([∘ʳ] (f x)))
  -- -- -- -- -- -- ⇑ˢ-resp-ʳ∘ˢ {ρ = ρ} {f = f} (var-right y) =
  -- -- -- -- -- --   ≈-trans
  -- -- -- -- -- --     ([]ʳ-resp-≡ʳ (𝟙ˢ y) (λ { (var-left _) → refl ; (var-right _) → refl}))
  -- -- -- -- -- --     ([∘ʳ] (𝟙ˢ y))

  -- -- -- -- -- -- -- composition of a renaming and a substitution respects equality

  -- -- -- -- -- -- [ˢ∘ʳ] : ∀ {γ δ Θ A} {f : δ →ˢ Θ} {ρ : γ →ʳ δ} → (t : Expr γ A) →
  -- -- -- -- -- --         [ f ˢ∘ʳ ρ ]ˢ t ≈ [ f ]ˢ [ ρ ]ʳ t
  -- -- -- -- -- -- [ˢ∘ʳ] {f = f} {ρ = ρ} (x ` ts) =
  -- -- -- -- -- --   []ˢ-resp-≡ˢ
  -- -- -- -- -- --     (f (ρ x))
  -- -- -- -- -- --     (λ { (var-left _) → ≈-refl
  -- -- -- -- -- --        ; (var-right y) → ≈-trans
  -- -- -- -- -- --                            ([]ˢ-resp-≡ˢ (ts y) (λ { (var-left _) → ≈-refl ; (var-right _) → ≈-refl}))
  -- -- -- -- -- --                            ([ˢ∘ʳ] (ts y))})

  -- -- -- -- -- -- {-# TERMINATING #-}
  -- -- -- -- -- -- [ʳ∘ˢ] : ∀ {γ δ Θ A} {ρ : δ →ʳ Θ} {f : γ →ˢ δ} (t : Expr γ A) →
  -- -- -- -- -- --         [ ρ ʳ∘ˢ f ]ˢ t ≈ [ ρ ]ʳ [ f ]ˢ t
  -- -- -- -- -- -- [ʳ∘ˢ] {ρ = ρ} {f = f} (x ` ts) =
  -- -- -- -- -- --   ≈-trans
  -- -- -- -- -- --     (≈-trans
  -- -- -- -- -- --        (≈-sym ([ˢ∘ʳ] (f x)))
  -- -- -- -- -- --        ([]ˢ-resp-≡ˢ (f x)
  -- -- -- -- -- --           (λ { (var-left y) →
  -- -- -- -- -- --                  ≈-trans
  -- -- -- -- -- --                    (𝟙ˢ-≈ (ρ y))
  -- -- -- -- -- --                    (≈-trans
  -- -- -- -- -- --                      (≈-` λ y → ≈-trans
  -- -- -- -- -- --                                   ([]ʳ-resp-≡ʳ (𝟙ˢ y) (λ { (var-left _) → refl ; (var-right _) → refl}))
  -- -- -- -- -- --                                   ([∘ʳ] (𝟙ˢ y)))
  -- -- -- -- -- --                      ([]ʳ-resp-≈ (⇑ʳ ρ) (≈-sym (𝟙ˢ-≈ y))))
  -- -- -- -- -- --           ; (var-right y) → ≈-trans ([]ˢ-resp-≡ˢ (ts y) ⇑ˢ-resp-ʳ∘ˢ) ([ʳ∘ˢ] (ts y))})))
  -- -- -- -- -- --     ([ʳ∘ˢ] (f x))

  -- -- -- -- -- -- -- composition of substitution respects identity
  -- -- -- -- -- -- [𝟙ˢ] : ∀ {γ A} (t : Expr γ A) → [ 𝟙ˢ ]ˢ t ≈ t
  -- -- -- -- -- -- [𝟙ˢ] {γ = 𝟘} (() ` _)
  -- -- -- -- -- -- [𝟙ˢ] {γ = [ γ , A ]} (var-here ` ts) = {!!}
  -- -- -- -- -- -- [𝟙ˢ] {γ = γ ⊕ δ} t = {!!}


  -- -- -- -- -- -- -- composition of substitutions respects equality

  -- -- -- -- -- -- {-# TERMINATING #-}
  -- -- -- -- -- -- [∘ˢ] : ∀ {γ δ Θ A} {g : δ →ˢ Θ} {f : γ →ˢ δ} (t : Expr γ A) → [ g ∘ˢ f ]ˢ t ≈ [ g ]ˢ [ f ]ˢ t
  -- -- -- -- -- -- [∘ˢ] {g = g} {f = f} (x ` ts) =
  -- -- -- -- -- --   ≈-trans
  -- -- -- -- -- --     (≈-sym ([∘ˢ] (f x)))
  -- -- -- -- -- --     (≈-trans
  -- -- -- -- -- --        ([]ˢ-resp-≡ˢ (f x)
  -- -- -- -- -- --           (λ { (var-left y) → {!!}
  -- -- -- -- -- --              ; (var-right _) → {!!}}))
  -- -- -- -- -- --        ([∘ˢ] (f x)))
