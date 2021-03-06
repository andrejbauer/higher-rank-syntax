open import Agda.Primitive
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Agda.Builtin.Sigma
open import Induction.WellFounded

import Syntax
import Renaming

module Substitution (Class : Set) where

  open Syntax Class
  open Renaming Class

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

  -- definition of identity substitution using well-founded recursion
  𝟙ˢ : ∀ {Γ} → Γ →ˢ Γ
  𝟙ˢ = rec-∈
         (λ {Γ} {Θ} {A} _ → Arg Γ Θ A)
         (λ x r → var-left x ` λ y → [ ⇑ʳ var-right ]ʳ r y)

  -- This is how we would define the identity substitution if Agda were smarter
  -- {-# TERMINATING #-}
  -- 𝟙ˢ : ∀ {Γ} → Γ →ˢ Γ
  -- 𝟙ˢ x =  var-left x ` λ y →  [ ⇑ʳ var-right ]ʳ 𝟙ˢ y

  -- Equational characterization of identity substitution

  unfold-𝟙ˢ : ∀ {Γ Θ A} (x : [ Θ , A ]∈ Γ) →
              𝟙ˢ x ≈ var-left x ` (λ y → [ ⇑ʳ var-right ]ʳ 𝟙ˢ y)
  unfold-𝟙ˢ {Γ} {Θ} {A} x =
    unfold-rec-∈
      (λ {Γ} {Θ} {A} _ → Arg Γ Θ A)
      (λ x r → var-left x ` λ y → [ ⇑ʳ var-right ]ʳ r y)
      _≈_
      (λ _ ξ → ≈-` (λ y → []ʳ-resp-≈ (⇑ʳ var-right) (ξ y)))

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

  infixl 7 _ʳ∘ˢ_

  _ʳ∘ˢ_ : ∀ {Γ Δ Θ} (ρ : Δ →ʳ Θ) (f : Γ →ˢ Δ) → Γ →ˢ Θ
  (ρ ʳ∘ˢ f) x = [ ⇑ʳ ρ ]ʳ f x

  -- instantiation of bound variables
  module _ where

    open import Data.Nat
    open import Data.Nat.Properties
    open import Data.Nat.Induction
    open import Data.Product
    open import Data.Product.Relation.Binary.Lex.Strict

    -- we proceed by well-founded recursion on the size measured by the lexicographic order given by _≺_ and _<_
    _≺,<_ = ×-Lex _≡_ _≺_ _<_
    wf-≺,< = ×-wellFounded wf-≺ <-wellFounded

    -- the type family over which we recurse to define instantiation
    P : Shape × ℕ → Set
    P (Γ , n) = ∀ {Δ A} (f : Γ →ˢ Δ) (e : Arg Δ Γ A) → size e ≡ n → Expr Δ A

    -- an auxiliary renaming
    swap-bound : ∀ {Γ Θ Ξ} → (Γ ⊕ Θ) ⊕ Ξ →ʳ (Γ ⊕ Ξ) ⊕ Θ
    swap-bound (var-left (var-left x)) = var-left (var-left x)
    swap-bound (var-left (var-right y)) = var-right y
    swap-bound (var-right z) = var-left (var-right z)

    open All wf-≺,< lzero

    -- the matrix of the recursion
    b : ∀ (Γ,m : Shape × ℕ) → (∀ (Ω,n : Shape × ℕ) → Ω,n ≺,< Γ,m → P Ω,n) → P Γ,m
    b (Γ , n) r f (var-left x ` ts) ξ =
      x ` λ y → r (Γ , (size ([ swap-bound ]ʳ ts y)))
                  (inj₂ (refl , respʳ _<_ ξ (respˡ _<_ []ʳ-resp-size (size-arg-< {x = var-left x}))))
                  (var-left ʳ∘ˢ f) ([ swap-bound ]ʳ ts y) refl
    b (Γ , n) r f (var-right x ` ts) ξ =
      r (_ , (size (f x))) (inj₁ (≺-∈ x))
        (λ y → r (Γ , size ([ swap-bound ]ʳ ts y))
                 (inj₂ (refl , respʳ _<_ ξ (respˡ _<_ []ʳ-resp-size (size-arg-< {x = var-right x}))))
                 (var-left ʳ∘ˢ f) ([ swap-bound ]ʳ ts y) refl)
        (f x) refl

    inst : ∀ {Γ Δ A} → (Γ →ˢ Δ) → Arg Δ Γ A → Expr Δ A
    inst {Γ = Γ} f e = wfRec P b (Γ , (size e)) f e refl

    _≡'_ : ∀ {Γ} {n} (u v : ∀ {Δ A} (g : Γ →ˢ Δ) (e : Arg Δ Γ A) → size e ≡ n → Expr Δ A) → Set
    u ≡' v = ∀ {Δ A} (g : _ →ˢ Δ) (e : Arg Δ _ A) ξ → u g e ξ ≡ v g e ξ

    -- the matrix respects syntacitc equality in all arguments
    b-ext : ∀ Γ,m {r₁ r₂ : WfRec _≺,<_ P Γ,m} → (∀ {Ω,n} (p : Ω,n ≺,< Γ,m) → r₁ Ω,n p ≡' r₂ Ω,n p) → b Γ,m r₁ ≡' b Γ,m r₂
    b-ext (Γ , m) ζ g (var-left x ` _) _ = cong (_`_ x) ( (arg-extensionality λ y → ζ _ _ _ refl) )
    b-ext (Γ , m) {r₁} {r₂} ζ g (var-right x ` ts) ξ =
      trans
        (cong-app (cong-app (cong (r₁ _ _) (arg-extensionality (λ y → ζ _ _ _ refl))) _) _)
        (ζ _ _ _ refl)

    open import FixPointRel wf-≺,< lzero P b _≡'_ b-ext

    unfold-inst-left : ∀ {Γ Δ Ξ A} {f : Γ →ˢ Δ} {x : [ Ξ , A ]∈ Δ} {ts : Ξ →ˢ Δ ⊕ Γ} →
                         inst f (var-left x ` ts) ≈ x ` λ y → inst (var-left ʳ∘ˢ f) ([ swap-bound ]ʳ ts y)
    unfold-inst-left {Γ = Γ} {Δ = Δ} {A = A} {f = f} {x = x} {ts = ts} =
      ≈-≡ (unfold-wfRec f (var-left x ` ts) refl)

    unfold-inst-right : ∀ {Γ Δ Ξ A} {f : Γ →ˢ Δ} {x : [ Ξ , A ]∈ Γ} {ts : Ξ →ˢ Δ ⊕ Γ} →
                          inst f (var-right x ` ts) ≈ inst (λ y → inst (var-left ʳ∘ˢ f) ([ swap-bound ]ʳ ts y)) (f x)
    unfold-inst-right {Γ = Γ} {Δ = Δ} {A = A} {f = f} {x = x} {ts = ts} =
      ≈-≡ (unfold-wfRec f (var-right x ` ts) refl)

    mutual
      -- the action of a substitution on an expression
      infix 6 [_]ˢ_
      [_]ˢ_ : ∀ {Γ Δ A} (f : Γ →ˢ Δ) → Expr Γ A → Expr Δ A
      [_]ˢ_ f (x ` ts) = inst (f ∘ˢ ts) (f x)

      -- composition of substitutions
      infixl 7 _∘ˢ_
      _∘ˢ_ : ∀ {Γ Δ Θ} (g : Δ →ˢ Θ) (f : Γ →ˢ Δ) → Γ →ˢ Θ
      (g ∘ˢ f) x =  [ ⇑ˢ g ]ˢ f x

    -- In a formalism that accepts suspicious recursion, the action of substitution a one-liner:
    -- {-# TERMINATING #-}
    -- [_]ˢ_ : ∀ {Γ Δ A} (f : Γ →ˢ Δ) → Expr Γ A → Expr Δ A
    -- [ f ]ˢ x ` ts = [ [ 𝟙ˢ , f ∘ˢ ts ]ˢ ]ˢ f x

    -- We can still show that the equation holds, after some preparation

    inst-resp-≈ : ∀ {Γ Δ A} {f : Γ →ˢ Δ} {e₁ e₂ : Arg Δ Γ A} → e₁ ≈ e₂ → inst f e₁ ≈ inst f e₂
    inst-resp-≈ ξ = {!!}

    inst-resp-≈ˢ : ∀ {Γ Δ A} {f g : Γ →ˢ Δ} {e : Arg Δ Γ A} → f ≈ˢ g → inst f e ≈ inst g e
    inst-resp-≈ˢ ξ = {!!}

    mutual

      unfold-inst : ∀ {Γ Δ A} {f : Γ →ˢ Δ} {e : Arg Δ Γ A} → inst f e ≈ [ [ 𝟙ˢ , f ]ˢ ]ˢ e
      unfold-inst {f = f} {e = var-left x ` ts} =
         ≈-trans
           (unfold-inst-left {ts = ts})
           {!!}
      unfold-inst {f = f} {e = var-right x ` ts} = {!!}
        -- ≈-trans
        --   (unfold-inst-right {f = f} {x = x} {ts = ts})
        --   (inst-resp-≈ˢ {e = f x} λ y → {!!})

      unfold-[]ˢ : ∀ {Γ Δ} {f : Γ →ˢ Δ} {Θ A} {x : [ Θ , A ]∈ Γ} {ts : Θ →ˢ Γ} →
                   [ f ]ˢ x ` ts ≈ [ [ 𝟙ˢ , f ∘ˢ ts ]ˢ ]ˢ f x
      unfold-[]ˢ {f = f} {x = x} {ts = ts} = unfold-inst {f = f ∘ˢ ts} {e = f x}

  -- -- -- composition of a substitutition and a renaming
  -- -- infixl 7 _ˢ∘ʳ_

  -- -- _ˢ∘ʳ_ :  ∀ {Γ Δ Θ} (f : Δ →ˢ Θ) (ρ : Γ →ʳ Δ) → Γ →ˢ Θ
  -- -- (f ˢ∘ʳ ρ) x = f (ρ x)

  -- -- -- [_]ˢ_ : ∀ {Γ Δ B} (f : Γ →ˢ Δ) → Expr Γ B → Expr Δ B
  -- -- -- [_]ˢ_ {Γ = 𝟘} f (() ` _)
  -- -- -- [_]ˢ_ {Γ = [ Γ , A ]} f (var-here ` ts) =  [ {!!} ]ˢ f var-here
  -- -- -- [_]ˢ_ {Γ = Γ ⊕ Δ} f (var-left x ` ts) = {! f (var-left x)!}
  -- -- -- [_]ˢ_ {Γ = Γ ⊕ Δ} f (var-right y ` ts) = {!!}

  -- -- -- -- substitution respects equality

  -- -- -- []ˢ-resp-≈ : ∀ {Γ Δ A} (f : Γ →ˢ Δ) {t u : Expr Γ A} → t ≈ u → [ f ]ˢ t ≈ [ f ]ˢ u

  -- -- -- []ˢ-resp-≈ˢ : ∀ {Γ Δ A} {f g : Γ →ˢ Δ} (t : Expr Γ A) → f ≈ˢ g → [ f ]ˢ t ≈ [ g ]ˢ t

  -- -- -- []ˢ-resp-≈-≈ˢ : ∀ {Γ Δ A} {f g : Γ →ˢ Δ} {t u : Expr Γ A} → f ≈ˢ g → t ≈ u → [ f ]ˢ t ≈ [ g ]ˢ u

  -- -- -- []ˢ-resp-≈ f (≈-≡ ξ) = ≈-≡ (cong ( [ f ]ˢ_) ξ)
  -- -- -- []ˢ-resp-≈ f (≈-` ξ) = ?

  -- -- -- []ˢ-resp-≈ˢ (x ` ts) ξ = []ˢ-resp-≈-≈ˢ
  -- -- --                            ([,]ˢ-resp-≈ˢ (λ x → ≈-refl) λ y → []ˢ-resp-≈ˢ (ts y) ((⇑ˢ-resp-≈ˢ ξ)))
  -- -- --                            (ξ x)

  -- -- -- []ˢ-resp-≈-≈ˢ {g = g} {t = t} ζ ξ = ≈-trans ([]ˢ-resp-≈ˢ t ζ) ([]ˢ-resp-≈ g ξ)

  -- -- -- -- composition of substitutitions

  -- -- -- infixl 7 _∘ˢ_

  -- -- -- _∘ˢ_ : ∀ {Γ Δ Θ} (g : Δ →ˢ Θ) (f : Γ →ˢ Δ) → Γ →ˢ Θ
  -- -- -- (g ∘ˢ f) x =  [ ⇑ˢ g ]ˢ f x

  -- -- -- -- composition of a renaming and a substitutition

  -- -- -- infixl 7 _ˢ∘ʳ_

  -- -- -- _ˢ∘ʳ_ :  ∀ {Γ Δ Θ} (f : Δ →ˢ Θ) (ρ : Γ →ʳ Δ) → Γ →ˢ Θ
  -- -- -- (f ˢ∘ʳ ρ) x = f (ρ x)

  -- -- -- -- extension respects identity

  -- -- -- ⇑ˢ-resp-𝟙ˢ : ∀ {Γ Θ} → ⇑ˢ {Θ = Θ} (𝟙ˢ {Γ = Γ}) ≈ˢ 𝟙ˢ
  -- -- -- ⇑ˢ-resp-𝟙ˢ {Γ = Γ} (var-left x) = ≈-refl
  -- -- -- ⇑ˢ-resp-𝟙ˢ {Γ = Γ} (var-right y) = ≈-refl

  -- -- -- -- extension of a substitutition and a renaming respects composition

  -- -- -- ⇑ˢ-resp-ˢ∘ʳ : ∀ {Γ Δ Ξ Θ} {f : Δ →ˢ Ξ} {ρ : Γ →ʳ Δ} →
  -- -- --               ⇑ˢ {Θ = Θ} (f ˢ∘ʳ ρ) ≈ˢ ⇑ˢ f ˢ∘ʳ ⇑ʳ ρ
  -- -- -- ⇑ˢ-resp-ˢ∘ʳ {f = f} (var-left x) = ≈-refl
  -- -- -- ⇑ˢ-resp-ˢ∘ʳ {f = f} (var-right y) = ≈-refl

  -- -- -- ⇑ˢ-resp-ʳ∘ˢ : ∀ {Γ Δ Ξ Θ} {ρ : Δ →ʳ Ξ} {f : Γ →ˢ Δ} →
  -- -- --               ⇑ˢ {Θ = Θ} (ρ ʳ∘ˢ f) ≈ˢ ⇑ʳ ρ ʳ∘ˢ ⇑ˢ f

  -- -- -- ⇑ˢ-resp-ʳ∘ˢ {f = f} (var-left x) =
  -- -- --   ≈-trans
  -- -- --     (≈-sym ([∘ʳ] (f x)))
  -- -- --     (≈-trans
  -- -- --       ([]ʳ-resp-≡ʳ (f x) (λ { (var-left y) → refl ; (var-right z) → refl}))
  -- -- --       ([∘ʳ] (f x)))
  -- -- -- ⇑ˢ-resp-ʳ∘ˢ {ρ = ρ} {f = f} (var-right y) =
  -- -- --   ≈-trans
  -- -- --     ([]ʳ-resp-≡ʳ (𝟙ˢ y) (λ { (var-left _) → refl ; (var-right _) → refl}))
  -- -- --     ([∘ʳ] (𝟙ˢ y))

  -- -- -- -- composition of a renaming and a substitution respects equality

  -- -- -- [ˢ∘ʳ] : ∀ {Γ Δ Θ A} {f : Δ →ˢ Θ} {ρ : Γ →ʳ Δ} → (t : Expr Γ A) →
  -- -- --         [ f ˢ∘ʳ ρ ]ˢ t ≈ [ f ]ˢ [ ρ ]ʳ t
  -- -- -- [ˢ∘ʳ] {f = f} {ρ = ρ} (x ` ts) =
  -- -- --   []ˢ-resp-≈ˢ
  -- -- --     (f (ρ x))
  -- -- --     (λ { (var-left _) → ≈-refl
  -- -- --        ; (var-right y) → ≈-trans
  -- -- --                            ([]ˢ-resp-≈ˢ (ts y) (λ { (var-left _) → ≈-refl ; (var-right _) → ≈-refl}))
  -- -- --                            ([ˢ∘ʳ] (ts y))})

  -- -- -- {-# TERMINATING #-}
  -- -- -- [ʳ∘ˢ] : ∀ {Γ Δ Θ A} {ρ : Δ →ʳ Θ} {f : Γ →ˢ Δ} (t : Expr Γ A) →
  -- -- --         [ ρ ʳ∘ˢ f ]ˢ t ≈ [ ρ ]ʳ [ f ]ˢ t
  -- -- -- [ʳ∘ˢ] {ρ = ρ} {f = f} (x ` ts) =
  -- -- --   ≈-trans
  -- -- --     (≈-trans
  -- -- --        (≈-sym ([ˢ∘ʳ] (f x)))
  -- -- --        ([]ˢ-resp-≈ˢ (f x)
  -- -- --           (λ { (var-left y) →
  -- -- --                  ≈-trans
  -- -- --                    (𝟙ˢ-≈ (ρ y))
  -- -- --                    (≈-trans
  -- -- --                      (≈-` λ y → ≈-trans
  -- -- --                                   ([]ʳ-resp-≡ʳ (𝟙ˢ y) (λ { (var-left _) → refl ; (var-right _) → refl}))
  -- -- --                                   ([∘ʳ] (𝟙ˢ y)))
  -- -- --                      ([]ʳ-resp-≈ (⇑ʳ ρ) (≈-sym (𝟙ˢ-≈ y))))
  -- -- --           ; (var-right y) → ≈-trans ([]ˢ-resp-≈ˢ (ts y) ⇑ˢ-resp-ʳ∘ˢ) ([ʳ∘ˢ] (ts y))})))
  -- -- --     ([ʳ∘ˢ] (f x))

  -- -- -- -- composition of substitution respects identity
  -- -- -- [𝟙ˢ] : ∀ {Γ A} (t : Expr Γ A) → [ 𝟙ˢ ]ˢ t ≈ t
  -- -- -- [𝟙ˢ] {Γ = 𝟘} (() ` _)
  -- -- -- [𝟙ˢ] {Γ = [ Γ , A ]} (var-here ` ts) = {!!}
  -- -- -- [𝟙ˢ] {Γ = Γ ⊕ Δ} t = {!!}


  -- -- -- -- composition of substitutions respects equality

  -- -- -- {-# TERMINATING #-}
  -- -- -- [∘ˢ] : ∀ {Γ Δ Θ A} {g : Δ →ˢ Θ} {f : Γ →ˢ Δ} (t : Expr Γ A) → [ g ∘ˢ f ]ˢ t ≈ [ g ]ˢ [ f ]ˢ t
  -- -- -- [∘ˢ] {g = g} {f = f} (x ` ts) =
  -- -- --   ≈-trans
  -- -- --     (≈-sym ([∘ˢ] (f x)))
  -- -- --     (≈-trans
  -- -- --        ([]ˢ-resp-≈ˢ (f x)
  -- -- --           (λ { (var-left y) → {!!}
  -- -- --              ; (var-right _) → {!!}}))
  -- -- --        ([∘ˢ] (f x)))
