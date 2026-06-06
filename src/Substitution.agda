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

module Substitution where

  open Syntax
  open Renaming

  -- Lifting of renamings to substitutions, and of variables to expressions

  lift : ∀ {γ δ} → (γ →ʳ δ) → (γ →ˢ δ)

  η : ∀ {γ a} (x : a ∈ γ) → Arg γ a

  lift 𝟘 = 𝟘
  lift [ x ] = [ η x ]
  lift (ρ₁ ⧺ ρ₂) = lift ρ₁ ⧺ lift ρ₂

  η x = var-left x ` lift (tabulate var-right)

  lift-map-η : ∀ {γ δ} (ρ : γ →ʳ δ) → lift ρ ≡ map η ρ
  lift-map-η 𝟘 = refl
  lift-map-η [ x ] = refl
  lift-map-η (ρ₁ ⧺ ρ₂) = cong₂ _⧺_ (lift-map-η ρ₁) (lift-map-η ρ₂)

  lift-𝟙ʳ : ∀ {γ} → lift 𝟙ʳ ≡ tabulate (η {γ = γ})
  lift-𝟙ʳ = trans (lift-map-η 𝟙ʳ) map-tabulate

  -- Identity substitution

  𝟙ˢ : ∀ {γ} → γ →ˢ γ
  𝟙ˢ = lift 𝟙ʳ

  -- Substitution extension

  ⇑ˢ : ∀ {γ δ θ} → γ →ˢ δ → γ ⧺ θ →ˢ δ ⧺ θ
  ⇑ˢ {θ = θ} f =  map [ ⇑ʳ (tabulate var-left) ]ʳ_ f ⧺ lift (tabulate var-right)

  -- The interaction of lifting with various operations

  lift-∙ : ∀ {γ δ} (ρ : γ →ʳ δ) {a} (x : a ∈ γ) →
           lift ρ ∙ x ≡ η (ρ ∙ x)
  lift-∙ [ _ ] var-here = refl
  lift-∙ (ρ₁ ⧺ ρ₂) (var-left x) = lift-∙ ρ₁ x
  lift-∙ (ρ₁ ⧺ ρ₂) (var-right y) = lift-∙ ρ₂ y

  𝟙ˢ-∙ : ∀ {γ a} {x : a ∈ γ} → 𝟙ˢ ∙ x ≡ η x
  𝟙ˢ-∙ {x = x} = trans (lift-∙ 𝟙ʳ x) (cong η 𝟙ʳ-≡)

  𝟙ˢ-tabulate-η : ∀ {γ} → 𝟙ˢ {γ = γ} ≡ tabulate η
  𝟙ˢ-tabulate-η = shape-≡ (λ x → trans 𝟙ˢ-∙ (sym (tabulate-∙ η)))

  lift-tabulate : ∀ {γ δ} (f : ∀ {α} → α ∈ γ → α ∈ δ) {a} (x : a ∈ γ) →
                  lift (tabulate f) ∙ x ≡ η (f x)
  lift-tabulate f var-here = refl
  lift-tabulate f (var-left x) = lift-tabulate (λ z → f (var-left z)) x
  lift-tabulate f (var-right y) = lift-tabulate (λ z → f (var-right z)) y

  ∘ʳ-lift : ∀ {γ δ θ} (ρ : γ →ʳ δ) (τ : δ →ʳ θ) {a} (x : a ∈ γ) →
             lift (τ ∘ʳ ρ) ∙ x ≡  lift τ ∙ (ρ ∙ x)
  ∘ʳ-lift [ x ] τ var-here = sym (lift-∙ τ x)
  ∘ʳ-lift (ρ₁ ⧺ ρ₂) τ (var-left x) = ∘ʳ-lift ρ₁ τ x
  ∘ʳ-lift (ρ₁ ⧺ ρ₂) τ (var-right y) = ∘ʳ-lift ρ₂ τ y

  []ʳ-lift : ∀ {γ δ θ} (ρ : γ →ʳ δ) (τ : δ →ʳ θ) {a} (x : a ∈ γ) → [ ⇑ʳ τ ]ʳ (lift ρ ∙ x) ≡  lift (τ ∘ʳ ρ) ∙ x
  []ʳ-η : ∀ {γ δ} (ρ : γ →ʳ δ) {a} (x : a ∈ γ) → [ ⇑ʳ ρ ]ʳ η x ≡ η (ρ ∙ x)

  []ʳ-lift [ x ] τ var-here = []ʳ-η τ x
  []ʳ-lift (ρ₁ ⧺ ρ₂) τ (var-left x) = []ʳ-lift ρ₁ τ x
  []ʳ-lift (ρ₁ ⧺ ρ₂) τ (var-right x) = []ʳ-lift ρ₂ τ x

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
  ʳ∘ˢ-lift (ρ₁ ⧺ ρ₂) τ (var-left x) = ʳ∘ˢ-lift ρ₁ τ x
  ʳ∘ˢ-lift (ρ₁ ⧺ ρ₂) τ (var-right x) = ʳ∘ˢ-lift ρ₂ τ x

  lift-map : ∀ {γ δ θ} (f : ∀ {α} → α ∈ γ → α ∈ δ) (ρ : θ →ʳ γ) →
             lift (map f ρ) ≡ map [ ⇑ʳ (tabulate f) ]ʳ_ (lift ρ)
  lift-map f 𝟘 = refl
  lift-map f [ x ] = cong [_] (trans (cong η (sym (tabulate-∙ f))) (sym ([]ʳ-η (tabulate f) x)))
  lift-map f (ρ₁ ⧺ ρ₂) = cong₂ _⧺_ (lift-map f ρ₁) (lift-map f ρ₂)

  ⇑ˢ-lift : ∀ {γ δ θ} (ρ : γ →ʳ δ) → ⇑ˢ {θ = θ} (lift ρ) ≡ lift (⇑ʳ ρ)
  ⇑ˢ-lift ρ = cong₂ _⧺_ (sym (lift-map var-left ρ)) refl

  lift-⧺ : ∀ {γ δ θ} (ρ : γ →ʳ θ) (τ : δ →ʳ θ) →
           lift (ρ ⧺ τ) ≡ lift ρ ⧺ lift τ
  lift-⧺ ρ τ = refl

  -- Auxiliary substitution function
  -- {-# TERMINATING #-}
  -- sbs : ∀ {γ δ θ} (ρ : γ →ʳ θ) (f : δ →ˢ θ) → Expr (γ ⧺ δ) → Expr θ
  -- sbs ρ f (var-left x ` ts) = ρ ∙ x `` λ z → sbs (in-left ∘ʳ ρ) (⇑ˢ f) ([ assoc-right ]ʳ ts ∙ z)
  -- sbs ρ f (var-right x ` ts) = sbs 𝟙ʳ (tabulate (λ z → sbs (in-left ∘ʳ ρ) (⇑ˢ f) ([ assoc-right ]ʳ ts ∙ z))) (f ∙ x)

  data Focus : Set where
    focus-here : Focus
    focus-left : Focus → Shape → Focus
    focus-right : Shape → Focus → Focus

  focus-shape : Shape → Focus → Shape
  focus-shape θ focus-here = θ
  focus-shape θ (focus-left f γ) = focus-shape θ f ⧺ γ
  focus-shape θ (focus-right γ f) = γ ⧺ focus-shape θ f

  infixr 6 [_]ˢ_
  infixl 6 _∘ˢ_
  _∘ˢ_ : ∀ {γ δ θ} (g : δ →ˢ θ) (f : γ →ˢ δ) → γ →ˢ θ
  [_]ˢ_ : ∀ {γ δ} (f : γ →ˢ δ) → Expr γ → Expr δ

  sbs : ∀ (foc : Focus) {γ δ} (g : γ →ˢ δ) → Expr (focus-shape γ foc) → Expr (focus-shape δ foc)
  sbs focus-here g e =  [ g ]ˢ e
  sbs (focus-left foc γ) g x = {!!}
  sbs (focus-right x foc) g e = {!!}


  -- The action of substitution

  -- [ f ]ˢ (x ` ts) = sbs (f ∘ˢ ts) (f ∙ x)

  -- -- Composition of substitutions
  -- g ∘ˢ f = tabulate λ x → [ ⇑ˢ g ]ˢ f ∙ x

  -- -- Basic properties of substitution
  -- ∘ˢ-∙ : ∀ {γ δ θ} (g : δ →ˢ θ) (f : γ →ˢ δ) {α} (x : α ∈ γ) →
  --        (g ∘ˢ f) ∙ x ≡ [ ⇑ˢ g ]ˢ (f ∙ x)
  -- ∘ˢ-∙ g f x = tabulate-∙ (λ x → [ ⇑ˢ g ]ˢ f ∙ x)

  -- [∘]ˢ : ∀ {γ δ θ} (g : δ →ˢ θ) (f : γ →ˢ δ) {cl} (e : Expr γ cl) →
  --        [ g ∘ˢ f ]ˢ e ≡ [ g ]ˢ [ f ]ˢ e
  -- [∘]ˢ f g (x ` ts) = {!!}

  -- sbs-lift : ∀ {γ δ θ} (ρ : γ →ʳ θ) (τ : δ →ʳ θ) (e : Expr (γ ⧺ δ)) →
  --             sbs ρ (lift τ) e ≡ [ ρ ⧺ τ ]ʳ e
  -- sbs-lift ρ τ (var-left x ` ts) =
  --   ≡-`
  --     refl
  --     (λ z → trans
  --              (tabulate-∙ (λ z → sbs (in-left ∘ʳ ρ) (⇑ˢ (lift τ)) ([ assoc-right ]ʳ ts ∙ z)))
  --              (trans
  --                 {!!}
  --                 (sym (ʳ∘ˢ-∙ {ρ = ρ ⧺ τ} {ts = ts} {x = z}))))
  -- sbs-lift ρ τ (var-right x ` ts) =
  --   trans
  --     (cong (sbs 𝟙ʳ _) (lift-∙ τ x))
  --     (≡-` 𝟙ʳ-≡ λ z → {!!})

  -- [lift]ˢ : ∀ {γ δ} (ρ : γ →ʳ δ) (e : Expr γ) → [ lift ρ ]ˢ e ≡ [ ρ ]ʳ e
  -- [lift]ˢ ρ (x ` ts) = {!!}

  -- -- lift-∘ˢ : ∀ {γ δ θ} (ρ : δ →ʳ θ) (f : γ →ˢ δ) → lift ρ ∘ˢ f ≡ ρ ʳ∘ˢ f
  -- -- lift-∘ˢ {γ = γ} ρ f = shape-≡ λ x → E x
  -- --   where
  -- --     open ≡-Reasoning
  -- --     E : ∀ {α} (x : α ∈ γ) → (lift ρ ∘ˢ f) ∙ x ≡ (ρ ʳ∘ˢ f) ∙ x
  -- --     E x =
  -- --       begin
  -- --         (lift ρ ∘ˢ f) ∙ x
  -- --           ≡⟨ ∘ˢ-∙ (lift ρ) f x ⟩
  -- --         [ ⇑ˢ (lift ρ) ]ˢ f ∙ x
  -- --           ≡⟨ cong ([_]ˢ f ∙ x) (⇑ˢ-lift ρ) ⟩
  -- --         [ lift (⇑ʳ ρ) ]ˢ f ∙ x
  -- --           ≡⟨ [lift]ˢ (⇑ʳ ρ) (f ∙ x) ⟩
  -- --         [ ⇑ʳ ρ ]ʳ f ∙ x
  -- --           ≡⟨ sym (ʳ∘ˢ-∙ {ρ = ρ} {ts = f} {x = x})⟩
  -- --         (ρ ʳ∘ˢ f) ∙ x
  -- --       ∎


  -- -- [𝟙]ˢ : ∀ {γ cl} {e : Expr γ cl} → [ 𝟙ˢ ]ˢ e ≡ e
  -- -- [𝟙]ˢ {e = x ` ts} = trans (cong [ 𝟙ˢ ⧺ (𝟙ˢ ∘ˢ ts) ]ˢ_ 𝟙ˢ-∙) {!!}
