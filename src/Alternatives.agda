-- Old attempts at convincing Agda that substituition terminates.

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


module Alternatives (Class : Set) where

  open Syntax Class
  open Renaming Class

  -- Lifting of renamings to substitutions, and of variables to expressions

  lift : ∀ {γ δ} → (γ →ʳ δ) → (γ →ˢ δ)

  η : ∀ {γ a} (x : a ∈ γ) → Arg γ a

  lift 𝟘 = 𝟘
  lift [ x ] = [ η x ]
  lift (ρ₁ ++ ρ₂) = lift ρ₁ ++ lift ρ₂

  η x = var-left x ` lift (tabulate var-right)

  -- Ideally we would like the following to be the definition of lift,
  -- but Agda termination gets in the way

  lift-map-η : ∀ {γ δ} (ρ : γ →ʳ δ) → lift ρ ≡ map η ρ
  lift-map-η 𝟘 = refl
  lift-map-η [ x ] = refl
  lift-map-η (ρ₁ ++ ρ₂) = cong₂ _++_ (lift-map-η ρ₁) (lift-map-η ρ₂)

  lift-𝟙ʳ : ∀ {γ} → lift 𝟙ʳ ≡ tabulate (η {γ = γ})
  lift-𝟙ʳ = trans (lift-map-η 𝟙ʳ) map-tabulate

  -- Identity substitution

  𝟙ˢ : ∀ {γ} → γ →ˢ γ
  𝟙ˢ = lift 𝟙ʳ

  -- Substitution extension

  ⇑ˢ : ∀ {γ δ θ} → γ →ˢ δ → γ ++ θ →ˢ δ ++ θ
  ⇑ˢ {θ = θ} f =  map [ ⇑ʳ (tabulate var-left) ]ʳ_ f ++ lift (tabulate var-right)

  -- The interaction of lifting with various operations

  lift-∙ : ∀ {γ δ} (ρ : γ →ʳ δ) {a} (x : a ∈ γ) →
           lift ρ ∙ x ≡ η (ρ ∙ x)
  lift-∙ [ _ ] var-here = refl
  lift-∙ (ρ₁ ++ ρ₂) (var-left x) = lift-∙ ρ₁ x
  lift-∙ (ρ₁ ++ ρ₂) (var-right y) = lift-∙ ρ₂ y

  𝟙ˢ-∙ : ∀ {γ a} {x : a ∈ γ} → 𝟙ˢ ∙ x ≡ η x
  𝟙ˢ-∙ {x = x} = trans (lift-∙ 𝟙ʳ x) (cong η 𝟙ʳ-≡)

  lift-tabulate : ∀ {γ δ} (f : ∀ {α} → α ∈ γ → α ∈ δ) {a} (x : a ∈ γ) →
                  lift (tabulate f) ∙ x ≡ η (f x)
  lift-tabulate f var-here = refl
  lift-tabulate f (var-left x) = lift-tabulate (λ z → f (var-left z)) x
  lift-tabulate f (var-right y) = lift-tabulate (λ z → f (var-right z)) y

  ∘ʳ-lift : ∀ {γ δ θ} (ρ : γ →ʳ δ) (τ : δ →ʳ θ) {a} (x : a ∈ γ) →
             lift (τ ∘ʳ ρ) ∙ x ≡  lift τ ∙ (ρ ∙ x)
  ∘ʳ-lift [ x ] τ var-here = sym (lift-∙ τ x)
  ∘ʳ-lift (ρ₁ ++ ρ₂) τ (var-left x) = ∘ʳ-lift ρ₁ τ x
  ∘ʳ-lift (ρ₁ ++ ρ₂) τ (var-right y) = ∘ʳ-lift ρ₂ τ y

  []ʳ-lift : ∀ {γ δ θ} (ρ : γ →ʳ δ) (τ : δ →ʳ θ) {a} (x : a ∈ γ) → [ ⇑ʳ τ ]ʳ (lift ρ ∙ x) ≡  lift (τ ∘ʳ ρ) ∙ x
  []ʳ-η : ∀ {γ δ} (ρ : γ →ʳ δ) {a} (x : a ∈ γ) → [ ⇑ʳ ρ ]ʳ η x ≡ η (ρ ∙ x)

  []ʳ-lift [ x ] τ var-here = []ʳ-η τ x
  []ʳ-lift (ρ₁ ++ ρ₂) τ (var-left x) = []ʳ-lift ρ₁ τ x
  []ʳ-lift (ρ₁ ++ ρ₂) τ (var-right x) = []ʳ-lift ρ₂ τ x

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
  ʳ∘ˢ-lift (ρ₁ ++ ρ₂) τ (var-left x) = ʳ∘ˢ-lift ρ₁ τ x
  ʳ∘ˢ-lift (ρ₁ ++ ρ₂) τ (var-right x) = ʳ∘ˢ-lift ρ₂ τ x

  lift-map : ∀ {γ δ θ} (f : ∀ {α} → α ∈ γ → α ∈ δ) (ρ : θ →ʳ γ) →
             lift (map f ρ) ≡ map [ ⇑ʳ (tabulate f) ]ʳ_ (lift ρ)
  lift-map f 𝟘 = refl
  lift-map f [ x ] = cong [_] (trans (cong η (sym (tabulate-∙ f))) (sym ([]ʳ-η (tabulate f) x)))
  lift-map f (ρ₁ ++ ρ₂) = cong₂ _++_ (lift-map f ρ₁) (lift-map f ρ₂)

  ⇑ˢ-lift : ∀ {γ δ θ} (ρ : γ →ʳ δ) → ⇑ˢ {θ = θ} (lift ρ) ≡ lift (⇑ʳ ρ)
  ⇑ˢ-lift ρ = cong₂ _++_ (sym (lift-map var-left ρ)) refl

  shift : Shape → List Shape → Shape
  shift γ [] = γ
  shift γ (δ ∷ δs) = (shift γ δs) ++ δ

  ⟰ʳ : ∀ {γ δ Ξ} → (γ →ʳ δ) → (shift γ Ξ →ʳ shift δ Ξ)
  ⟰ʳ {Ξ = []} ρ = ρ
  ⟰ʳ {Ξ = _ ∷ _} ρ = ⇑ʳ (⟰ʳ ρ)

  ⟰ˢ : ∀ {γ δ Ξ} → (γ →ˢ δ) → (shift γ Ξ →ˢ shift δ Ξ)
  ⟰ˢ {Ξ = []} f = f
  ⟰ˢ {Ξ = _ ∷ _} f = ⇑ˢ (⟰ˢ f)

  data act-defined : ∀ {γ cl} → Expr γ cl → Set where
    act-sub : ∀ {γ δ} {cl} (x : (δ , cl) ∈ γ) → (ts : δ →ˢ γ) →
              (∀ {a} (z : a ∈ δ) → act-defined (ts ∙ z)) → act-defined (x ` ts)
    -- act-∙ : ∀ {γ δ} {cl} (f : γ →ˢ δ) (x : (δ , cl) ∈ γ) → (ts : δ →ˢ γ) →
    --           (act-defined (f ∙ x)


  module SubstitutionWithFucus where
    -- An attempt that explicitly deals with all the shifting and weakening

    infix 4 _⇒ˢ_
    data _⇒ˢ_ : Shape → Shape → Set where
      sbs : ∀ {γ δ} (f : γ →ˢ δ) → γ ⇒ˢ δ
      𝟙++ : ∀ {δ θ} (f : θ ⇒ˢ δ) → δ ++ θ ⇒ˢ δ
      rgh : ∀ {γ δ θ} (f : γ ⇒ˢ δ) → γ ++ θ ⇒ˢ δ ++ θ
      𝟙, : ∀ {γ δ θ} (f : γ ⇒ˢ θ ++ δ) → θ ++ γ ⇒ˢ θ ++ δ

    infix 7 _∙∙_
    _∙∙_ : ∀ {γ δ} (f : γ ⇒ˢ δ) {a} → a ∈ γ → Arg δ a
    sbs f ∙∙ x = f ∙ x
    𝟙++ f ∙∙ var-left x = η x
    𝟙++ f ∙∙ var-right y = f ∙∙ y
    rgh f ∙∙ var-left x = [ ⇑ʳ (tabulate var-left) ]ʳ (f ∙∙ x)
    rgh f ∙∙ var-right y = η (var-right y)
    𝟙, f ∙∙ var-left x = η (var-left x)
    𝟙, f ∙∙ var-right y = f ∙∙ y

    {-# TERMINATING #-}
    act : ∀ {γ δ cl} (f : γ ⇒ˢ δ) → Expr γ cl → Expr δ cl
    act (sbs f) (x ` ts) =  act (𝟙++ (sbs (tabulate λ z → act (rgh (sbs f)) (ts ∙ z)))) (f ∙ x)
    act (𝟙++ f) (var-left x ` ts) = x ` (tabulate λ z → act (rgh (𝟙++ f)) (ts ∙ z))
    act (𝟙++ f) (var-right y ` ts) = act (𝟙++ (sbs (tabulate λ z → act (rgh (𝟙++ f)) (ts ∙ z)))) (f ∙∙ y)
    act (rgh f) (var-left x ` ts) = act (𝟙, (sbs (tabulate (λ z → act (rgh (rgh f))  (ts ∙ z))))) (f ∙∙ x)
    act (rgh f) (var-right y ` ts) = var-right y ` tabulate λ z → act (rgh (rgh f)) (ts ∙ z)
    act (𝟙, f) (var-left x ` ts) = var-left x ` tabulate (λ z →  act (rgh (𝟙, f)) (ts ∙ z))
    act (𝟙, f) (var-right x ` ts) = act (𝟙++ (sbs (tabulate (λ z → act (rgh (𝟙, f)) (ts ∙ z))))) (f ∙∙ x)


  module IdealDefintion where
    -- The naive definition, which Agda does not see as terminating
    infix 6 [_]ˢ_
    infix 6 _∘ˢ_

    {-# TERMINATING #-}
    [_]ˢ_ : ∀ {γ δ cl} (f : γ →ˢ δ) → Expr γ cl → Expr δ cl

    {-# TERMINATING #-}
    _∘ˢ_ : ∀ {γ δ θ} (g : δ →ˢ θ) (f : γ →ˢ δ) → γ →ˢ θ

    [ f ]ˢ x ` ts = [ 𝟙ˢ ++ (f ∘ˢ ts) ]ˢ (f ∙ x)
    g ∘ˢ f = tabulate (λ x → [ ⇑ˢ g ]ˢ f ∙ x)

    [lift]ˢ : ∀ {γ δ cl} (ρ : γ →ʳ δ) (e : Expr γ cl) → [ lift ρ ]ˢ e ≡ [ ρ ]ʳ e
    [lift]ˢ ρ (x ` ts) = trans (cong [ 𝟙ˢ ++ lift ρ ∘ˢ ts ]ˢ_ (lift-∙ ρ x)) {!!}

    [𝟙]ˢ : ∀ {γ cl} {e : Expr γ cl} → [ 𝟙ˢ ]ˢ e ≡ e
    [𝟙]ˢ {e = x ` ts} = trans (cong [ 𝟙ˢ ++ (𝟙ˢ ∘ˢ ts) ]ˢ_ 𝟙ˢ-∙) {!!}




  module BoveCappreta where
    -- Instead we use the Bove-Cappreta method, whereby we define the support of [_]ˢ_ and _∘ˢ_, then we define the maps
    -- as partial maps defined on the support, and finally show that the supports are the entire domains.
    -- See doi:10.1017/S0960129505004822

    -- The action of a substitution defined at a given argument
    data defined : ∀ {γ δ cl} (f : γ →ˢ δ) (e : Expr γ cl) → Set

    -- The action of substitution
    act : ∀ {γ δ cl} (f : γ →ˢ δ) (e : Expr γ cl) → defined f e → Expr δ cl

    -- The action is defined when the recursive calls are defined
    data defined where
      df : ∀ {γ δ} {f : γ →ˢ δ} {γˣ clˣ} {x : (γˣ , clˣ) ∈ γ} {ts : γˣ →ˢ γ}
              (D : ∀ {a} (z : a ∈ γˣ) → defined (⇑ˢ f) (ts ∙ z)) →
              (E : defined (𝟙ˢ ++ tabulate (λ z → act (⇑ˢ f) (ts ∙ z) (D z))) (f ∙ x)) →
              defined f (x ` ts)

    act f (x ` ts) (df D E) = act (𝟙ˢ ++ tabulate (λ z → act (⇑ˢ f) (ts ∙ z) (D z))) (f ∙ x) E

    -- we'll do this later
    postulate total-D : ∀ {γ δ} {f : γ →ˢ δ} {γˣ clˣ} (x : (γˣ , clˣ) ∈ γ) (ts : γˣ →ˢ γ) →
                        ∀ {a} (z : a ∈ γˣ) → defined (⇑ˢ f) (ts ∙ z)

    postulate total-E : ∀ {γ δ} {f : γ →ˢ δ} {γˣ clˣ} (x : (γˣ , clˣ) ∈ γ) (ts : γˣ →ˢ γ) →
                        defined (𝟙ˢ ++ tabulate (λ {a} (z : a ∈ γˣ) → act (⇑ˢ f) (ts ∙ z)
                                        (total-D x ts z))) (f ∙ x)

    total-act : ∀ {γ δ cl} (f : γ →ˢ δ) (e : Expr γ cl) → defined f e
    total-act f (x ` ts) = df (total-D x ts) (total-E x ts)

    infix 6 [_]ˢ_
    [_]ˢ_ : ∀ {γ δ cl} (f : γ →ˢ δ) → Expr γ cl → Expr δ cl
    [ f ]ˢ e = act f e (total-act f e)

    [𝟙]ˢ : ∀ {γ cl} {e : Expr γ cl} → [ 𝟙ˢ ]ˢ e ≡ e
    [𝟙]ˢ {e = x ` ts} = {!!}

    [lift]ˢ : ∀ {γ δ cl} (ρ : γ →ʳ δ) (e : Expr γ cl) → [ lift ρ ]ˢ e ≡ [ ρ ]ʳ e
    [lift]ˢ ρ (x ` ts) = {! !}


  module AsGraph where
    -- action of substitution as a graph
    infix 4 [_]ˢ_:=_
    data [_]ˢ_:=_ : ∀ {γ δ cl} → (γ →ˢ δ) → Expr γ cl → Expr δ cl → Set where
       sbs : ∀ {γ δ} {f : γ →ˢ δ} {γˣ clˣ} {x : (γˣ , clˣ) ∈ γ} {ts : γˣ →ˢ γ} (d : γˣ →ˢ δ) {e} →
                  (∀ {a} (z : a ∈ γˣ) → [ ⇑ˢ f ]ˢ ts ∙ z := d ∙ z) →
                  [ 𝟙ˢ ++ d ]ˢ f ∙ x := e →
                  [ f ]ˢ (x ` ts) := e

    act-++-left : ∀ {γ δ θ} {f : γ →ˢ θ} {g : δ →ˢ θ} {γˣ clˣ} {x : (γˣ , clˣ) ∈ γ} {ts : γˣ →ˢ γ ++ δ} (d : γˣ →ˢ θ) e →
                 (∀ {a} (z : a ∈ γˣ) → [ ⇑ˢ (f ++ g) ]ˢ ts ∙ z  := d ∙ z) →
                 [ 𝟙ˢ ++ d ]ˢ (f ∙ x) := e →
                 [ f ++ g ]ˢ var-left x ` ts := e
    act-++-left d e r₁ r₂ = sbs d r₁ r₂

    act-⇑ˢ : ∀ {γ δ θ} {f : γ →ˢ δ} {γˣ clˣ} {ts : γˣ →ˢ γ} {x : (γˣ , clˣ) ∈ γ} {ts : γˣ →ˢ γ ++ θ} (d : γˣ →ˢ δ ++ θ) e →
            (∀ {a} (z : a ∈ γˣ) → [ ⇑ˢ (⇑ˢ f) ]ˢ ts ∙ z := d ∙ z) →
            [ 𝟙ˢ ++ d ]ˢ [ ⇑ʳ (tabulate var-left) ]ʳ f ∙ x  := e →
            [ ⇑ˢ f ]ˢ var-left x ` ts := e
    act-⇑ˢ {γ = γ} {θ = θ} {f = f} {x = x} d e r₁ r₂ =
      sbs d r₁ (subst (λ u → [ 𝟙ˢ ++ d ]ˢ u := e) (sym (map-∙ {ps = f} {x = x})) r₂)

    act-η : ∀ {γ δ} (f : γ →ˢ δ) {a} (x : a ∈ γ) → [ ⇑ˢ f ]ˢ η x := f ∙ x
    act-η f x = {!!}

    act-lift : ∀ {γ δ cl} (ρ : γ →ʳ δ) (e : Expr γ cl) →
               [ lift ρ ]ˢ e := [ ρ ]ʳ e
    act-lift ρ (x ` ts) = sbs (ρ ʳ∘ˢ ts) (λ z → {!!}) {!lift-∙!}

    infix 6 [_]ˢ_
    [_]ˢ_ : ∀ {γ δ cl} (f : γ →ˢ δ) → Expr γ cl → Expr δ cl
    [ f ]ˢ e = {!!}

    []ˢ-total : ∀ {γ δ cl} (f : γ →ˢ δ) (e : Expr γ cl) → [ f ]ˢ e := [ f ]ˢ e
    []ˢ-total f e = {!!}
