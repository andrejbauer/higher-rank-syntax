open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Relation.Binary
open import Induction.WellFounded

{-

   A formalization of (raw) syntax with higher-order binders.

   We define a notion of syntax which allows for higher-order binders, variables and substitutions. Ordinary notions of
   variables are special cases:

   * order 1: ordinary variables and substitutions, for example those of λ-calculus
   * order 2: meta-variables and their instantiations
   * order 3: symbols (term formers) in dependent type theory, such as Π, Σ, W, and syntactic transformations between theories

   The syntax is parameterized by a type Class of syntactic classes. For example, in dependent type theory there might
   be two syntactic classes, ty and tm, corresponding to type and term expressions.

-}


module Syntax (Class : Set) where

  infixl 6 _⊕_

  {- Shapes are a kind of variable contexts. They assign to each variable its syntactic arity, which is a syntactic
     class and a binding shape. We model shapes as binary trees so that it is easy to concatenate two of them. A more
     traditional approach models shapes as lists, in which case one has to append lists. -}

  data Shape : Set where
    𝟘 : Shape -- the empty shape
    [_,_] : ∀ (Γ : Shape) (A : Class) → Shape -- the shape with precisely one variable
    _⊕_ : ∀ (Γ : Shape) (Δ : Shape) → Shape -- disjoint sum of shapes

  infix 5 [_,_]∈_

  {- The de Bruijn indices are binary numbers because shapes are binary trees.
     [ Δ , A ]∈ Γ is the set of variable indices in Γ whose arity is (A , Δ). -}
  data [_,_]∈_ : Shape → Class → Shape → Set where
    var-here : ∀ {Ξ} {A} → [ Ξ , A ]∈  [ Ξ , A ]
    var-left :  ∀ {Ξ} {A} {Γ} {Δ} → [ Ξ , A ]∈ Γ → [ Ξ , A ]∈ Γ ⊕ Δ
    var-right : ∀ {Ξ} {A} {Γ} {Δ} → [ Ξ , A ]∈ Δ → [ Ξ , A ]∈ Γ ⊕ Δ

  {- Examples:

  postulate ty : Class -- type class
  postulate tm : Class -- term class

  ordinary-variable-arity : Class → Shape
  ordinary-variable-arity c = [ 𝟘 , c ]

  binary-type-metavariable-arity : Shape
  binary-type-metavariable-arity = [ [ 𝟘 , tm ] ⊕ [ 𝟘 , tm ] , ty ]

  Π-arity : Shape
  Π-arity = [ [ 𝟘 , ty ] ⊕ [ [ 𝟘 , tm ] , ty ] , ty ]

  [ Π-arity , ty ]∈ ([ 𝟘 , tm ] ⊕ [ 𝟘 , ty ])

  -}

  {- Because everything is a variable, even symbols, there is a single expression constructor
     x ` ts which forms and expression by applying the variable x to arguments ts. -}

  infix 9 _`_

  data Expr : Shape → Class → Set

  Arg : Shape → Shape → Class → Set
  Arg Γ Ξ A = Expr (Γ ⊕ Ξ) A

  -- Expressions

  data Expr where
    _`_ : ∀ {Γ} {Δ} {A} (x : [ Δ , A ]∈ Γ) →
            (ts : ∀ {Ξ} {B} (y : [ Ξ , B ]∈ Δ) → Arg Γ Ξ B) → Expr Γ A

  -- We define renamings and substitutions here so that they can be referred to.
  -- In particular, notice that the ts above is just a substituition

  -- renaming
  infix 5 _→ʳ_

  _→ʳ_ : Shape → Shape → Set
  Γ →ʳ Δ = ∀ {Ξ} {A} (x : [ Ξ , A ]∈ Γ) → [ Ξ , A ]∈ Δ

  -- substitution
  infix 5 _→ˢ_

  _→ˢ_ : Shape → Shape → Set
  Γ →ˢ Δ = ∀ {Θ} {A} (x : [ Θ , A ]∈ Γ) → Arg Δ Θ A

  -- A recursion principle for shapes which needs to be explained to Agda
  module _ where

    open Induction.WellFounded

    infix 4 _≺_

    -- A well-founded relation on shapes
    data _≺_ (Θ : Shape) (Γ : Shape) : Set where
      ≺-∈ : ∀ {B} → [ Θ , B ]∈ Γ → Θ ≺ Γ

    wf-≺ : WellFounded _≺_
    wf-≺ 𝟘 = acc (λ { _ (≺-∈ ())})
    wf-≺ [ Γ , A ] = acc (λ { Θ (≺-∈ var-here) → wf-≺ Γ})
    wf-≺ (Γ₁ ⊕ Γ₂) = acc (λ { Θ (≺-∈ (var-left x)) → acc-inverse (wf-≺ Γ₁) Θ (≺-∈ x)
                            ; Θ (≺-∈ (var-right y)) → acc-inverse (wf-≺ Γ₂) Θ (≺-∈ y)})
    open All wf-≺ lzero

    module _
      (P : ∀ {Γ Θ A} (x : [ Θ , A ]∈ Γ) → Set)
      (r : ∀ {Γ Θ A} (x : [ Θ , A ]∈ Γ) → (∀ {Ξ B} (y : [ Ξ , B ]∈ Θ) → P y) → P x) where

      -- Curried version of P
      private Q : Shape → Set
      Q Γ = ∀ {Θ A} (x : [ Θ , A ]∈ Γ) → P x

      -- Recursor suitable for Q derived from the recursor r
      private q : ∀ (Γ : Shape) (ε : WfRec _≺_ Q Γ) → Q Γ
      q Γ ε {Θ} {A} x = r x (λ y → ε Θ (≺-∈ x) y)

      -- The main recursion-forming operator
      rec-∈ : ∀ {Γ Θ A} (x : [ Θ , A ]∈ Γ) → P x
      rec-∈ {Γ = Γ} = wfRec Q q Γ

      -- We show that rec-∈ satisfies the desired fixpoint equation
      -- with respect to any relation that is preserved by the recursor r
      module _
           (_∼_ : ∀ {Γ Θ A} {x : [ Θ , A ]∈ Γ} → P x → P x → Set)
           (r-ext : ∀ {Γ Θ A} (x : [ Θ , A ]∈ Γ) {f g : Q Θ} →
                    (∀ {Ξ B} (y : [ Ξ , B ]∈ Θ) → f y ∼ g y) → r x f ∼ r x g) where

        _∼'_ : ∀ {Γ} (u v : ∀ {Ξ B} (x : [ Ξ , B ]∈ Γ) → P x) → Set
        _∼'_ {Γ} u v = ∀ {Ξ B} (x : [ Ξ , B ]∈ Γ) → u x ∼ v x

        q-ext : ∀ Γ {δ ε : WfRec _≺_ Q Γ} → (∀ {Δ} Δ≺Γ {Ξ B} (x : [ Ξ , B ]∈ Δ) → δ Δ Δ≺Γ x ∼ ε Δ Δ≺Γ x) →
                  ∀ {Θ A} (x : [ Θ , A ]∈ Γ) → q Γ δ x ∼ q Γ ε x
        q-ext Γ δ∼ε x = r-ext x (δ∼ε (≺-∈ x))

        open import FixPointRel wf-≺ _ Q q _∼'_ q-ext

        -- The fixpoint equation for rec-∈
        unfold-rec-∈ : ∀ {Γ Θ A} {x : [ Θ , A ]∈ Γ} → rec-∈ x ∼ r x rec-∈
        unfold-rec-∈ {x = x} = unfold-wfRec x

  -- The size of a term
  module _ where
    open import Data.Nat
    open import Data.Nat.Properties

    size : ∀ {Γ A} → Expr Γ A → ℕ

    shape-sum : ∀ {Γ} → (∀ {Ξ B} → [ Ξ , B ]∈ Γ → ℕ) → ℕ
    shape-sum {𝟘} f = 0
    shape-sum {[ Γ , A ]} f = f var-here
    shape-sum {Γ ⊕ Δ} f = (shape-sum (λ x → f (var-left x))) + (shape-sum (λ y → f (var-right y)))

    shape-sum-resp-≡ : ∀ {Γ} → {f g : ∀ {Ξ B} → [ Ξ , B ]∈ Γ → ℕ} →
                       (∀ {Ξ B} (y : [ Ξ , B ]∈ Γ) → f y ≡ g y) → shape-sum f ≡ shape-sum g
    shape-sum-resp-≡ {𝟘} ξ = refl
    shape-sum-resp-≡ {[ Γ , A ]} ξ = ξ var-here
    shape-sum-resp-≡ {Γ ⊕ Δ} ξ =
      cong₂ _+_
        (shape-sum-resp-≡ (λ y → ξ (var-left y)))
        (shape-sum-resp-≡ (λ y → ξ (var-right y)))

    size (x ` ts) = suc (shape-sum (λ y → size (ts y)))

    shape-sum-≤ : ∀ {Γ} (f : ∀ {Θ A} → [ Θ , A ]∈ Γ → ℕ) {Θ A} {y : [ Θ , A ]∈ Γ} → f y ≤ shape-sum f
    shape-sum-≤ {Γ = [ Γ , A ]} _ {y = var-here} = ≤-refl
    shape-sum-≤ {Γ = Γ₁ ⊕ Γ₂} f {y = var-left y} =
      ≤-trans (shape-sum-≤ (λ x → f (var-left x))) (m≤m+n _ _)
    shape-sum-≤ {Γ = Γ₁ ⊕ Γ₂} f {y = var-right y} =
      ≤-trans (shape-sum-≤ (λ x → f (var-right x))) (m≤n+m _ _)

    -- an argument is smaller than the whole expression
    size-arg-< : ∀ {Γ Θ A} {x : [ Θ , A ]∈ Γ} {ts : Θ →ˢ Γ} {Ξ B} {y : [ Ξ , B ]∈ Θ} →
                 size (ts y) < size (x ` ts)
    size-arg-< {ts = ts} = s≤s (shape-sum-≤ λ y → size (ts y))

  -- Syntactic equality of expressions

  infix 4 _≈_

  data _≈_ : ∀ {Γ} {A} → Expr Γ A → Expr Γ A → Set where
    ≈-≡ : ∀ {Γ} {A} {t u : Expr Γ A} (ξ : t ≡ u) → t ≈ u
    ≈-` : ∀ {Γ} {Δ} {A} {x : [ Δ , A ]∈ Γ} {ts us : Δ →ˢ Γ}
            (ξ : ∀ {Ξ} {B} (y : [ Ξ , B ]∈ Δ) → ts y ≈ us y) → x ` ts ≈ x ` us

  ≈-refl : ∀ {Γ} {A} {t : Expr Γ A} → t ≈ t
  ≈-refl = ≈-≡ refl

  ≈-sym : ∀ {Γ} {A} {t u : Expr Γ A} → t ≈ u → u ≈ t
  ≈-sym (≈-≡ ξ) = ≈-≡ (sym ξ)
  ≈-sym (≈-` ξ) = ≈-` λ { y → ≈-sym (ξ y) }

  ≈-trans : ∀ {Γ} {A} {t u v : Expr Γ A} → t ≈ u → u ≈ v → t ≈ v
  ≈-trans (≈-≡ refl) ξ = ξ
  ≈-trans (≈-` ζ) (≈-≡ refl) = ≈-` ζ
  ≈-trans (≈-` ζ) (≈-` ξ) = ≈-` λ { y → ≈-trans (ζ y) (ξ y) }
