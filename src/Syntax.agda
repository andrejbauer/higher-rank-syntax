open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Relation.Unary hiding (_∈_)
open import Relation.Binary
open import Data.Product
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

  data Shape : Set

  Arity : Set
  Arity = Shape × Class

  arg : Arity → Shape
  arg (γ  , _) = γ

  class : Arity → Class
  class (_  , cl) = cl

  data Shape where
    𝟘 : Shape -- the empty shape
    [_] : Arity → Shape -- the shape with precisely one variable
    _⊕_ : ∀ (γ : Shape) (δ : Shape) → Shape -- disjoint sum of shapes

  infix 5 _∈_

  {- The de Bruijn indices are binary numbers because shapes are binary trees.
     α ∈ γ is the set of variable indices in γ whose arity is α. -}
  data _∈_ : Arity → Shape → Set where
    var-here : ∀ {α} → α ∈ [ α ]
    var-left :  ∀ {α} {γ} {δ} → α ∈ γ → α ∈ γ ⊕ δ
    var-right : ∀ {α} {γ} {δ} → α ∈ δ → α ∈ γ ⊕ δ

  -- -- Examples:

  -- postulate ty : Class -- type class
  -- postulate tm : Class -- term class

  -- ordinary-variable-arity : Class → Shape
  -- ordinary-variable-arity c = [ 𝟘 , c ]

  -- binary-type-metavariable-arity : Shape
  -- binary-type-metavariable-arity = [ [ 𝟘 , tm ] ⊕ [ 𝟘 , tm ] , ty ]

  -- Π-arity : Shape
  -- Π-arity = [ [ 𝟘 , ty ] ⊕ [ [ 𝟘 , tm ] , ty ] , ty ]

  {- Because everything is a variable, even symbols, there is a single expression constructor
     x ` ts which forms and expression by applying the variable x to arguments ts. -}

  infix 9 _`_

  data Expr : Arity → Set

  Arg : Shape → Arity → Set
  Arg γ (δ , cl) = Expr (γ ⊕ δ , cl)

  -- substitution
  infix 5 _→ˢ_

  _→ˢ_ : Shape → Shape → Set
  γ →ˢ δ = ∀ {αˣ} (x : αˣ ∈ γ) → Arg δ αˣ

  -- Expressions

  data Expr where
    _`_ : ∀ {γ} {cl} {γˣ} (x : (γˣ , cl) ∈ γ) → (ts : γˣ →ˢ γ) → Expr (γ , cl)

  -- We define renamings and substitutions here so that they can be referred to.
  -- In particular, notice that the ts above is just a substituition

  -- renaming
  infix 5 _→ʳ_

  _→ʳ_ : Shape → Shape → Set
  γ →ʳ δ = ∀ {α} (x : α ∈ γ) → α ∈ δ

  -- Syntactic equality of expressions

  -- We require several instances of function extensionality, here is one for arguments.
  postulate argext : ∀ {γ} {δ}
                       {ts₁ ts₂ : γ →ˢ δ} →
                       (∀ {αʸ} (y : αʸ ∈ γ) → ts₁ y ≡ ts₂ y) →
                       (λ {αʸ} (y : αʸ ∈ γ) → ts₁ y) ≡ (λ y → ts₂ y)

  -- The common use of arg-extensionality
  ≡-` : ∀ {γ} {γˣ} {x : (γˣ , class γ) ∈ arg γ} {ts us : γˣ →ˢ arg γ}
          (ξ : ∀ {αʸ} (y : αʸ ∈ γˣ) → ts y ≡ us y) → x ` ts ≡ x ` us
  ≡-` ξ = cong (_`_ _) (argext (λ y → ξ y))
