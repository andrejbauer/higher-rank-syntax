open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Relation.Unary hiding (_∈_)
open import Relation.Binary
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)

{-

   A formalization of (raw) syntax with higher-rank binders.

   We define a notion of syntax which allows for higher-rank binders, variables and substitutions. Ordinary notions of
   variables are special cases:

   * rank 1: ordinary variables and substitutions, for example those of λ-calculus
   * rank 2: meta-variables and their instantiations
   * rank 3: symbols (term formers) in dependent type theory, such as Π, Σ, W, and syntactic transformations between theories

   The syntax is parameterized by a type Class of syntactic classes. For example, in dependent type theory there might
   be two syntactic classes, ty and tm, corresponding to type and term expressions. In the futre we would prefer to
   generalize the situation to any number of proof-relevant and proof-irrelevant judgements.

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

  -- -- Examples:

  -- postulate ty : Class -- type class
  -- postulate tm : Class -- term class

  -- ordinary-variable-arity : Class → Shape
  -- ordinary-variable-arity c = [ 𝟘 , c ]

  -- binary-type-metavariable-arity : Shape
  -- binary-type-metavariable-arity = [ [ 𝟘 , tm ] ⊕ [ 𝟘 , tm ] , ty ]

  -- Π-arity : Shape
  -- Π-arity = [ [ 𝟘 , ty ] ⊕ [ [ 𝟘 , tm ] , ty ] , ty ]

  infix 5 _∈_

  {- The de Bruijn indices are binary numbers because shapes are binary trees.
     α ∈ γ is the set of variable indices in γ whose arity is α. -}
  data _∈_ : Arity → Shape → Set where
    var-here : ∀ {α} → α ∈ [ α ]
    var-left :  ∀ {α} {γ} {δ} → α ∈ γ → α ∈ γ ⊕ δ
    var-right : ∀ {α} {γ} {δ} → α ∈ δ → α ∈ γ ⊕ δ

  -- In several cases we want a map defined on the positions of a shape.
  -- Defining such maps directly is difficult because the relevant recursion
  -- principle is not structural. Instead we use a method suggested by
  -- Guillaume Allais (http://gallais.github.io), which amounts to
  -- working with proof-relevant evidence that the function is defined.

  -- The definition of All, tabulate, lookup and map is taken from
  -- https://github.com/gallais/potpourri/blob/349d2f282a100ea5d82a548455b040939b04e67e/agda/poc/Syntax.agda

  -- A “predicate” witnessing that P is inhabited at all positions
  -- of a shape.
  data All (P : Arity → Set) : Shape → Set where
    𝟘 : All P 𝟘
    [_] : ∀ {α} → P α → All P [ α ]
    _⊕_ : ∀ {γ δ} → All P γ → All P δ → All P (γ ⊕ δ)

  -- Given a map on positions of a shape, we can produce evidence
  -- that it is defined at all positions.
  tabulate : ∀ {γ P} → (∀ {α} → α ∈ γ → P α) → All P γ
  tabulate {𝟘} f = 𝟘
  tabulate {[ δ , cl ]} f = [ f var-here ]
  tabulate {δ ⊕ δ₁} f = tabulate (f ∘ var-left) ⊕ tabulate (f ∘ var-right)

  -- Extensionally equal maps give the same tabulations
  tabulate-ext : ∀ {P : Arity → Set} {γ} {f g : ∀ {α} → α ∈ γ → P α} →
                 (∀ {α} {x : α ∈ γ} → f x ≡ g x) → tabulate f ≡ tabulate g
  tabulate-ext {γ = 𝟘} ξ = refl
  tabulate-ext {γ = [ x ]} ξ = cong [_] ξ
  tabulate-ext {γ = γ ⊕ δ} ξ = cong₂ _⊕_ (tabulate-ext ξ) (tabulate-ext ξ)

  -- Given evidence that a map is defined at all positions of a shape,
  -- we can lookup one of its values.
  infixl 12 _∙_
  _∙_ : ∀ {γ P} → All P γ → (∀ {α} → α ∈ γ → P α)
  [ p ] ∙ var-here = p
  (ps ⊕ _) ∙ (var-left x) = ps ∙ x
  (_ ⊕ qs) ∙ (var-right y) = qs ∙ y

  -- Tabulation stores values correctly
  tabulate-∙ : ∀ {P : Arity → Set} {γ} (f : (∀ {α} → α ∈ γ → P α)) {α} {x : α ∈ γ} → (tabulate f) ∙ x ≡ f x
  tabulate-∙ f {x = var-here} = refl
  tabulate-∙ f {x = var-left x} = tabulate-∙ (f ∘ var-left)
  tabulate-∙ f {x = var-right y} = tabulate-∙ (f ∘ var-right)

  cong-∙ : ∀ {γ P} {f g : All P γ} {α} {x y : α ∈ γ} → f ≡ g → x ≡ y → f ∙ x ≡ g ∙ y
  cong-∙ refl refl = refl

  map : ∀ {γ P Q} → (∀ {α} → P α → Q α) → All P γ → All Q γ
  map f 𝟘 = 𝟘
  map f [ x ] = [ f x ]
  map f (ps ⊕ qs) = map f ps ⊕ map f qs

  shape-≡ : ∀ {γ P} {ps qs : All P γ} → (∀ {α} (x : α ∈ γ) → ps ∙ x ≡ qs ∙ x)
            → ps ≡ qs
  shape-≡ {ps = 𝟘} {qs = 𝟘} ξ = refl
  shape-≡ {ps = [ x ]} {qs = [ y ]} ξ = cong [_] (ξ var-here)
  shape-≡ {ps = ps₁ ⊕ ps₂} {qs = qs₁ ⊕ qs₂} ξ =
    cong₂ _⊕_ (shape-≡ (ξ ∘ var-left)) (shape-≡ (ξ ∘ var-right))

  -- The interaction of map and tabulate
  map-tabulate : ∀ {P Q : Arity → Set} {γ} {g : ∀ {α} → P α → Q α} → {f : (∀ {α} → α ∈ γ → P α)} →
                 map g (tabulate f) ≡ tabulate (g ∘ f)
  map-tabulate {γ = 𝟘} = refl
  map-tabulate {γ = [ _ ]} = refl
  map-tabulate {γ = _ ⊕ _} = cong₂ _⊕_ map-tabulate map-tabulate

  -- the interaction of map and ∙
  map-∙ : ∀ {γ P} {Q : Arity → Set} → {f : ∀ {α} → P α → Q α} {ps : All P γ} {α : Arity} {x : α ∈ γ} → map f ps ∙ x  ≡ f (ps ∙ x)
  map-∙ {ps = [ _ ]} {x = var-here} = refl
  map-∙ {ps = ps₁ ⊕ ps₂} {x = var-left x} = map-∙ {ps = ps₁}
  map-∙ {ps = ps₁ ⊕ ps₂} {x = var-right x} = map-∙ {ps = ps₂}

  {- Because everything is a variable, even symbols, there is a single expression constructor
     x ` ts which forms and expression by applying the variable x to arguments ts. -}

  infix 9 _`_

  data Expr : Shape → Class → Set

  Arg : Shape → Arity → Set
  Arg γ (δ , cl) = Expr (γ ⊕ δ) cl

  -- We define renamings and substitutions here so that they can be referred to.

  -- Renaming
  infix 5 _→ʳ_

  _→ʳ_ : Shape → Shape → Set
  γ →ʳ δ = All (_∈ δ) γ

  -- Substitution
  infix 5 _→ˢ_

  _→ˢ_ : Shape → Shape → Set
  γ →ˢ δ = All (Arg δ) γ

  -- Expressions

  data Expr where
    _`_ : ∀ {γ δ} {cl} (x : (δ , cl) ∈ γ) → (ts : δ →ˢ γ) → Expr γ cl

  -- Syntactic equality of expressions

  ≡-` : ∀ {α} {γ} {x y : (γ , class α) ∈ arg α} {ts us : γ →ˢ arg α} →
          x ≡ y → (∀ {αᶻ} (z : αᶻ ∈ γ) → ts ∙ z ≡ us ∙ z) → x ` ts ≡ y ` us
  ≡-` ζ ξ = cong₂ (_`_) ζ (shape-≡ ξ)
