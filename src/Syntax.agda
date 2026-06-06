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

   This version has a single notion of syntactic entity. A generalization would have an additional parameter
   specifying a set of type classes.

-}


module Syntax where

  infixl 5 _++_

  {- Shapes are a kind of variable contexts. They assign to each variable its syntactic arity, which is a binding shape.
     We model shapes as binary trees so that it is easy to concatenate two of them. A more traditional approach models
     shapes as lists, in which case one has to append lists. -}

  -- We refer to a Shape when we have in mind an entity that describes available variables,
  -- and to an Arity when we think of the description of the arguments that a variable/symbol accepts.
  -- Formally, they are the same thing, though.

  data Shape : Set

  Arity : Set
  Arity = Shape

  arg : Arity → Shape
  arg γ = γ

  data Shape where
    𝟘 : Shape -- the empty shape
    [_] : Arity → Shape -- the shape with precisely one variable
    _++_ : ∀ (γ : Shape) (δ : Shape) → Shape -- disjoint sum of shapes

  -- -- Examples:

  ordinary-variable-arity : Shape
  ordinary-variable-arity = 𝟘

  binary-type-metavariable-arity : Shape
  binary-type-metavariable-arity = [ [ 𝟘 ] ++ [ 𝟘 ] ]

  Π-arity : Shape
  Π-arity = [ [ 𝟘 ] ++ [ [ 𝟘 ] ] ]

  infix 3 _∈_

  {- The de Bruijn indices are binary numbers because shapes are binary trees.
     α ∈ γ is the set of variable indices in γ whose arity is α. -}
  data _∈_ : Arity → Shape → Set where
    var-here : ∀ {α} → α ∈ [ α ]
    var-left :  ∀ {α} {γ} {δ} → α ∈ γ → α ∈ γ ++ δ
    var-right : ∀ {α} {γ} {δ} → α ∈ δ → α ∈ γ ++ δ

  -- In several cases we want a map defined on the positions of a shape.
  -- Defining such maps directly is difficult because the relevant recursion
  -- principle is not structural. Instead we use a method suggested by
  -- Guillaume Allais (http://gallais.github.io), which amounts to
  -- working with proof-relevant evidence that the function is defined.

  -- The definition of All, tabulate, lookup and map is taken from
  -- https://github.com/gallais/potpourri/blob/349d2f282a100ea5d82a548455b040939b04e67e/agda/poc/Syntax.agda

  -- A shape has positions, as detailed by _∈_ above. Often we want a map
  -- that for each positions  α ∈ γ returns an element of P α, where P
  -- is a type family indexed by arities. Such a map has the type
  -- ∀ γ {α} → α ∈ γ → P α. However, it is often easier to work
  -- with an equivalent representation of such a map, one that closely
  -- follows the structure of shapes.
  --
  -- The following definition accomplishes the idea. Given a type family
  -- P : Arity → Set and a shape γ, an element of Map P γ represents a
  -- map taking each α ∈ γ to an element of P α.
  data ShapeMap (P : Arity → Set) : Shape → Set where
    𝟘 : ShapeMap P 𝟘
    [_] : ∀ {α} → P α → ShapeMap P [ α ]
    _++_ : ∀ {γ δ} → ShapeMap P γ → ShapeMap P δ → ShapeMap P (γ ++ δ)

  -- Given a map on positions of a shape, we can produce the corresponding ShapeMap
  tabulate : ∀ {γ P} → (∀ {α} → α ∈ γ → P α) → ShapeMap P γ
  tabulate {𝟘} f = 𝟘
  tabulate {[ _ ]} f = [ f var-here ]
  tabulate {_ ++ _} f = tabulate (f ∘ var-left) ++ tabulate (f ∘ var-right)

  -- Extensionally equal maps give the same ShapeMap's
  tabulate-ext : ∀ {P : Arity → Set} {γ} {f g : ∀ {α} → α ∈ γ → P α} →
                 (∀ {α} {x : α ∈ γ} → f x ≡ g x) → tabulate f ≡ tabulate g
  tabulate-ext {γ = 𝟘} ξ = refl
  tabulate-ext {γ = [ x ]} ξ = cong [_] ξ
  tabulate-ext {γ = γ ++ δ} ξ = cong₂ _++_ (tabulate-ext ξ) (tabulate-ext ξ)

  -- In reverse direction, we can convert a ShapeMap to the map it represents
  infixl 12 _∙_
  _∙_ : ∀ {γ P} → ShapeMap P γ → (∀ {α} → α ∈ γ → P α)
  [ p ] ∙ var-here = p
  (ps ++ _) ∙ (var-left x) = ps ∙ x
  (_ ++ qs) ∙ (var-right y) = qs ∙ y

  -- Tabulation stores values correctly
  tabulate-∙ : ∀ {P : Arity → Set} {γ} (f : (∀ {α} → α ∈ γ → P α)) {α} {x : α ∈ γ} → (tabulate f) ∙ x ≡ f x
  tabulate-∙ f {x = var-here} = refl
  tabulate-∙ f {x = var-left x} = tabulate-∙ (f ∘ var-left)
  tabulate-∙ f {x = var-right y} = tabulate-∙ (f ∘ var-right)

  -- The operation _∙_ preserves equality (every operation does, but we will need this
  -- specific fact later).
  cong-∙ : ∀ {γ P} {f g : ShapeMap P γ} {α} {x y : α ∈ γ} → f ≡ g → x ≡ y → f ∙ x ≡ g ∙ y
  cong-∙ refl refl = refl

  -- Map the values stored in a ShapeMap
  map : ∀ {γ P Q} → (∀ {α} → P α → Q α) → ShapeMap P γ → ShapeMap Q γ
  map f 𝟘 = 𝟘
  map f [ x ] = [ f x ]
  map f (ps ++ qs) = map f ps ++ map f qs

  -- Mapping g ∘ f is the same as mapping f followed by mapping g
  map-map : ∀ {γ} {P Q R : Arity → Set} (f : ∀ {α} → P α → Q α) (g : ∀ {α} → Q α → R α) {p : ShapeMap P γ} →
              map (g ∘ f) p ≡ map g (map f p)
  map-map f g {p = 𝟘} = refl
  map-map f g {p = [ x ]} = refl
  map-map f g {p = p₁ ++ p₂} = cong₂ _++_ (map-map f g) (map-map f g)

  -- If two ShapeMaps store the same values then they are equal
  shape-≡ : ∀ {γ P} {ps qs : ShapeMap P γ} → (∀ {α} (x : α ∈ γ) → ps ∙ x ≡ qs ∙ x)
            → ps ≡ qs
  shape-≡ {ps = 𝟘} {qs = 𝟘} ξ = refl
  shape-≡ {ps = [ x ]} {qs = [ y ]} ξ = cong [_] (ξ var-here)
  shape-≡ {ps = ps₁ ++ ps₂} {qs = qs₁ ++ qs₂} ξ =
    cong₂ _++_ (shape-≡ (ξ ∘ var-left)) (shape-≡ (ξ ∘ var-right))

  -- The interaction of map and tabulate
  map-tabulate : ∀ {P Q : Arity → Set} {γ} {g : ∀ {α} → P α → Q α} → {f : (∀ {α} → α ∈ γ → P α)} →
                 map g (tabulate f) ≡ tabulate (g ∘ f)
  map-tabulate {γ = 𝟘} = refl
  map-tabulate {γ = [ _ ]} = refl
  map-tabulate {γ = _ ++ _} = cong₂ _++_ map-tabulate map-tabulate

  -- the interaction of map and ∙
  map-∙ : ∀ {γ P} {Q : Arity → Set} → {f : ∀ {α} → P α → Q α} {ps : ShapeMap P γ} {α : Arity} {x : α ∈ γ} → map f ps ∙ x  ≡ f (ps ∙ x)
  map-∙ {ps = [ _ ]} {x = var-here} = refl
  map-∙ {ps = ps₁ ++ ps₂} {x = var-left x} = map-∙ {ps = ps₁}
  map-∙ {ps = ps₁ ++ ps₂} {x = var-right x} = map-∙ {ps = ps₂}

  {- We now proceed with the definition of expressions. Because everything is a variable, even symbols, there is a
     single expression constructor x ` ts which forms and expression by applying the variable x to arguments ts. -}

  -- The expressions over a given shape
  data Expr : Shape → Set

  -- Auxiliary definition, think of Arg γ δ as the set of expressions that may refer to free
  -- variables in γ and bound variables in δ. The name arises because Arg γ δ is also the
  -- set of possible arguments of a variable of arity δ in shape γ.
  Arg : Shape → Arity → Set
  Arg γ δ = Expr (γ ++ δ)

  -- We define renamings and substitutions here so that they can be referred to.

  -- Renaming
  infix 4 _→ʳ_

  -- A renaming from γ to δ  maps every position in γ to a position in δ, while preserving
  -- the arity.
  _→ʳ_ : Shape → Shape → Set
  γ →ʳ δ = ShapeMap (_∈ δ) γ

  -- A substitution from γ to δ maps every position in γ of arity α to an expression
  -- with free variables δ and bound variables α
  infix 4 _→ˢ_
  _→ˢ_ : Shape → Shape → Set
  γ →ˢ δ = ShapeMap (Arg δ) γ

  -- Expressions
  infix 9 _`_
  data Expr where
    _`_ : ∀ {γ δ} (x : δ ∈ γ) → (ts : δ →ˢ γ) → Expr γ

  -- A common idiom
  infix 9 _``_

  _``_ : ∀ {γ δ} (x : δ ∈ γ) → (ts : ∀ {a} (z : a ∈ δ) → Arg γ a) → Expr γ
  x `` ts = x ` tabulate ts

  -- Syntactic equality of expressions
  ≡-` : ∀ {α} {γ} {x y : γ ∈ arg α} {ts us : γ →ˢ arg α} →
          x ≡ y → (∀ {αᶻ} (z : αᶻ ∈ γ) → ts ∙ z ≡ us ∙ z) → x ` ts ≡ y ` us
  ≡-` ζ ξ = cong₂ (_`_) ζ (shape-≡ ξ)
