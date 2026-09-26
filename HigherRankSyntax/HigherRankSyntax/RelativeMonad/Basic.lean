import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Relative monads

A *relative monad* over a functor `J : A ⥤ E` consists of:

* an object map `map : A → E`;
* a unit `η X : J.obj X ⟶ map X` for each `X : A`;
* a Kleisli extension, sending each `f : J.obj X ⟶ map Y` to
  `lift f : map X ⟶ map Y`;

satisfying the laws `unit_right`, `unit_left` and `comp_lift`.
-/

universe u₁ u₂ v₁ v₂

open CategoryTheory

/-- A relative monad over a functor `J : A ⥤ E`. -/
structure RelativeMonad {A : Type u₁} [Category.{v₁} A]
    {E : Type u₂} [Category.{v₂} E]
    (J : A ⥤ E) where
  /-- Underlying object map. -/
  map : A → E
  /-- Unit of the relative monad. -/
  η (X : A) : J.obj X ⟶ map X
  /-- Kleisli extension. -/
  lift {X Y : A} (f : J.obj X ⟶ map Y) : map X ⟶ map Y
  /-- Right unit law: lifting the unit is the identity. -/
  unit_right : ∀ (X : A), lift (η X) = 𝟙 (map X)
  /-- Left unit law: `f` is `η X` followed by `lift f`. -/
  unit_left : ∀ {X Y : A} (f : J.obj X ⟶ map Y), f = η X ≫ lift f
  /-- Associativity law: the extension of `f ≫ lift g` is `lift f ≫ lift g`. -/
  comp_lift : ∀ {X Y Z : A}
      (f : J.obj X ⟶ map Y) (g : J.obj Y ⟶ map Z),
    lift (f ≫ lift g) = lift f ≫ lift g

/-- A morphism of relative monads over `J : A ⥤ E`: a family of morphisms
`T.map X ⟶ T'.map X` commuting with `η` and `lift`. -/
structure RelativeMonad.Hom {A : Type u₁} [Category.{v₁} A]
    {E : Type u₂} [Category.{v₂} E]
    {J : A ⥤ E} (T T' : RelativeMonad J) where
  /-- The component at `X`. -/
  map_hom {X : A} : T.map X ⟶ T'.map X
  /-- `T.η X` followed by the component is `T'.η X`. -/
  hom_unit {X : A} : T.η X ≫ map_hom = T'.η X
  /-- `T.lift f` followed by the component is the component followed by
  `T'.lift (f ≫ map_hom)`. -/
  hom_lift {X Y : A} : ∀ (f : J.obj X ⟶ T.map Y),
    T.lift f ≫ map_hom = map_hom (X := X) ≫ T'.lift (f ≫ map_hom)
