import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Relative monads

A *relative monad* over a functor `J : A ⥤ E` consists of:

* an object map `T : A → E`;
* a unit, providing a morphism `η X : J.obj X ⟶ T X` for each
  `X : A`;
* a Kleisli extension, sending each `f : J.obj X ⟶ T Y` to a
  morphism `lift f : T X ⟶ T Y`;

satisfying the three relative-monad laws (`unit_right`, `unit_left`,
`comp_lift`).
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
  /-- Left unit law: every Kleisli map factors as unit then extension. -/
  unit_left : ∀ {X Y : A} (f : J.obj X ⟶ map Y), f = η X ≫ lift f
  /-- Composition law for Kleisli extensions. -/
  comp_lift : ∀ {X Y Z : A}
      (f : J.obj X ⟶ map Y) (g : J.obj Y ⟶ map Z),
    lift (f ≫ lift g) = lift f ≫ lift g

/-- A morphism between two relative monads over the same functor
`J : A ⥤ E`: a family of `E`-morphisms commuting with `η` and
`lift`. -/
structure RelativeMonad.Hom {A : Type u₁} [Category.{v₁} A]
    {E : Type u₂} [Category.{v₂} E]
    {J : A ⥤ E} (T T' : RelativeMonad J) where
  /-- Component of the morphism at each object. -/
  map_hom {X : A} : T.map X ⟶ T'.map X
  /-- Compatibility with the unit. -/
  hom_unit {X : A} : T.η X ≫ map_hom = T'.η X
  /-- Compatibility with the Kleisli extension. -/
  hom_lift {X Y : A} : ∀ (f : J.obj X ⟶ T.map Y),
    T.lift f ≫ map_hom = map_hom (X := X) ≫ T'.lift (f ≫ map_hom)
