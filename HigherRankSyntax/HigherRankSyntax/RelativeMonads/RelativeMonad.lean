import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Lean.Level
import Mathlib.CategoryTheory.Monad.Basic

open CategoryTheory


/- General definitions pertaining to relative monads. This should
   probably be the main part of this file, and the stuff above
   pertaining to syntax should go elsewhere. -/



section
  universe u₁ u₂ v₁ v₂

  variable {A : Type u₁} [Category.{v₁} A]
  variable {E : Type u₂} [Category.{v₂} E]
  variable (J : A ⥤ E)

  structure RelativeMonad where
    map : A → E
    η (X) : J.obj X ⟶ map X
    lift {X Y} (f : (J.obj X) ⟶ (map Y)) :
      (map X) ⟶ (map Y)
    unit_right : ∀ (X : A), lift (η X) = 𝟙 (map X)
    unit_left : forall {X Y : A} (f : (J.obj X) ⟶ (map Y)),
      f =  η X ≫ lift f
    comp_lift : forall {X Y Z : A}
      (f : (J.obj X) ⟶ (map Y))
      (g : (J.obj Y) ⟶ (map Z)),
      lift (f ≫ (lift g)) = (lift f) ≫ (lift g)
end

section
  universe u₁ u₂ v₁ v₂
  variable {A : Type u₁} [Category.{v₁} A]
  variable {E : Type u₂} [Category.{v₂} E]
  variable (J : A ⥤ E)
  variable (T T' : RelativeMonad J)

/-- Tentative definition for relative monad morphisms
  (where both monads have the same root J)-/
  structure RelMonHom where
    map_hom {X : A} : (T.map X) ⟶ (T'.map X)
    hom_unit {X : A} : (T.η X) ≫ map_hom = (T'.η X)
    hom_lift {X Y} : ∀ (f : (J.obj X)  ⟶ (T.map Y)),
      (T.lift f) ≫ map_hom = map_hom (X := X) ≫ (T'.lift (f ≫ map_hom))
end

/- I sould add proofs that :
  - T can be equiupped with a functor structure
  - η and lift are then natural transformations
-/
