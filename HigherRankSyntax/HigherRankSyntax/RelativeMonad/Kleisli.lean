import HigherRankSyntax.RelativeMonad.Basic

/-!
# The Kleisli category of a relative monad

For a relative monad `T` on `J : A ⥤ E`, a Kleisli morphism from `X` to `Y`
is a morphism `J.obj X ⟶ T.map Y`.  Composition uses the relative Kleisli
extension.
-/

universe u₁ u₂ v₁ v₂

open CategoryTheory

namespace RelativeMonad

variable {A : Type u₁} [Category.{v₁} A]
  {E : Type u₂} [Category.{v₂} E]
  {J : A ⥤ E}

/-- The object type of the Kleisli category of a relative monad. -/
def Kleisli (_T : RelativeMonad J) := A

namespace Kleisli

variable (T : RelativeMonad J)

/-- Regard a base-category object as a relative Kleisli object. -/
def of (X : A) : Kleisli T := X

/-- The base-category object underlying a relative Kleisli object. -/
def toBase (X : Kleisli T) : A := X

@[simp]
theorem toBase_of (X : A) : toBase T (of T X) = X := rfl

@[simp]
theorem of_toBase (X : Kleisli T) : of T (toBase T X) = X := rfl

instance : Category.{v₂} (Kleisli T) where
  Hom X Y := J.obj (toBase T X) ⟶ T.map (toBase T Y)
  id X := T.η (toBase T X)
  comp f g := f ≫ T.lift g
  id_comp := by
    intro X Y f
    exact (T.unit_left f).symm
  comp_id := by
    intro X Y f
    rw [T.unit_right, Category.comp_id]
  assoc := by
    intro W X Y Z f g h
    rw [T.comp_lift, Category.assoc]

/-- A relative Kleisli hom is the corresponding ambient-category hom. -/
def homEquiv (X Y : A) :
    (of T X ⟶ of T Y) ≃ (J.obj X ⟶ T.map Y) :=
  Equiv.refl _

@[simp]
theorem id_eq (X : A) :
    (𝟙 (of T X) : of T X ⟶ of T X) = T.η X := rfl

@[simp]
theorem comp_eq {X Y Z : A}
    (f : J.obj X ⟶ T.map Y) (g : J.obj Y ⟶ T.map Z) :
    (homEquiv T X Z) (f ≫ g) = f ≫ T.lift g := rfl

end Kleisli

end RelativeMonad
