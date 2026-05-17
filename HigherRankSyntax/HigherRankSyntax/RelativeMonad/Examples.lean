
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Lean.Level
import Mathlib.CategoryTheory.Monad.Basic

import HigherRankSyntax.RelativeMonad.Basic

open CategoryTheory

section
  universe u₁ u₂ v₁ v₂

  variable {A : Type u₁} [Category.{v₁} A]
  variable {E : Type u₂} [Category.{v₂} E]
  variable (J : A ⥤ E)


/- This one might be the idenitity Klesili triple (as a relative monad), precomposed with J,
   altough that may not be the optiomal way to define it. -/
def RelativeMonad.Id : RelativeMonad J :=
  { map := J.obj
    η := fun X => 𝟙 (J.obj X)
    lift := id
    unit_right := fun _ => rfl
    unit_left := by aesop_cat
    comp_lift := by aesop_cat }

def RelativeMonad.precompose.{u₃, v₃} {B : Type u₃} [Category.{v₃} B] (G : B ⥤ A) (T : RelativeMonad J) :
  RelativeMonad (G ⋙ J) :=
  { map := fun X => T.map (G.obj X)
    η := fun X => T.η (G.obj X)
    lift := T.lift
    unit_right := by
      intro X
      apply T.unit_right
    unit_left := by
      intro X Y f
      apply T.unit_left

    comp_lift := by
      simp
      intro X Y Z f g
      apply T.comp_lift
  }
end
