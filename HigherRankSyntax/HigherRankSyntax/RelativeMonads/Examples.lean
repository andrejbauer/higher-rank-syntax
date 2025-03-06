
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Lean.Level
import Mathlib.CategoryTheory.Monad.Basic

import HigherRankSyntax.RelativeMonads.RelativeMonad



/- This one might be the idenitity Klesili triple (as a relative monad), precomposed with J,
   altough that may not be the optiomal way to define it. -/
def RelativeMonad.Id : RelativeMonad J :=
  { map := J.obj
    η := fun X => 𝟙 (J.obj X)
    lift := id
    unit_right := fun _ => rfl
    unit_left := by aesop_cat
    comp_lift := by aesop_cat }

def RelativeMonad.precompose.{u₃, v₃} {B : Type u₃} [Category.{v₃} B] (G : B ⥤ A) (M : RelativeMonad J) :
  RelativeMonad (G ⋙ J) :=
  { map := fun X => M.map (G.obj X)
    η := sorry
    lift := sorry
    unit_left := sorry
    unit_right := sorry
    comp_lift := sorry
  }
end
