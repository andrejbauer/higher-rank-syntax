import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Lean.Level
import Mathlib.CategoryTheory.Monad.Basic
import HigherRankSyntax.RelativeMonads.RelativeMonad

open CategoryTheory


section
universe u₁ u₂ v₁ v₂ u v
  variable {A : Type u₁} [Category.{v₁} A]
  variable {E : Type u₂} [Category.{v₂} E]
  variable {J : A ⥤ E}
  variable (T : RelativeMonad J)

-- This attempt currently does not work (level issues ?)
  instance RelativeKleisliCategory : Category A where
    Hom {X Y} :=  (J.obj X) ⟶ (T.map Y)
    id X := (T.η X)
    comp {X Y Z} f g := f ≫ (T.lift g)
    id_comp {X Y} f := by simp ; rw[<-(T.unit_left f)]
    comp_id {X Y} f := by
       simp
       have prp := (Category.comp_id f)
       -- this is a bit messy, i should clean it
       rw[<-prp, Category.assoc, whisker_eq]
       rw[T.unit_right Y]
       simp
    assoc {X Y Z W} f g h := by
      simp
      -- If I don't add the levels of the category, the following line works,
      -- but not the definition as a whole.
      rw[T.comp_lift]
end
