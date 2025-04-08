import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Lean.Level
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Types
import HigherRankSyntax.RelativeMonads.RelativeMonad

open CategoryTheory
open Opposite

section
universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂

  variable {A : Type u₁} [Category.{v₁} A]
  variable {E : Type u₂} [Category.{v₂} E]
  variable {J : A ⥤ E}
  variable {C : Type u₃} [Category.{v₃} C]

  variable (L : A ⥤ C)
  variable (R : C ⥤ E)

/- The following definition of a relative adjunction
  is based on the paper "Monads need not be endofunctors"
  (Altenkirch, Chapman & Uustalu). -/

  def LeftHomFun : Aᵒᵖ × C ⥤ Type v₃ where
    obj p :=   ((L.obj (unop p.1)) ⟶ (p.2))
    map := by
      intros x y f h
      /- have g := f.1.unop ≫ h ≫ f.2 -/

  def RightHomFun : Aᵒᵖ × C ⥤ Type w₂ :=
  sorry

  structure RelativeAdjunction (L : A ⥤ D) (R : D ⥤ C) where
    /- Natural transformation α : () ⟶ ()-/
    α : LeftHomFun ⟶ RightHomFun
    /- Inverse(candidate) α⁻ : () ⟶ ()-/
    α⁻ : RightHomFun ⟶  LeftHomFunHomFun
    /- Proof that α⁻ is left inverse to α -/
    /- Proof that α⁻ is right inverse to α -/

  /-infixl:15 " ⊣ʳ " => RelativeAdjunction-/

end
