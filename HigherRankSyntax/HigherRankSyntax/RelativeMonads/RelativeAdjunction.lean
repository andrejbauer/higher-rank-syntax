import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Lean.Level
import Mathlib.CategoryTheory.Monad.Basic
import HigherRankSyntax.RelativeMonads.RelativeMonad

open CategoryTheory

section
universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂

  variable {A : Type u₁} [Category.{v₁} A]
  variable {C : Type u₂} [Category.{v₂} C]
  variable {J : A ⥤ C}
  variable {D : Type u₃} [Category.{v₃} D]

  variable (L : A ⥤ D)
  variable (R : D ⥤ C)

/- The following definition of a relative adjunction
  is based on the paper "Monads need not be endofunctors"
  (Altenkirch, Chapman & Uustalu). -/

  def LeftHomFun : Cᵒᵖ × A ⥤ Type w₁ :=
  sorry

  def RightHomFun : Cᵒᵖ × A ⥤ Type w₂ :=
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
