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
  variable {C : Type u₃} [Category.{v₂} C]

  variable (L : A ⥤ C)
  variable (R : C ⥤ E)

/- The following definition of a relative adjunction
  is based on the paper "Monads need not be endofunctors"
  (Altenkirch, Chapman & Uustalu). -/

  -- def cow : Aᵒᵖ × C ⥤ Type v₂  := J.op.prod R ⋙ Functor.hom E
  -- def dog : Aᵒᵖ × C ⥤ Type v₂ := L.op.prod (𝟭 C) ⋙ Functor.hom C

  structure RelativeAdjunction where
    /- Natural transformation α : () ⟶ ()-/
    α : (L.op.prod (𝟭 _) ⋙ .hom C) ⟶ (J.op.prod R ⋙ .hom E)
    /- Inverse(candidate) α⁻ : () ⟶ ()-/
    β : (J.op.prod R ⋙ .hom E) ⟶ (L.op.prod (𝟭 _) ⋙ .hom C)
    /- Proof that β is left inverse to α -/
    βα_inverse : α ≫ β = 𝟙 _
    /- Proof that β is right inverse to α -/
    αβ_inverse : β ≫ α = 𝟙 _

  /-infixl:15 " ⊣ʳ " => RelativeAdjunction-/

  -- Possible progress:
  -- 1. every adjunction gives a relative adjunction
  -- 2. every relative adjunction gives a relative monad (Theorem 2.10)
  -- 3. every relative monad gives a Kleisli relative adjunction (paragraph 3 of section 2.3)
  --    (first requires the definition of the Kleisli category of a relative monad)
  -- 4. every relative monad gives an EM relative adjunction (paragraph after Definition 2.11)
  --    (first requires the definition of the Elienberg-Moore category of a relative monad)

end
