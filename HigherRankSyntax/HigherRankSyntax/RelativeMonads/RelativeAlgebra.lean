import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Lean.Level
import Mathlib.CategoryTheory.Monad.Basic
import HigherRankSyntax.RelativeMonads.RelativeMonad

open CategoryTheory

section
universe u₁ u₂ v₁ v₂

  variable {A : Type u₁} [Category.{v₁} A]
  variable {E : Type u₂} [Category.{v₂} E]
  variable {J : A ⥤ E}
  variable (T : RelativeMonad J)

  structure RelativeAlgebra where
    carr : E
    χ : ∀ {Z : A},
      (J.obj Z ⟶ carr) → (T.map Z ⟶ carr)
    unit_law : ∀ {Z : A} (f : J.obj Z ⟶ carr),
      f = (T.η Z)≫ (χ f)
    bind_law : ∀ {Z W: A}
      (k : J.obj Z ⟶ T.map W)
      (f : J.obj W ⟶ carr),
      (T.lift k) ≫ (χ f) = χ (k ≫ (χ f))
end

section
universe u₁ u₂ v₁ v₂

  variable {A : Type u₁} [Category.{v₁} A]
  variable {E : Type u₂} [Category.{v₂} E]
  variable {J : A ⥤ E}
  variable {T : RelativeMonad J}
  variable (X X' : RelativeAlgebra T)

  structure RelAlgebraHom where
    carr_map : X.carr ⟶ X'.carr
    struct_comm : ∀ {Z : A} (f : J.obj Z ⟶ X.carr),
      (X.χ f) ≫ carr_map  = X'.χ (f ≫ carr_map)
end

/- Add proofs that :
  - χ is natural
  - We can define an identity map for relative algebras
  - We can define composition for these maps
  - We can form a category with these algebras and morphisms

-/
