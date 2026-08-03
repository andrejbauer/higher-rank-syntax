import Mathlib.CategoryTheory.Functor.Category
import HigherRankSyntax.RelativeMonad.Kleisli

/-!
# Modules over relative monads

A left module over a relative monad `T`, with values in a category `D`, is a
functor from the Kleisli category of `T` to `D`.
-/

universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory

namespace RelativeMonad

variable {A : Type u₁} [Category.{v₁} A]
  {E : Type u₂} [Category.{v₂} E]
  {J : A ⥤ E}

/-- A left module over a relative monad is a functor from its Kleisli category. -/
abbrev LeftModule (T : RelativeMonad J)
    (D : Type u₃) [Category.{v₃} D] :=
  Kleisli T ⥤ D

namespace LeftModule

variable {D : Type u₃} [Category.{v₃} D]
  {T : RelativeMonad J}

/-- The action of a module on a relative Kleisli morphism. -/
abbrev act (M : LeftModule T D) {X Y : A}
    (f : J.obj X ⟶ T.map Y) :
    M.obj (Kleisli.of T X) ⟶ M.obj (Kleisli.of T Y) :=
  M.map f

@[simp]
theorem act_η (M : LeftModule T D) (X : A) :
    act M (T.η X) = 𝟙 (M.obj (Kleisli.of T X)) := by
  apply M.map_id

@[simp]
theorem act_comp (M : LeftModule T D)
    {X Y Z : A} (f : J.obj X ⟶ T.map Y) (g : J.obj Y ⟶ T.map Z) :
    act M (f ≫ T.lift g) = act M f ≫ act M g := by
  apply M.map_comp

/-- A morphism of relative-monad modules is a natural transformation. -/
abbrev Hom (M N : LeftModule T D) := M ⟶ N

end LeftModule

end RelativeMonad
