import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Mathlib.Tactic.ApplyFun
import Lean.Level
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Adjunction.Basic


import HigherRankSyntax.RelativeMonads.RelativeMonad

open CategoryTheory
open Opposite
open NatIso
open Adjunction

section
universe u₁ u₂ u₃ v₁ v₂

  variable {A : Type u₁} [Category.{v₁} A]
  variable {E : Type u₂} [Category.{v₂} E]
  variable (J : A ⥤ E)
  variable {C : Type u₃} [Category.{v₂} C]

  variable (L : A ⥤ C)
  variable (R : C ⥤ E)

/- The following definition of a relative adjunction
  is based on the paper "Monads need not be endofunctors"
  (Altenkirch, Chapman & Uustalu). -/


  /-- This version uses (natural) isomorphisms,
  which defined in Mathlib.CategoryTheory.NatIso. -/
  def RelativeAdjunction :=
    L.op.prod (𝟭 C) ⋙ Functor.hom C
     ≅ J.op.prod R ⋙ Functor.hom E
  -- infixl:15 " ⊣ʳ " => RelativeAdjunction


-- Possible progress:
  -- 1. every adjunction gives a relative adjunction
  -- 2. every relative adjunction gives a relative monad (Theorem 2.10)
  -- 3. every relative monad gives a Kleisli relative adjunction (paragraph 3 of section 2.3)
  --    (first requires the definition of the Kleisli category of a relative monad)
  -- 4. every relative monad gives an EM relative adjunction (paragraph after Definition 2.11)
  --    (first requires the definition of the Elienberg-Moore category of a relative monad)

end


/- From any adjunction we get a relative adjunction. -/
section FromAdjunctionToRelativeAdjunction

  universe v v₂ u₁ u₂

  variable {C : Type u₁} [Category.{v} C]
  variable {D : Type u₂} [Category.{v} D]

  variable (F : C ⥤ D)
  variable (G : D ⥤ C)
  variable (adj : F ⊣ G)

  /- We first define the two inverse natural transformations separately.-/
  @[reducible]
  def homNatTrans :
    F.op.prod (𝟭 D) ⋙ Functor.hom D
    ⟶ (𝟭 C).op.prod G ⋙ Functor.hom C where
    app f := by
      simp
      intro φ
      exact (adj.homEquiv (unop f.1) f.2) φ
    naturality f g h := by
      funext φ
      simp
      rw[homEquiv_naturality_left, homEquiv_naturality_right]

@[reducible]
  def invNatTrans :
  (𝟭 C).op.prod G ⋙ Functor.hom C
  ⟶  F.op.prod (𝟭 D) ⋙ Functor.hom D where
    app f := by
      intro φ
      exact (adj.homEquiv (unop f.1) f.2).symm φ
    naturality g f h := by
      funext φ
      simp
      rw [homEquiv_naturality_left_symm, homEquiv_naturality_right_symm]

  /- The resulting relqtive adjunction. -/
  def Adjunction.toRelativeAdjunction :
    RelativeAdjunction (𝟭 C) F G where
      hom := homNatTrans F G adj
      inv := invNatTrans F G adj
      hom_inv_id := by aesop_cat
      inv_hom_id := by aesop_cat


end FromAdjunctionToRelativeAdjunction


/- From any relative adjunction we get a relative monad. -/
section FromRelativeAdjunctionToRelativeMonad
universe u₁ u₂ u₃ v₁ v₂

  variable {A : Type u₁} [Category.{v₁} A]
  variable {E : Type u₂} [Category.{v₂} E]
  variable (J : A ⥤ E)
  variable {C : Type u₃} [Category.{v₂} C]

  variable (L : A ⥤ C)
  variable (R : C ⥤ E)


  def RelativeAdjunction.toRelativeMonad (Φ : RelativeAdjunction J L R) :
    (RelativeMonad J) where
    /- Objects -/
    map X := R.obj (L.obj X)
    η X := (((Φ.hom.app ((op X) , L.obj X))) (𝟙 (L.obj X)))
    lift {X Y} f := (R.map ((Φ.inv.app (op X, L.obj Y)) f))
    /- Laws -/
    unit_left {X Y} k := by
      have square := Φ.inv.naturality (X := (op X, L.obj X)) (Y := (op X, L.obj Y)) (𝟙 (op X), Φ.inv.app (op X, L.obj Y) k)
      have Φ_square := (reassoc_of% square) (Φ.hom.app (op X, L.obj Y))
      rw [Φ.inv_hom_id_app] at Φ_square
      have Φ_square_applied := congrFun Φ_square (Φ.hom.app (op X, L.obj X) (𝟙 L.obj X))
      simp at Φ_square_applied
      symm
      exact Φ_square_applied

    unit_right := by simp

    comp_lift {X Y Z} f g := by
      simp
      have square := Φ.inv.naturality (X := (op X, L.obj Y)) (Y := (op X, L.obj Z)) (𝟙 (op X), Φ.inv.app (_, _) g)
      have square_applied := congrFun square f
      simp at square_applied
      rw [←R.map_comp]
      congr

end FromRelativeAdjunctionToRelativeMonad
