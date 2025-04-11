import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
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


  /-- This version uses isomorphisms already defined in
 Mathlib.CategoryTheory.Iso so it may be more practical
 to work with this one. -/

  -- def IsoLeftFunctor : Aᵒᵖ × C ⥤ Type v₂ := L.op.prod (𝟭 C) ⋙ Functor.hom C
  -- def IsoRightFunctor : Aᵒᵖ × C ⥤ Type v₂  := J.op.prod R ⋙ Functor.hom E

  def RelativeAdjunction :=
    L.op.prod (𝟭 C) ⋙ Functor.hom C
     ≅ J.op.prod R ⋙ Functor.hom E
  -- infixl:15 " ⊣ʳ " => RelativeAdjunction

  structure RelativeAdjunction_alt where
    /- Natural transformation α : () ⟶ ()-/
    α : (L.op.prod (𝟭 _) ⋙ .hom C) ⟶ (J.op.prod R ⋙ .hom E)
    /- Inverse(candidate) α⁻ : () ⟶ ()-/
    β : (J.op.prod R ⋙ .hom E) ⟶ (L.op.prod (𝟭 _) ⋙ .hom C)
    /- Proof that β is left inverse to α -/
    βα_inverse : α ≫ β = 𝟙 _
    /- Proof that β is right inverse to α -/
    αβ_inverse : β ≫ α = 𝟙 _


-- Possible progress:
  -- 1. every adjunction gives a relative adjunction
  -- 2. every relative adjunction gives a relative monad (Theorem 2.10)
  -- 3. every relative monad gives a Kleisli relative adjunction (paragraph 3 of section 2.3)
  --    (first requires the definition of the Kleisli category of a relative monad)
  -- 4. every relative monad gives an EM relative adjunction (paragraph after Definition 2.11)
  --    (first requires the definition of the Elienberg-Moore category of a relative monad)

end

section FromAdjunctionToRelativeAdjunction

  universe v v₂ u₁ u₂

  variable {C : Type u₁} [Category.{v} C]
  variable {D : Type u₂} [Category.{v} D]

  variable (F : C ⥤ D)
  variable (G : D ⥤ C)
  variable (adj : F ⊣ G)

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


  def Adjunction.toRelativeAdjunction :
    RelativeAdjunction (𝟭 C) F G where
      hom := homNatTrans F G adj
      inv := invNatTrans F G adj
      hom_inv_id := by aesop_cat
      inv_hom_id := by aesop_cat


/- I may remove the following piece of code later,
  if I choose to continue with the "_alt" version
  of relative adjunctions. -/

  /- def Adjunction.toRelativeAdjunction_alt  :
    RelativeAdjunction_alt (𝟭 C) F G where
      α := sorry
      β := sorry
      βα_inverse := sorry
      αβ_inverse := sorry -/

end FromAdjunctionToRelativeAdjunction

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
    --  by
    --   have id_LX := 𝟙 (L.obj X)
    --   have Φ_LX := (Φ.hom.app ((op X) , L.obj X))
    --   simp at Φ_LX
    --   exact (Φ_LX id_LX)
    lift {X Y} f := (R.map ((Φ.inv.app (op X, L.obj Y)) f))
    -- by
    --   simp
    --   have Φinv_XLY := (Φ.inv.app (op X, L.obj Y))
    --   exact (R.map (Φinv_XLY f))

    /- Laws -/
    unit_left := sorry
    unit_right := sorry
    comp_lift := sorry


end FromRelativeAdjunctionToRelativeMonad
