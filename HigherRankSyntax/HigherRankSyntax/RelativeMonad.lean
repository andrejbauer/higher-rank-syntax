import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Lean.Level
import Mathlib.CategoryTheory.Monad.Basic

import HigherRankSyntax.Syntax
import HigherRankSyntax.Renaming

def ArityCat := ShapeCat

open CategoryTheory

structure VarRen (γ δ : Shape) : Type where
  arity : Arity
  var : Var arity γ
  ren : arity →ʳ δ

/-- The object part of the variables functor -/
def 𝕁' (γ : Shape) : Arity ⥤ Type 0 where
  obj := VarRen γ
  map := fun ρ xσ => { arity := xσ.arity, var := xσ.var, ren := ρ ∘ʳ xσ.ren }

/-- The variables functor -/
def 𝕁 : Shape ⥤ (Arity ⥤ Type 0) where
  obj := 𝕁'
  map := fun {γ γ'} ρ =>
    { app := fun δ xσ => { arity := xσ.arity, var := ρ xσ.var, ren := xσ.ren } }

/-- The object part of the expression functor -/
def 𝕋' (γ : Shape) : Arity ⥤ Type 0 where

  obj := Expr γ

  map := fun {δ δ' f} => f.actBound

  map_id := by
    intro δ
    funext e
    apply Renaming.actBound.map_id

  map_comp := by
    intro δ₁ δ₂ δ₃ f g
    funext e
    simp
    apply Renaming.actBound.map_comp

/-- The expressions functor -/
def 𝕋 : Shape ⥤ (Arity ⥤ Type 0) where

  obj := 𝕋'

  map := fun {γ γ'} f =>
    { app := fun _ => Renaming.actFree f
      naturality := by
        intros δ δ' g
        funext e
        simp [𝕋']
        apply Renaming.actFree_actBound
    }

  map_id := by
    intro γ
    simp [𝕋']
    congr
    funext δ e
    apply Renaming.actFree.map_id

  map_comp := by
    intro γ₁ γ₂ γ₃ f g
    simp [𝕋']
    congr
    funext δ e
    apply Renaming.actFree.map_comp


/- General definitions pertaining to relative monads. This should
   probably be the main part of this file, and the stuff above
   pertaining to syntax should go elsewhere. -/

/- Actually, Kleisli triples should also be in their own file. -/
section
  universe u v

  variable (C : Type u) [Category.{v} C]

  structure KleisliTriple where
    map : C → C
    η : ∀ X, X ⟶ map X
    lift {X Y} (f : X ⟶ map Y) : map X ⟶ map Y
    /- missing fields: unit_rihgt, unit_left, comp_lift -/

  /-- The idenity Kleisli triple on `C` -/
  def KleisliTriple.id : KleisliTriple C := sorry

  /-- From every monad we get a Kleisly triple -/
  def KleisliTriple.fromMonad (T : Monad C) : KleisliTriple C := sorry

end

section
  universe u₁ u₂ v₁ v₂

  variable {A : Type u₁} [Category.{v₁} A]
  variable {E : Type u₂} [Category.{v₂} E]
  variable (J : A ⥤ E)

  structure RelativeMonad where
    map : A → E
    η (X) : J.obj X ⟶ map X
    lift {X Y} (f : (J.obj X) ⟶ (map Y)) :
      (map X) ⟶ (map Y)
    unit_right : ∀ (X : A), lift (η X) = 𝟙 (map X)
    unit_left : forall {X Y : A} (f : (J.obj X) ⟶ (map Y)),
      f =  η X ≫ lift f
    comp_lift : forall (X Y Z : A)
      (f : (J.obj X) ⟶ (map Y))
      (g : (J.obj Y) ⟶ (map Z)),
      lift (f ≫ (lift g)) = (lift f) ≫ (lift g)

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

section FromKlesiliTripleToRelativeMonad

  universe v u

  variable {C : Type u} [Category.{v} C]
  variable (T : KleisliTriple C)

  /- It is probably better to first define Kleisli triples and then
     to show how to go from a CategoryTheory.Monad to a Kleisli triple,
     and from a Kleisli triple to a relative monad. -/

  def KleisliTriple.toRelativeMonad : RelativeMonad (𝟭 C) :=
  { map := T.map
    η := T.η
    lift := sorry
    unit_left := sorry
    unit_right := sorry
    comp_lift := sorry
  }

end FromKlesiliTripleToRelativeMonad

/-- The main goal is to define the relative monad for syntax.
    This should be in the same file as the first part of this file.  -/
def SyntaxRelativeMonad : RelativeMonad 𝕁 := {
  map := 𝕋'
  η := sorry
  lift := sorry
  unit_left := sorry
  unit_right := sorry
  comp_lift := sorry
}
