
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Lean.Level
import Mathlib.CategoryTheory.Monad.Basic

import HigherRankSyntax.RelativeMonads.RelativeMonad

open CategoryTheory

/- Actually, Kleisli triples should also be in their own file. -/
section
  universe u v

  variable (C : Type u) [Category.{v} C]

  structure KleisliTriple where
    map : C → C
    η : ∀ X, X ⟶ map X
    lift {X Y} (f : X ⟶ map Y) : map X ⟶ map Y
    /- missing fields: unit_rihgt, unit_left, comp_lift -/
    unit_right : ∀ (X : C), lift (η X) = 𝟙 (map X)
    unit_left : forall {X Y : C} (f : X ⟶ (map Y)),
      f =  η X ≫ lift f
    comp_lift : forall {X Y Z : C}
      (f : X ⟶ (map Y))
      (g : Y ⟶ (map Z)),
      lift (f ≫ (lift g)) = (lift f) ≫ (lift g)

    /-- The idenity Kleisli triple on `C` -/
   def KleisliTriple.id : KleisliTriple C where
      map := fun X => X
      η := fun X => 𝟙 X
      lift := fun f => f
      unit_right := fun X => rfl
      unit_left := fun f => by aesop_cat
      comp_lift := fun f g => by aesop_cat

  /-- From every monad we get a Kleisly triple -/
  def KleisliTriple.fromMonad (T : Monad C) : KleisliTriple C where
      map := T.obj
      η := fun X => T.η.app X
      lift := fun {X Y} f => (T.map f) ≫ (T.μ.app Y)
      unit_right := fun x => by simp
      unit_left := fun {X Y} f => by simp [←Category.assoc, ←T.η.naturality f, Category.assoc, T.left_unit]
      comp_lift := fun {X Y Z} f g => by
        have nat_g := T.μ.naturality g
        simp at nat_g
        simp [T.assoc, ←Category.assoc (T.map (T.map g)), nat_g]
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
    lift := T.lift
    unit_left := T.unit_left
    unit_right := T.unit_right
    comp_lift := T.comp_lift
  }

end FromKlesiliTripleToRelativeMonad
