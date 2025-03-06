
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

  /-- The idenity Kleisli triple on `C` -/
  def KleisliTriple.id : KleisliTriple C := sorry

  /-- From every monad we get a Kleisly triple -/
  def KleisliTriple.fromMonad (T : Monad C) : KleisliTriple C := sorry

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
