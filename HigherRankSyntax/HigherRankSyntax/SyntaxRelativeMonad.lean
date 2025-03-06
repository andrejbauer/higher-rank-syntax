import Lean.Level
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Mathlib.CategoryTheory.Monad.Basic

import HigherRankSyntax.RelativeMonads.RelativeMonad
import HigherRankSyntax.Renaming
import HigherRankSyntax.Syntax
import HigherRankSyntax.Substitution

def ArityCat := ShapeCat

open CategoryTheory

structure VarRen (γ δ : Shape) : Type where
  arity : Arity
  var : Var arity γ
  ren : arity →ʳ δ

/-- The object part of the variables functor -/
def 𝕁ₒ (γ : Shape) : Arity ⥤ Type 0 where
  obj := VarRen γ
  map := fun ρ xσ => { arity := xσ.arity, var := xσ.var, ren := ρ ∘ʳ xσ.ren }

/-- The variables functor -/
def 𝕁 : Shape ⥤ (Arity ⥤ Type 0) where
  obj := 𝕁ₒ
  map := fun {γ γ'} ρ =>
    { app := fun δ xσ => { arity := xσ.arity, var := ρ xσ.var, ren := xσ.ren } }

/-- The object part of the expression functor -/
def 𝕋ₒ (γ : Shape) : Arity ⥤ Type 0 where

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

  obj := 𝕋

  map := fun {γ γ'} f =>
    { app := fun _ => Renaming.actFree f
      naturality := by
        intros δ δ' g
        funext e
        simp [𝕋ₒ]
        apply Renaming.actFree_actBound
    }

  map_id := by
    intro γ
    simp [𝕋ₒ]
    congr
    funext δ e
    apply Renaming.actFree.map_id

  map_comp := by
    intro γ₁ γ₂ γ₃ f g
    simp [𝕋ₒ]
    congr
    funext δ e
    apply Renaming.actFree.map_comp


/-- The main goal is to define the relative monad for syntax.
    This should be in the same file as the first part of this file.  -/
def SyntaxRelativeMonad : RelativeMonad 𝕁 := {
  map := 𝕋ₒ
  η := sorry
  lift := sorry
  unit_left := sorry
  unit_right := sorry
  comp_lift := sorry
}
