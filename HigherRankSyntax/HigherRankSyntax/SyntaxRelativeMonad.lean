
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Lean.Level
import Mathlib.CategoryTheory.Monad.Basic

import HigherRankSyntax.RelativeMonads.RelativeMonad
import HigherRankSyntax.Renaming
import HigherRankSyntax.Syntax
-- import HigherRankSyntax.Substitution

def ArityCat := ShapeCat

open CategoryTheory

structure Var (γ δ : Shape) : Type where
  arity : Arity
  var : var_in arity γ
  ren : arity →ʳ δ

def var_in.toVar {γ α} (x : var_in α γ) : Var γ α where
  arity := α
  var := x
  ren := 𝟙ʳ

/-- The object part of the variables functor -/
@[reducible]
def 𝕁ₒ (γ : Shape) : Arity ⥤ Type 0 where
  obj := Var γ
  map := fun ρ xσ => { arity := xσ.arity, var := xσ.var, ren := ρ ∘ʳ xσ.ren }

/-- The variables functor -/
@[reducible]
def 𝕁 : Shape ⥤ (Arity ⥤ Type 0) where
  obj := 𝕁ₒ
  map := fun {γ γ'} ρ =>
    { app := fun δ xσ => { arity := xσ.arity, var := ρ xσ.var, ren := xσ.ren } }

/-- The object part of the expression functor -/
@[reducible]
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

  obj := 𝕋ₒ

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


def η_val (γ : Shape) :  𝕁ₒ γ ⟶ 𝕋ₒ γ where
  app δ := by
    -- unfold 𝕁ₒ ; simp
    -- unfold 𝕋ₒ ; simp
    intro x
    have temp1 β := (η_val x.arity).app β
    simp [𝕁ₒ, 𝕋ₒ] at temp1
    have ren_subterms : x.arity →ʳ γ ⊕ δ := ((γ ⇑ʳ x.ren) ∘ʳ .varRight)
    have temp2 := x.var ◃ (fun β y => ⟦ren_subterms⟧ʳ (temp1 β (var_in.toVar y)))
    exact temp2
  naturality {δ δ'} r := by
    simp
    funext x
    simp
    unfold Renaming.actBound
    simp
    funext β y
    rw [<-Renaming.actFree.map_comp]
    congr
-- prove termination

def lift_val {γ γ'} (f : 𝕁ₒ γ ⟶ 𝕋ₒ γ') :
  (𝕋ₒ γ ⟶ 𝕋ₒ γ') where
  app δ := by
    simp
    intro t
    /- first I need to define (mutually inductive)
    action of a substitution and instanciation of bound variables. -/
    sorry
  naturality := sorry


/-- The main goal is to define the relative monad for syntax.
    This should be in the same file as the first part of this file.  -/
def SyntaxRelativeMonad : RelativeMonad 𝕁 := {
  map := 𝕋ₒ
  η := η_val
  lift := lift_val
  unit_left := sorry
  unit_right := sorry
  comp_lift := sorry
}
