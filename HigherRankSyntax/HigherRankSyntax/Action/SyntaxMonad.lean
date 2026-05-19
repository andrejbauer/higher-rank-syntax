import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import HigherRankSyntax.Action.Expr
import HigherRankSyntax.Action.Subst
import HigherRankSyntax.Action.Equations
import HigherRankSyntax.RelativeMonad.Basic

/-!
# Categorical scaffolding for the syntax monad

The categorical setting on which the syntax-monad structure of `Expr` sits.

* Source category `Shape C`: morphisms are renamings.
* Target category `ArityType C := C.Arity → Type`: α-pointwise functions; `C.Arity` is
  treated as a discrete base.
* `J : Shape C ⥤ ArityType C` — the variables-of-arity-α functor.
* `T : Shape C ⥤ ArityType C` — the expressions-under-one-α-binder functor.

The relative-monad structure (unit `η`, Kleisli extension, and laws) sits on top of this
scaffolding.  The two unit laws are proved; the Kleisli composition law remains.
-/

namespace Action

open CategoryTheory

/-- The category of shapes and renamings. -/
instance ShapeCat {C : Carrier} : Category (Shape C) where
  Hom := Renaming
  id := Renaming.id
  comp := Renaming.comp
  id_comp _ := Renaming.id_comp _
  comp_id _ := Renaming.comp_id _
  assoc _ _ _ := Renaming.comp_assoc _ _ _

/-- The target category: families `C.Arity → Type` with α-pointwise morphisms. -/
abbrev ArityType (C : Carrier) : Type 1 := C.Arity → Type

instance ArityTypeCat {C : Carrier} : Category (ArityType C) where
  Hom F G := ∀ α : C.Arity, F α → G α
  id _ := fun _ x => x
  comp f g := fun α x => g α (f α x)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Variables functor: `Γ ↦ (α ↦ Expr.J Γ α)`. -/
def J {C : Carrier} : Shape C ⥤ ArityType C where
  obj Γ := fun α => Expr.J Γ α
  map ρ := fun _ v => Expr.J.map ρ v
  map_id _ := by funext _ _; rfl
  map_comp _ _ := by funext _ _; rfl

/-- Expressions functor: `Γ ↦ (α ↦ Expr.T Γ α)`. -/
def T {C : Carrier} : Shape C ⥤ ArityType C where
  obj Γ := fun α => Expr.T Γ α
  map ρ := fun α e => Expr.T.map ρ α e
  map_id _ := by funext α e; exact Expr.T.map_id α e
  map_comp _ _ := by funext α e; exact Expr.T.map_comp _ _ α e

/-- The syntax relative monad: `T` is the free relative monad on `J`.  Map, unit,
Kleisli extension, and the two unit laws are filled in; `comp_lift` remains. -/
def SyntaxMonad {C : Carrier} : RelativeMonad (@J C) where
  map        := T.obj
  η          := fun _ _ v => Expr.η v
  lift       := fun {_ _} f _ e => Subst.lift (fun s => f s.arity ⟨s, rfl⟩) e
  unit_right := by
    intro Γ
    funext α e
    exact unit_right α e
  unit_left  := by
    intro Γ Δ f
    funext α v
    exact unit_left f v
  comp_lift  := by
    intro X Y Z f g
    funext α e
    exact comp_lift (fun s => f s.arity ⟨s, rfl⟩) (fun s => g s.arity ⟨s, rfl⟩) e

end Action
