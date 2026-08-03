import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Types.Basic
import HigherRankSyntax.Typing.BaseExtension

/-!
# Arity-shaped syntax modules

`ArityMod C` is the slice of raw syntax modules over the constant functor of
raw arities.  Its objects are modules equipped with a substitution-invariant
raw shape.
-/

open CategoryTheory

variable {A : Type} {C : Carrier A}

/-- The constant raw-arity functor on the syntax Kleisli category. -/
def arityConst (C : Carrier A) : SyntaxKleisli C ⥤ Type where
  obj _ := C.Arity
  map _ := ↾fun (Φ : C.Arity) => Φ
  map_id _ := by ext Φ; rfl
  map_comp _ _ := by ext Φ; rfl

/-- Syntax modules equipped with a substitution-invariant raw arity. -/
abbrev ArityMod (C : Carrier A) :=
  CategoryTheory.Over (arityConst C)

namespace ArityMod

/-- The underlying raw syntax module. -/
abbrev module (M : ArityMod C) : SyntaxKleisli C ⥤ Type := M.left

/-- The raw shape carried by an element of an arity-shaped module. -/
def shape (M : ArityMod C) {Ω : C.Arity} :
    module M |>.obj Ω → C.Arity :=
  M.hom.app Ω

/-- Substitution preserves raw shape. -/
theorem shape_natural (M : ArityMod C) {Ω Ξ : C.Arity}
    (σ : RelativeMonad.Kleisli.of (SyntaxMonad C) Ω ⟶
      RelativeMonad.Kleisli.of (SyntaxMonad C) Ξ)
    (x : module M |>.obj (RelativeMonad.Kleisli.of (SyntaxMonad C) Ω)) :
    shape M (module M |>.map σ x) = shape M x := by
  change M.hom.app _ (M.left.map σ x) = M.hom.app _ x
  exact NatTrans.naturality_apply M.hom σ x

/-- A morphism of arity modules preserves shape. -/
theorem hom_shape {M N : ArityMod C} (f : M ⟶ N)
    {Ω : C.Arity} (x : module M |>.obj Ω) :
    shape N (f.left.app Ω x) = shape M x := by
  change N.hom.app Ω (f.left.app Ω x) = M.hom.app Ω x
  have h := congrArg (fun q => q.app Ω x) f.w
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using h

end ArityMod
