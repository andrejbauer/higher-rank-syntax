import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Types.Basic
import HigherRankSyntax.RelativeMonad.Module
import HigherRankSyntax.SyntaxMonad

/-!
# Arity-shaped syntax modules

Fix a relative monad `T` whose objects are the raw arities of a carrier `C`.
A `T`-module is a functor from `Kl(T)` to `Type`: its elements can be
reindexed by the substitutions represented by Kleisli arrows.  The constant
arity functor sends every Kleisli object to the type of all raw arities and
acts trivially on substitutions.

`ArityMod T` is the slice of `T`-modules over this constant functor.  An object
is therefore a module together with a substitution-invariant shape map, sending
each element to a raw arity.

This file supplies only module action and shape.  Their dependent sequencing is
the tensor in `ArityModuleTensor`.
-/

open CategoryTheory

variable {A : Type} {C : Carrier A}
variable {T : RelativeMonad (J C)}

/-- The constant raw-arity functor on a relative Kleisli category. -/
def arityConst (T : RelativeMonad (J C)) : RelativeMonad.Kleisli T ⥤ Type where
  obj _ := C.Arity
  map _ := ↾fun (Φ : C.Arity) => Φ
  map_id _ := by ext Φ; rfl
  map_comp _ _ := by ext Φ; rfl

/-- `T`-modules equipped with a substitution-invariant raw arity. -/
abbrev ArityMod (T : RelativeMonad (J C)) := CategoryTheory.Over (arityConst T)

namespace ArityMod

/-- The underlying relative-monad module. -/
abbrev module (M : ArityMod T) : RelativeMonad.Kleisli T ⥤ Type := M.left

/-- The raw shape carried by an element of an arity-shaped module. -/
def shape (M : ArityMod T) {Ω : C.Arity} :
    module M |>.obj Ω → C.Arity :=
  M.hom.app Ω

/-- Substitution preserves raw shape. -/
theorem shape_natural (M : ArityMod T) {Ω Ξ : C.Arity}
    (σ : RelativeMonad.Kleisli.of T Ω ⟶ RelativeMonad.Kleisli.of T Ξ)
    (x : module M |>.obj (RelativeMonad.Kleisli.of T Ω)) :
    shape M (module M |>.map σ x) = shape M x := by
  change M.hom.app _ (M.left.map σ x) = M.hom.app _ x
  exact NatTrans.naturality_apply M.hom σ x

/-- A morphism of arity modules preserves shape. -/
theorem hom_shape {M N : ArityMod T} (f : M ⟶ N)
    {Ω : C.Arity} (x : module M |>.obj Ω) :
    shape N (f.left.app Ω x) = shape M x := by
  change N.hom.app Ω (f.left.app Ω x) = M.hom.app Ω x
  have h := congrArg (fun q => q.app Ω x) f.w
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using h

end ArityMod
