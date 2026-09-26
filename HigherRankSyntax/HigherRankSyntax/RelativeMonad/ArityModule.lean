import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Types.Basic
import HigherRankSyntax.RelativeMonad.Module
import HigherRankSyntax.SyntaxMonad

/-!
# Arity modules

Fix a relative monad `T` over `J`, so that the objects of its Kleisli category are the
arities `C.Arity`.  A `T`-module is a functor from the Kleisli category of `T` to `Type`.
The functor `arityConst T` is constant with value `C.Arity`.

`ArityMod T` is the slice of `T`-modules over `arityConst T`: a module `M` together with
a map `shape M` from its elements to arities that is invariant under the action of
Kleisli arrows.
-/

open CategoryTheory

variable {T : RelativeMonad (J)}

/-- The constant functor on the Kleisli category of `T` with value `C.Arity`. -/
def arityConst (T : RelativeMonad (J)) : RelativeMonad.Kleisli T ⥤ Type where
  obj _ := C.Arity
  map _ := ↾fun (Φ : C.Arity) => Φ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The slice category of `T`-modules over `arityConst T`. -/
abbrev ArityMod (T : RelativeMonad (J)) := CategoryTheory.Over (arityConst T)

namespace ArityMod

/-- The underlying `T`-module. -/
abbrev module (M : ArityMod T) : RelativeMonad.Kleisli T ⥤ Type := M.left

/-- The shape of an element of `M`: its image under `M.hom`. -/
def shape (M : ArityMod T) {Ω : C.Arity} :
    module M |>.obj Ω → C.Arity :=
  M.hom.app Ω

/-- The action of a Kleisli arrow preserves shape. -/
theorem shape_natural
    (M : ArityMod T) {Ω Ξ : C.Arity}
    (σ : RelativeMonad.Kleisli.of T Ω ⟶ RelativeMonad.Kleisli.of T Ξ)
    (x : module M |>.obj (RelativeMonad.Kleisli.of T Ω)) :
  shape M (module M |>.map σ x) = shape M x
  := by
  apply NatTrans.naturality_apply M.hom σ x

/-- A morphism of arity modules preserves shape. -/
theorem hom_shape
    {M N : ArityMod T} (f : M ⟶ N)
    {Ω : C.Arity} (x : module M |>.obj Ω) :
  shape N (f.left.app Ω x) = shape M x
  := by
  apply ConcreteCategory.congr_hom (NatTrans.congr_app (Over.w f) Ω) x

end ArityMod
