import HigherRankSyntax.HrS.Presheaf.Pi
import HigherRankSyntax.HrS.Presheaf.Universe
import HigherRankSyntax.HrS.Presheaf.Identity
import HigherRankSyntax.Initiality.Initial

/-!
# The presheaf model

For a small category `𝒞`, the model of the framework whose objects are the presheaves
on `𝒞`, whose substitutions are the maps of presheaves, whose types are the dependent
presheaves and whose terms are their sections; and the morphism from `Ctx.model` to it.
-/

universe v

open CategoryTheory

namespace HrS

namespace Presheaf

variable (𝒞 : Type v) [SmallCategory 𝒞]

/-- The model of presheaves on `𝒞`. -/
def model : Structure.{v + 2} where
  Ob := Presheaf.{v, v + 1} 𝒞
  Sub Δ Γ := Hom Δ Γ
  Ty Γ := DependentPresheaf.{v, v + 1, v + 1} Γ
  Tm _ a := a.Section
  identity := Hom.identity
  comp := Hom.comp
  comp_assoc := Hom.comp_assoc
  identity_comp := Hom.identity_comp
  comp_identity := Hom.comp_identity
  empty := terminal
  toEmpty := Hom.toTerminal
  toEmpty_unique := Hom.toTerminal_unique
  substTy := DependentPresheaf.subst
  substTm := DependentPresheaf.Section.subst
  substTy_identity := DependentPresheaf.subst_identity
  substTm_identity := DependentPresheaf.Section.subst_identity
  substTy_comp := DependentPresheaf.subst_comp
  substTm_comp := DependentPresheaf.Section.subst_comp
  extend := extend
  projection := projection
  generic := generic
  pair := pair
  projection_pair := projection_pair
  generic_pair := generic_pair
  pair_eta := pair_eta
  pair_comp := pair_comp
  U := U
  U_subst := U_subst
  El := El
  El_subst := El_subst
  Bind := Bind
  lam := lam
  unlam := unlam
  lam_unlam := lam_unlam
  unlam_lam := unlam_lam
  Bind_subst := Bind_subst
  lam_subst := lam_subst
  IdSort := DependentPresheaf.Equality
  IdSort_refl := DependentPresheaf.Equality.refl
  IdSort_subst := DependentPresheaf.Equality_subst
  IdSort_irrelevant := DependentPresheaf.Equality.irrelevant
  IdSort_reflect := DependentPresheaf.Equality.reflect
  IdElement := DependentPresheaf.Equality
  IdElement_refl := DependentPresheaf.Equality.refl
  IdElement_subst := DependentPresheaf.Equality_subst
  IdElement_irrelevant := DependentPresheaf.Equality.irrelevant
  IdElement_reflect := DependentPresheaf.Equality.reflect

/-- The morphism from `Ctx.model` to the model of presheaves on `𝒞`. -/
def interpretation : Morphism Ctx.model (model 𝒞) :=
  initialMorphism (model 𝒞)

end Presheaf

end HrS
