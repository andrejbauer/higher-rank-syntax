import HigherRankSyntax.Ctx.Binding
import HigherRankSyntax.Ctx.Identity
import HigherRankSyntax.HrS.Structure

/-!
# The model on context classes

The context classes, with the substitutions between them, the one-entry types
over them and the terms of those types, form a model of the framework `HrS`.
-/

open CategoryTheory

namespace Ctx

/-- The model of `HrS` whose objects are the context classes, whose substitutions
are the morphisms of `Ob`, and whose types and terms are `Ty₁` and `Tm₁`. -/
def model : HrS.Structure where
  Ob := Ob
  Sub X Y := X ⟶ Y
  Ty := Ty₁
  Tm := Tm₁
  identity X := 𝟙 X
  comp σ θ := θ ≫ σ
  comp_assoc σ θ κ := by rw [Category.assoc]
  identity_comp σ := Category.comp_id σ
  comp_identity σ := Category.id_comp σ
  empty := Ctx.empty.toOb
  toEmpty X := emptyIsTerminal.from X
  toEmpty_unique σ := emptyIsTerminal.hom_ext σ _
  substTy a σ := a.subst σ
  substTm t σ := t.subst σ
  substTy_identity a := Ty₁.subst_id a
  substTm_identity t := Tm₁.cast_eq (Ty₁.subst_id _) (Tm₁.subst_id t)
  substTy_comp a σ θ := Ty₁.subst_comp a σ θ
  substTm_comp t σ θ := Tm₁.cast_eq (Ty₁.subst_comp _ σ θ) (Tm₁.subst_comp t σ θ)
  extend X a := Ob.extend X a.toTy
  projection a := Ob.projection _ a.toTy
  generic a := Tm₁.generic a
  pair σ t := Ty₁.pair σ t
  projection_pair σ t := Ty₁.projection_pair σ t
  generic_pair σ t := Ty₁.generic_pair σ t
  pair_eta a := Ty₁.pair_eta a
  lift a σ := Ty₁.lift a σ
  projection_lift a σ := Ty₁.projection_lift a σ
  generic_lift a σ := Ty₁.generic_lift a σ
  U X := U X
  U_subst σ := U_subst σ
  El S := El S
  El_subst S σ := El_subst S σ
  Bind a c := Bind a c
  lam e := lam e
  unlam t := unlam t
  lam_unlam t := lam_unlam t
  unlam_lam e := unlam_lam e
  Bind_subst a c σ := Bind_subst a c σ
  lam_subst e σ := lam_subst e σ
  IdSort S S' := IdSort S S'
  IdSort_refl S := IdSort_refl S
  IdSort_subst S S' σ := IdSort_subst S S' σ
  IdSort_irrelevant t t' := IdSort_irrelevant t t'
  IdSort_reflect t := IdSort_reflect t
  IdElement l r := IdElement l r
  IdElement_refl l := IdElement_refl l
  IdElement_subst l r σ := IdElement_subst l r σ
  IdElement_irrelevant t t' := IdElement_irrelevant t t'
  IdElement_reflect t := IdElement_reflect t

end Ctx
