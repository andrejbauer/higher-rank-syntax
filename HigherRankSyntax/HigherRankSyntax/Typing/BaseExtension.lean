import Mathlib.CategoryTheory.EqToHom
import HigherRankSyntax.SyntaxMonad

/-!
# Fixed-suffix base extension

The syntax Kleisli category is acted on on the right by raw arities: extending
the base by `Φ` fixes the slots of `Φ` and lifts substitutions through them.
-/

open CategoryTheory

variable {A : Type} {C : Carrier A}

/-- The Kleisli category of the raw syntax relative monad. -/
abbrev SyntaxKleisli (C : Carrier A) :=
  RelativeMonad.Kleisli (SyntaxMonad C)

namespace SyntaxKleisli

/-- The Kleisli identity is the raw eta-substitution. -/
theorem id_eq (Ω : C.Arity) :
    (𝟙 (RelativeMonad.Kleisli.of (SyntaxMonad C) Ω) :
      RelativeMonad.Kleisli.of (SyntaxMonad C) Ω ⟶
        RelativeMonad.Kleisli.of (SyntaxMonad C) Ω) =
      Subst.id Ω := rfl

/-- The equality morphism in the syntax Kleisli category is eta-expansion of
the transported raw slot. -/
theorem eqToHom_apply {Ω Ξ : C.Arity} (h : Ω = Ξ)
    {α : C.Arity} {τ : C.Ty} (x : Ω ∋[τ] α) :
    (@CategoryTheory.eqToHom (SyntaxKleisli C) _ Ω Ξ h) α τ x =
      Expr.η (h ▸ x) := by
  subst Ξ
  rfl

/-- Acting by an equality morphism only transports the ambient raw base. -/
theorem act_eqToHom {Ω Ξ Φ : C.Arity} (h : Ω = Ξ)
    {τ : C.Ty} (e : Expr (Ω ⋈ Φ) τ) :
    Subst.act (Γ := 1) (@CategoryTheory.eqToHom (SyntaxKleisli C) _ Ω Ξ h)
      Φ e =
      (congrArg (fun Λ => Expr (Λ ⋈ Φ) τ) h) ▸ e := by
  subst Ξ
  apply act_id

/-- Extend every raw base by a fixed suffix. -/
def extendBy (Φ : C.Arity) : SyntaxKleisli C ⥤ SyntaxKleisli C where
  obj Ω := Ω ⋈ Φ
  map σ := Subst.lift σ Φ
  map_id Ω := by
    change Subst.lift (Subst.id Ω) Φ = Subst.id (Ω ⋈ Φ)
    apply Subst.lift_id
  map_comp σ θ := by
    change Subst.lift (Subst.comp (Γ := 1) σ θ) Φ =
      Subst.comp (Γ := 1) (Θ := _ ⋈ Φ) (Ξ := _ ⋈ Φ)
        (Subst.lift σ Φ) (Subst.lift θ Φ)
    apply Subst.lift_comp

/-- Extending by the empty suffix is naturally the identity functor. -/
def extendByOne : extendBy (C := C) 1 ≅ 𝟭 (SyntaxKleisli C) :=
  NatIso.ofComponents
    (fun Ω => eqToIso (@mul_one C.Arity _ Ω)) (by
    intro Ω Ξ σ
    apply eq_of_heq
    exact
      (comp_eqToHom_heq ((extendBy (C := C) 1).map σ)
        (@mul_one C.Arity _ Ξ)).trans
      ((heq_of_eq (Subst.lift_one σ)).trans
        (eqToHom_comp_heq σ (@mul_one C.Arity _ Ω)).symm))

/-- Successive fixed-suffix extensions are naturally extension by the
product suffix. -/
def extendByAssoc (Φ Ψ : C.Arity) :
    extendBy (C := C) Φ ⋙ extendBy Ψ ≅ extendBy (Φ ⋈ Ψ) :=
  NatIso.ofComponents
    (fun Ω => eqToIso (@mul_assoc C.Arity _ Ω Φ Ψ)) (by
    intro Ω Ξ σ
    apply eq_of_heq
    exact
      (comp_eqToHom_heq
        ((extendBy (C := C) Φ ⋙ extendBy Ψ).map σ)
        (@mul_assoc C.Arity _ Ξ Φ Ψ)).trans
      ((heq_of_eq (Subst.lift_assoc σ Φ Ψ).symm).trans
        (eqToHom_comp_heq ((extendBy (C := C) (Φ ⋈ Ψ)).map σ)
          (@mul_assoc C.Arity _ Ω Φ Ψ)).symm))

end SyntaxKleisli
