import Mathlib.CategoryTheory.Types.Basic
import HigherRankSyntax.RelativeMonad.Module
import HigherRankSyntax.SyntaxMonad
import HigherRankSyntax.Typing.Decoration

/-!
# Decorated telescopes as a module over raw syntax

Raw substitutions reindex the external base of a decorated telescope while
leaving its arity unchanged.
-/

open CategoryTheory

variable {A : Type} {C : Carrier A}

namespace ClassifierAt

variable {bd : C.Ty → Option C.Ty}

private def renameAux {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) :
    (o : Option C.Ty) →
      (match o with | none => PUnit | some τ => Expr Γ τ) →
      (match o with | none => PUnit | some τ => Expr Δ τ)
  | none, _ => PUnit.unit
  | some _, a => Renaming.act ρ a

/-- Reindex a classifier along a renaming of its base. -/
def rename {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) {τ : C.Ty}
    (a : ClassifierAt bd Γ τ) : ClassifierAt bd Δ τ :=
  renameAux ρ (bd τ) a

private theorem renameAux_id {Γ : C.Arity}
    (o : Option C.Ty)
    (a : match o with | none => PUnit | some τ => Expr Γ τ) :
    renameAux (𝟙ʳ Γ) o a = a := by
  cases o with
  | none => exact Subsingleton.elim _ _
  | some τ => apply Renaming.act_id

theorem rename_id {Γ : C.Arity} {τ : C.Ty} (a : ClassifierAt bd Γ τ) :
    rename (𝟙ʳ Γ) a = a :=
  renameAux_id (bd τ) a

private def substituteAux {S Γ Δ Φ : C.Arity} (σ : Subst Γ (S ⋈ Δ)) :
    (o : Option C.Ty) →
      (match o with | none => PUnit | some τ => Expr (S ⋈ Γ ⋈ Φ) τ) →
      (match o with | none => PUnit | some τ => Expr (S ⋈ Δ ⋈ Φ) τ)
  | none, _ => PUnit.unit
  | some _, a => Subst.act σ Φ a

/-- Reindex a classifier by substituting the component after a fixed prefix. -/
def substitute {S Γ Δ Φ : C.Arity} (σ : Subst Γ (S ⋈ Δ)) {τ : C.Ty}
    (a : ClassifierAt bd (S ⋈ Γ ⋈ Φ) τ) :
    ClassifierAt bd (S ⋈ Δ ⋈ Φ) τ :=
  substituteAux σ (bd τ) a

private theorem substituteAux_comp {S Γ Δ Ξ Φ : C.Arity}
    (σ : Subst Γ (S ⋈ Δ)) (θ : Subst Δ (S ⋈ Ξ))
    (o : Option C.Ty)
    (a : match o with | none => PUnit | some τ => Expr (S ⋈ Γ ⋈ Φ) τ) :
    substituteAux (Subst.comp σ θ) o a =
      substituteAux θ o (substituteAux σ o a) := by
  cases o with
  | none => exact Subsingleton.elim _ _
  | some τ => apply act_comp

theorem substitute_comp {S Γ Δ Ξ Φ : C.Arity}
    (σ : Subst Γ (S ⋈ Δ)) (θ : Subst Δ (S ⋈ Ξ))
    {τ : C.Ty} (a : ClassifierAt bd (S ⋈ Γ ⋈ Φ) τ) :
    substitute (Subst.comp σ θ) a = substitute θ (substitute σ a) :=
  substituteAux_comp σ θ (bd τ) a

private theorem substituteAux_ofRenaming {Γ Δ Φ : C.Arity}
    (ρ : Γ →ʳ Δ) (o : Option C.Ty)
    (a : match o with | none => PUnit | some τ => Expr (Γ ⋈ Φ) τ) :
    substituteAux (S := 1) (Φ := Φ) (Subst.ofRenaming ρ) o a =
      renameAux (ρ ⇑ʳ Φ) o a := by
  cases o with
  | none => rfl
  | some τ => apply act_ofRenaming

/-- Substitution by eta-expanded renamed slots agrees with classifier renaming. -/
theorem substitute_ofRenaming {Γ Δ Φ : C.Arity} (ρ : Γ →ʳ Δ)
    {τ : C.Ty} (a : ClassifierAt bd (Γ ⋈ Φ) τ) :
    substitute (S := 1) (Φ := Φ) (Subst.ofRenaming ρ) a =
      rename (ρ ⇑ʳ Φ) a :=
  substituteAux_ofRenaming ρ (bd τ) a

/-- Classifier action by a lift agrees with substitution below the suffix. -/
theorem substitute_lift {Γ Δ Φ Ψ : C.Arity} (σ : Subst Γ Δ)
    {τ : C.Ty} (a : ClassifierAt bd (Γ ⋈ Φ ⋈ Ψ) τ) :
    ClassifierAt.cast
        (show 1 ⋈ (Δ ⋈ Φ) ⋈ Ψ = 1 ⋈ Δ ⋈ (Φ ⋈ Ψ) by
          simp only [one_mul, mul_assoc])
        (substitute (S := 1) (Φ := Ψ) (Subst.lift σ Φ) a) =
      substitute (S := 1) (Φ := Φ ⋈ Ψ) σ a := by
  unfold substitute ClassifierAt.cast
  unfold ClassifierAt at a ⊢
  generalize h : bd τ = o at a ⊢
  cases o with
  | none => rfl
  | some υ =>
      simpa only [ClassifierAt, substitute, substituteAux,
        ClassifierAt.cast, one_mul] using Subst.act_lift σ Φ Ψ a

theorem substitute_cast_local {S Γ Δ Φ Λ Ξ α : C.Arity}
    (σ : Subst Γ (S ⋈ Δ)) (h : Λ = Ξ) {τ : C.Ty}
    (a : ClassifierAt bd (S ⋈ Γ ⋈ Φ ⋈ Λ ⋈ α) τ) :
    substitute (Φ := Φ ⋈ Ξ ⋈ α) σ
        (ClassifierAt.cast
          (congrArg (fun Ω => S ⋈ Γ ⋈ Φ ⋈ Ω ⋈ α) h) a) =
      ClassifierAt.cast
        (congrArg (fun Ω => S ⋈ Δ ⋈ Φ ⋈ Ω ⋈ α) h)
        (substitute (Φ := Φ ⋈ Λ ⋈ α) σ a) := by
  subst Ξ
  rfl

end ClassifierAt

namespace Decoration

variable [Precedence C] {bd : C.Ty → Option C.Ty}

/-- Reindex the external base of a decoration along a renaming. -/
def rename {Γ Δ Ξ : C.Arity} (ρ : Γ →ʳ Δ) :
    Decoration bd Γ Ξ → Decoration bd Δ Ξ :=
  fun D ⦃Φ⦄ ⦃α⦄ ⦃_⦄ p =>
    ClassifierAt.rename ((ρ ⇑ʳ Φ) ⇑ʳ α) (D p)

theorem rename_id {Γ Ξ : C.Arity} (D : Decoration bd Γ Ξ) :
    rename (𝟙ʳ Γ) D = D := by
  funext Φ α τ p
  rw [rename, Renaming.extend_id, Renaming.extend_id]
  apply ClassifierAt.rename_id

/-- Reindex the context component of a decoration after the fixed prefix `S`. -/
def substitute {S Γ Δ Φ Ξ : C.Arity} (σ : Subst Γ (S ⋈ Δ)) :
    Decoration bd (S ⋈ Γ ⋈ Φ) Ξ → Decoration bd (S ⋈ Δ ⋈ Φ) Ξ :=
  fun D ⦃Ω⦄ ⦃α⦄ ⦃_⦄ p =>
    ClassifierAt.substitute (Φ := Φ ⋈ Ω ⋈ α) σ (D p)

theorem substitute_comp {S Γ Δ Ξ Φ Ω : C.Arity}
    (σ : Subst Γ (S ⋈ Δ)) (θ : Subst Δ (S ⋈ Ξ))
    (D : Decoration bd (S ⋈ Γ ⋈ Φ) Ω) :
    substitute (Subst.comp σ θ) D = substitute θ (substitute σ D) := by
  funext Λ α τ p
  apply ClassifierAt.substitute_comp

/-- Reindex the external base of a decoration by a raw substitution. -/
def act {Γ Δ Ξ : C.Arity} (σ : Subst Γ Δ) :
    Decoration bd Γ Ξ → Decoration bd Δ Ξ :=
  substitute (S := 1) (Φ := 1) σ

/-- Acting by eta-expanded renamed slots agrees with decoration renaming. -/
theorem act_ofRenaming {Γ Δ Ξ : C.Arity} (ρ : Γ →ʳ Δ)
    (D : Decoration bd Γ Ξ) :
    act (Subst.ofRenaming ρ) D = rename ρ D := by
  funext Φ α τ p
  rw [act, substitute, rename, ← Renaming.extend_assoc]
  apply ClassifierAt.substitute_ofRenaming

/-- The identity substitution acts trivially on decorations. -/
theorem act_id {Γ Ξ : C.Arity} (D : Decoration bd Γ Ξ) :
    act (Subst.id Γ) D = D := by
  calc
    act (Subst.id Γ) D = act (Subst.ofRenaming (𝟙ʳ Γ)) D := rfl
    _ = rename (𝟙ʳ Γ) D := act_ofRenaming _ _
    _ = D := rename_id D

/-- Acting by a composite substitution is successive action. -/
theorem act_comp {Γ Δ Ξ Ω : C.Arity}
    (σ : Subst Γ Δ) (θ : Subst Δ Ξ) (D : Decoration bd Γ Ω) :
    act (Subst.comp (Γ := 1) σ θ) D = act θ (act σ D) := by
  apply substitute_comp

/-- Decoration action by a lift agrees with substitution below the suffix. -/
theorem act_lift {Γ Δ Φ Ξ : C.Arity} (σ : Subst Γ Δ)
    (D : Decoration bd (Γ ⋈ Φ) Ξ) :
    act (Subst.lift σ Φ) D = substitute (S := 1) (Φ := Φ) σ D := by
  funext Ψ Λ τ p
  apply ClassifierAt.cast_injective (mul_assoc Δ Φ (Ψ ⋈ Λ))
  apply ClassifierAt.substitute_lift

end Decoration

namespace DecoratedTelescope

variable [Precedence C] {bd : C.Ty → Option C.Ty}

/-- Reindex the base of a decorated telescope along a renaming. -/
def rename {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ)
    (Ξ : DecoratedTelescope bd Γ) : DecoratedTelescope bd Δ where
  arity := Ξ.arity
  decoration := Decoration.rename ρ Ξ.decoration

/-- Reindex the context component of a decorated telescope by substitution. -/
def substitute {S Γ Δ Φ : C.Arity} (σ : Subst Γ (S ⋈ Δ))
    (Ξ : DecoratedTelescope bd (S ⋈ Γ ⋈ Φ)) :
    DecoratedTelescope bd (S ⋈ Δ ⋈ Φ) where
  arity := Ξ.arity
  decoration := Decoration.substitute σ Ξ.decoration

/-- Reindex the external base of a decorated telescope by a raw substitution. -/
def act {Γ Δ : C.Arity} (σ : Subst Γ Δ)
    (Ξ : DecoratedTelescope bd Γ) : DecoratedTelescope bd Δ where
  arity := Ξ.arity
  decoration := Decoration.act σ Ξ.decoration

/-- Acting by eta-expanded renamed slots agrees with telescope renaming. -/
theorem act_ofRenaming {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ)
    (Ξ : DecoratedTelescope bd Γ) :
    act (Subst.ofRenaming ρ) Ξ = rename ρ Ξ := by
  cases Ξ
  simp [act, rename, Decoration.act_ofRenaming]

/-- The identity substitution acts trivially on decorated telescopes. -/
theorem act_id {Γ : C.Arity} (Δ : DecoratedTelescope bd Γ) :
    act (Subst.id Γ) Δ = Δ := by
  cases Δ
  simp [act, Decoration.act_id]

/-- Acting by a composite substitution is successive action. -/
theorem act_comp {Γ Δ Ξ : C.Arity}
    (σ : Subst Γ Δ) (θ : Subst Δ Ξ)
    (Ω : DecoratedTelescope bd Γ) :
    act (Subst.comp (Γ := 1) σ θ) Ω = act θ (act σ Ω) := by
  cases Ω
  simp [act, Decoration.act_comp]
  rfl

/-- Telescope action by a lift agrees with substitution below the suffix. -/
theorem act_lift {Γ Δ Φ : C.Arity} (σ : Subst Γ Δ)
    (Ξ : DecoratedTelescope bd (Γ ⋈ Φ)) :
    act (Subst.lift σ Φ) Ξ = substitute (S := 1) (Φ := Φ) σ Ξ := by
  cases Ξ
  simp [act, substitute, Decoration.act_lift]
  rfl

end DecoratedTelescope

/-- Decorated telescopes form a module over the raw syntax relative monad. -/
def DTel [Precedence C] (bd : C.Ty → Option C.Ty) :
    RelativeMonad.LeftModule (SyntaxMonad C) (Type) where
  obj Γ := DecoratedTelescope bd Γ
  map σ := ↾(DecoratedTelescope.act σ)
  map_id Γ := by
    ext Δ
    apply DecoratedTelescope.act_id
  map_comp σ θ := by
    ext Ω
    apply DecoratedTelescope.act_comp

@[simp]
theorem DTel_act [Precedence C] (bd : C.Ty → Option C.Ty)
    {Γ Δ : C.Arity} (σ : Subst Γ Δ) (Ξ : DecoratedTelescope bd Γ) :
    (RelativeMonad.LeftModule.act (DTel bd) σ) Ξ =
      DecoratedTelescope.act σ Ξ := rfl
