import Mathlib.CategoryTheory.Types.Basic
import HigherRankSyntax.RelativeMonad.Module
import HigherRankSyntax.SyntaxMonad
import HigherRankSyntax.Typing.Decoration

/-!
# Decorated telescopes as a module over raw syntax

The boundaries stored in a decoration are raw expressions, so raw renamings and
substitutions act on them.  Reindexing changes only the external base and
transports every boundary in the context determined by its accumulated prefix
and binding arity; the undecorated arity stays fixed.

Decorated telescopes therefore assemble into the module
`DTel : Kl(SyntaxMonad C) ⥤ Type`.  This file supplies only that action.
Boundaries remain raw expressions: the module carries no well-formedness
evidence.
-/

open CategoryTheory

variable {A : Type} {C : Carrier A}

namespace Boundary

/-- Substitution by eta-expanded renamed slots agrees with renaming. -/
theorem act_ofRenaming {Γ Δ Φ : C.Arity} (ρ : Γ →ʳ Δ) (β : Boundary (Γ ⋈ Φ)) :
  act (Γ := 1) (Subst.ofRenaming ρ) Φ β = rename (ρ ⇑ʳ Φ) β := by
  cases β with
  | sort => rfl
  | of S => exact congrArg Boundary.of (_root_.act_ofRenaming ρ S)

end Boundary

namespace Decoration

/-- Reindex the external base of a decoration along a renaming. -/
def rename {Γ Δ Ξ : C.Arity} (ρ : Γ →ʳ Δ) :
    Decoration Γ Ξ → Decoration Δ Ξ :=
  fun D ⦃Φ⦄ ⦃α⦄ p => Boundary.rename ((ρ ⇑ʳ Φ) ⇑ʳ α) (D p)

theorem rename_id {Γ Ξ : C.Arity} (D : Decoration Γ Ξ) :
  rename (𝟙ʳ Γ) D = D := by
  funext Φ α p
  rw [rename, Renaming.extend_id, Renaming.extend_id]
  apply Boundary.rename_id

/-- Reindex the context component of a decoration after the fixed prefix `S`. -/
def substitute {S Γ Δ Φ Ξ : C.Arity} (σ : Subst Γ (S ⋈ Δ)) :
    Decoration (S ⋈ Γ ⋈ Φ) Ξ → Decoration (S ⋈ Δ ⋈ Φ) Ξ :=
  fun D ⦃Ω⦄ ⦃α⦄ p => Boundary.act σ (Φ ⋈ Ω ⋈ α) (D p)

theorem substitute_comp {S Γ Δ Ξ Φ Ω : C.Arity}
    (σ : Subst Γ (S ⋈ Δ)) (θ : Subst Δ (S ⋈ Ξ))
    (D : Decoration (S ⋈ Γ ⋈ Φ) Ω) :
  substitute (Subst.comp σ θ) D = substitute θ (substitute σ D) := by
  funext Λ α p
  apply Boundary.act_comp

/-- Reindex the external base of a decoration by a raw substitution. -/
def act {Γ Δ Ξ : C.Arity} (σ : Subst Γ Δ) :
    Decoration Γ Ξ → Decoration Δ Ξ :=
  substitute (S := 1) (Φ := 1) σ

/-- Acting by eta-expanded renamed slots agrees with decoration renaming. -/
theorem act_ofRenaming {Γ Δ Ξ : C.Arity} (ρ : Γ →ʳ Δ) (D : Decoration Γ Ξ) :
  act (Subst.ofRenaming ρ) D = rename ρ D := by
  funext Φ α p
  rw [act, substitute, rename, ← Renaming.extend_assoc]
  apply Boundary.act_ofRenaming

/-- The identity substitution acts trivially on decorations. -/
theorem act_id {Γ Ξ : C.Arity} (D : Decoration Γ Ξ) :
  act (Subst.id Γ) D = D := by
  calc
    act (Subst.id Γ) D = act (Subst.ofRenaming (𝟙ʳ Γ)) D := rfl
    _ = rename (𝟙ʳ Γ) D := act_ofRenaming _ _
    _ = D := rename_id D

/-- Acting by a composite substitution is successive action. -/
theorem act_comp {Γ Δ Ξ Ω : C.Arity}
    (σ : Subst Γ Δ) (θ : Subst Δ Ξ) (D : Decoration Γ Ω) :
  act (Subst.comp (Γ := 1) σ θ) D = act θ (act σ D) :=
  substitute_comp (S := 1) (Φ := 1) σ θ D

end Decoration

namespace DecoratedTelescope

/-- Reindex the base of a decorated telescope along a renaming. -/
def rename {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ)
    (Ξ : DecoratedTelescope Γ) : DecoratedTelescope Δ where
  arity := Ξ.arity
  decoration := Decoration.rename ρ Ξ.decoration

/-- Reindex the context component of a decorated telescope by substitution. -/
def substitute {S Γ Δ Φ : C.Arity} (σ : Subst Γ (S ⋈ Δ))
    (Ξ : DecoratedTelescope (S ⋈ Γ ⋈ Φ)) :
    DecoratedTelescope (S ⋈ Δ ⋈ Φ) where
  arity := Ξ.arity
  decoration := Decoration.substitute σ Ξ.decoration

/-- Reindex the external base of a decorated telescope by a raw substitution. -/
def act {Γ Δ : C.Arity} (σ : Subst Γ Δ)
    (Ξ : DecoratedTelescope Γ) : DecoratedTelescope Δ where
  arity := Ξ.arity
  decoration := Decoration.act σ Ξ.decoration

/-- Acting by eta-expanded renamed slots agrees with telescope renaming. -/
theorem act_ofRenaming {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ)
    (Ξ : DecoratedTelescope Γ) :
  act (Subst.ofRenaming ρ) Ξ = rename ρ Ξ := by
  cases Ξ
  simp [act, rename, Decoration.act_ofRenaming]

/-- The identity substitution acts trivially on decorated telescopes. -/
theorem act_id {Γ : C.Arity} (Δ : DecoratedTelescope Γ) :
  act (Subst.id Γ) Δ = Δ := by
  cases Δ
  simp [act, Decoration.act_id]

/-- Acting by a composite substitution is successive action. -/
theorem act_comp {Γ Δ Ξ : C.Arity}
    (σ : Subst Γ Δ) (θ : Subst Δ Ξ) (Ω : DecoratedTelescope Γ) :
  act (Subst.comp (Γ := 1) σ θ) Ω = act θ (act σ Ω) := by
  cases Ω
  simp [act, Decoration.act_comp]
  rfl

end DecoratedTelescope

/-- Decorated telescopes form a module over the raw syntax relative monad. -/
def DTel (C : Carrier A) : RelativeMonad.LeftModule (SyntaxMonad C) Type where
  obj Γ := DecoratedTelescope (C := C) Γ
  map σ := ↾(DecoratedTelescope.act σ)
  map_id Γ := by
    ext Δ
    apply DecoratedTelescope.act_id
  map_comp σ θ := by
    ext Ω
    apply DecoratedTelescope.act_comp

@[simp]
theorem DTel_act {Γ Δ : C.Arity} (σ : Subst Γ Δ) (Ξ : DecoratedTelescope Γ) :
  (RelativeMonad.LeftModule.act (DTel C) σ) Ξ = DecoratedTelescope.act σ Ξ := rfl
