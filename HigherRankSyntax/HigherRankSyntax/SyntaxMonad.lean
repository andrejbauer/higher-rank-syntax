import HigherRankSyntax.MonadLaws
import HigherRankSyntax.RelativeMonad.Basic

/-!
# Syntax as a relative monad

`SyntaxMonad C` packages `Expr` over a carrier `C` as a relative monad
over the slots functor `J : C.Arity ⥤ ArityTyFunc C`, with
`T Γ α τ = Expr (Γ ⋈ α) τ`.

The base category has arities as objects and renamings as morphisms.  A Kleisli
map `J Γ ⟶ T Δ` is exactly a substitution from `Γ` to `Δ`: it sends each
`Γ`-slot of arity `α` and result type `τ` to an expression in `Δ ⋈ α` of
result type `τ`.
-/


open CategoryTheory

/-- Category structure on arities with renamings as morphisms. -/
instance arityCategory {A : Type} (C : Carrier A) : Category C.Arity where
  Hom Γ Δ := Γ →ʳ Δ
  id Γ := Renaming.id Γ
  comp f g := g ∘ʳ f

/-- The arity-and-type-indexed family category. -/
@[ext] structure ArityTyFunc {A : Type} (C : Carrier A) where
  toFun : C.Arity → C.Ty → Type

instance {A : Type} (C : Carrier A) :
    CoeFun (ArityTyFunc C) (fun _ => C.Arity → C.Ty → Type) :=
  ⟨ArityTyFunc.toFun⟩

instance {A : Type} (C : Carrier A) : Category (ArityTyFunc C) where
  Hom f g := ∀ α τ, f α τ → g α τ
  id _ := fun _ _ x => x
  comp f g := fun α τ x => g α τ (f α τ x)

/-- The slots functor: arity `Γ ↦ α ↦ τ ↦ Γ ∋[τ] α`. -/
def J {A : Type} (C : Carrier A) : C.Arity ⥤ ArityTyFunc C where
  obj Γ := ⟨fun α τ => Γ ∋[τ] α⟩
  map {Γ Δ} (ρ : Γ →ʳ Δ) := fun _ _ p => ρ p

/-- The expressions functor: arity `Γ ↦ α ↦ τ ↦ Expr (Γ ⋈ α) τ`. -/
def T {A : Type} (C : Carrier A) : C.Arity ⥤ ArityTyFunc C where

  obj Γ := ⟨fun α τ => Expr (Γ ⋈ α) τ⟩

  map {Γ Δ} (ρ : Γ →ʳ Δ) := fun α _ e => ⟦ ρ ⇑ʳ α ⟧ʳ e

  map_id Γ := by
    funext α τ e
    have hId : (𝟙 Γ : Γ →ʳ Γ) = 𝟙ʳ Γ := rfl
    rw [hId, Renaming.extend_id]
    apply Renaming.act_id

  map_comp {Γ Δ Ξ} (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ξ) := by
    funext α τ e
    trans ⟦ (σ ∘ʳ ρ) ⇑ʳ α ⟧ʳ e
    · congr 2
    · rw [Renaming.extend_comp]
      apply Renaming.act_comp

/-- The relative monad of the syntax. -/
def SyntaxMonad {A : Type} (C : Carrier A) : RelativeMonad (J C) where

  map := (T C).obj

  η Γ _ _ := Expr.η

  lift {Γ Δ} f α _ e :=
    Subst.act @f (Γ := 1) α e

  unit_right := by
    intro Γ
    funext α τ e
    apply act_id

  unit_left := by
    intro Γ Δ f
    funext α τ p
    symm
    apply act_η

  comp_lift := by
    intro Γ Δ Ξ f g
    funext α τ e
    apply act_comp
