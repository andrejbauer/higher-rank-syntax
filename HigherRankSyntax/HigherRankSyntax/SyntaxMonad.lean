import HigherRankSyntax.MonadLaws
import HigherRankSyntax.RelativeMonad.Kleisli

/-!
# Syntax as a relative monad

`SyntaxMonad` packages `Expr` as a relative monad over the slots functor
`J : C.Arity ⥤ ArityFunc`, with
`T Γ α = Expr (Γ ⋈ α)`.

The base category has arities as objects and renamings as morphisms.  A Kleisli
map `J Γ ⟶ T Δ` is exactly a substitution from `Γ` to `Δ`: it sends each
`Γ`-slot of arity `α` to an expression in `Δ ⋈ α`.
-/


open CategoryTheory

/-- Category structure on arities with renamings as morphisms. -/
instance arityCategory : Category C.Arity where
  Hom Γ Δ := Γ →ʳ Δ
  id Γ := Renaming.id Γ
  comp f g := g ∘ʳ f

/-- The arity-indexed family category. -/
@[ext] structure ArityFunc where
  toFun : C.Arity → Type

instance : CoeFun ArityFunc (fun _ => C.Arity → Type) :=
  ⟨ArityFunc.toFun⟩

instance : Category ArityFunc where
  Hom f g := ∀ α, f α → g α
  id _ := fun _ x => x
  comp f g := fun α x => g α (f α x)

/-- The slots functor: arity `Γ ↦ α ↦ Γ ∋ α`. -/
def J : C.Arity ⥤ ArityFunc where
  obj Γ := ⟨fun α => Γ ∋ α⟩
  map {Γ Δ} (ρ : Γ →ʳ Δ) := fun _ p => ρ p

/-- The expressions functor: arity `Γ ↦ α ↦ Expr (Γ ⋈ α)`. -/
def T : C.Arity ⥤ ArityFunc where

  obj Γ := ⟨fun α => Expr (Γ ⋈ α)⟩

  map {Γ Δ} (ρ : Γ →ʳ Δ) := fun α e => ⟦ ρ ⇑ʳ α ⟧ʳ e

  map_id Γ := by
    funext α e
    have hId : (𝟙 Γ : Γ →ʳ Γ) = 𝟙ʳ Γ := rfl
    rw [hId, Renaming.extend_id]
    apply Renaming.act_id

  map_comp {Γ Δ Ξ} (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ξ) := by
    funext α e
    trans ⟦ (σ ∘ʳ ρ) ⇑ʳ α ⟧ʳ e
    · congr 2
    · rw [Renaming.extend_comp]
      apply Renaming.act_comp

/-- The relative monad of the syntax. -/
def SyntaxMonad : RelativeMonad J where

  map := T.obj

  η Γ _ := Expr.η

  lift {Γ Δ} f α e :=
    Subst.act @f (Γ := 1) α e

  unit_right := by
    intro Γ
    funext α e
    apply act_id

  unit_left := by
    intro Γ Δ f
    funext α p
    symm
    apply act_η

  comp_lift := by
    intro Γ Δ Ξ f g
    funext α e
    apply act_comp

/-- Kleisli morphisms for raw syntax are raw substitutions. -/
def syntaxKleisliHomEquiv (Γ Δ : C.Arity) :
    (RelativeMonad.Kleisli.of SyntaxMonad Γ ⟶
      RelativeMonad.Kleisli.of SyntaxMonad Δ) ≃ Subst Γ Δ :=
  Equiv.refl _
