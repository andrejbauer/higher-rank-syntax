import HigherRankSyntax.MonadLaws
import HigherRankSyntax.RelativeMonad.Kleisli

/-!
# Syntax as a relative monad

`SyntaxMonad` packages `Expr` as a relative monad over the slots functor
`J : C.Arity ⥤ ArityFunc`, with
`T Γ α = Expr (Γ ⋈ α)`.

The base category has arities as objects and renamings as morphisms.  A Kleisli
map `J.obj Γ ⟶ T.obj Δ` is a substitution `Subst Γ Δ`: it sends each slot of `Γ`
of arity `α` to an expression over `Δ ⋈ α`.
-/


open CategoryTheory

/-- Category structure on arities with renamings as morphisms. -/
instance arityCategory : Category C.Arity where
  Hom Γ Δ := Γ →ʳ Δ
  id Γ := Renaming.id Γ
  comp f g := g ∘ʳ f

/-- Arity-indexed families of types. -/
@[ext] structure ArityFunc where
  toFun : C.Arity → Type

instance : CoeFun ArityFunc (fun _ => C.Arity → Type) :=
  ⟨ArityFunc.toFun⟩

instance : Category ArityFunc where
  Hom f g := ∀ α, f α → g α
  id _ := fun _ x => x
  comp f g := fun α x => g α (f α x)

/-- The functor sending `Γ` to the family of its slots `α ↦ Γ ∋ α` and a renaming to
its action on slots. -/
def J : C.Arity ⥤ ArityFunc where
  obj Γ := ⟨fun α => Γ ∋ α⟩
  map {Γ Δ} (ρ : Γ →ʳ Δ) := fun _ p => ρ p

/-- The functor sending `Γ` to `α ↦ Expr (Γ ⋈ α)` and `ρ` to renaming along `ρ ⇑ʳ α`. -/
def T : C.Arity ⥤ ArityFunc where

  obj Γ := ⟨fun α => Expr (Γ ⋈ α)⟩

  map {Γ Δ} (ρ : Γ →ʳ Δ) := fun α e => ⟦ ρ ⇑ʳ α ⟧ʳ e

  map_id Γ := by
    funext α e
    convert Renaming.act_id e
    apply Renaming.extend_id

  map_comp ρ σ := by
    funext α e
    convert Renaming.act_comp (ρ ⇑ʳ α) (σ ⇑ʳ α) e
    apply Renaming.extend_comp

/-- The relative monad over `J` sending `Γ` to `α ↦ Expr (Γ ⋈ α)`, with unit `Expr.η` and
Kleisli extension the substitution action `Subst.act` at depth `α`. -/
def SyntaxMonad : RelativeMonad J where

  map := T.obj

  η Γ _ := Expr.η

  lift {Γ Δ} f α e :=
    Subst.act @f (Γ := 1) α e

  unit_right Γ := by
    funext α e
    apply act_id

  unit_left f := by
    funext α x
    symm
    apply act_η

  comp_lift f g := by
    funext α e
    apply act_comp

/-- Kleisli morphisms `Γ ⟶ Δ` of `SyntaxMonad` are the substitutions `Subst Γ Δ`. -/
def syntaxKleisliHomEquiv (Γ Δ : C.Arity) :
    (RelativeMonad.Kleisli.of SyntaxMonad Γ ⟶
      RelativeMonad.Kleisli.of SyntaxMonad Δ) ≃ Subst Γ Δ :=
  Equiv.refl _
