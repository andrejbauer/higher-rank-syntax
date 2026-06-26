import HigherRankSyntax.MonadLaws
import HigherRankSyntax.RelativeMonad.Basic

/-!
# Syntax as a relative monad

`SyntaxMonad C` packages `Expr` over a carrier `C` as a relative monad
over the "slots" functor `J : PShape C ⥤ ArityFunc C`, with
`T Γ α = Expr (Γ.tele ∷ α)`.

The category objects are `PShape C`: a `Tele C.Arity` bundled with a
`Proper` instance.  This makes `[Proper Γ.tele]` auto-synthesized
whenever `Γ : PShape C` is in scope, so `lift`, `unit_right`,
`unit_left`, and `comp_lift` can call `Subst.act` and the monad-law
lemmas without manually threading instance args.

With cons-style telescopes, the Kleisli ↔ Subst bridge is cast-free:
`Shape.nil ⋈ X = X` definitionally, so `lift f` is just
`(Subst.mk f).act (Γ := Shape.nil) ⌊α⌋`.
-/


open CategoryTheory

/-- Category structure on `PShape C` with renamings between underlying
telescopes as morphisms. -/
instance ShapeCat {A : Type} (C : Carrier A) : Category C.Arity where
  Hom Γ Δ := Γ →ʳ Δ
  id Γ := Renaming.id Γ
  comp f g := g ∘ʳ f

/-- The arity-indexed family category: a wrapper around `C.Arity → Type` so we can put
a `Category` instance on it without conflicting with the global `Type → Type` setup. -/
@[ext] structure ArityFunc {A : Type} (C : Carrier A) where
  toFun : C.Arity → Type

instance {A : Type} (C : Carrier A) : CoeFun (ArityFunc C) (fun _ => C.Arity → Type) :=
  ⟨ArityFunc.toFun⟩

instance {A : Type} (C : Carrier A) : Category (ArityFunc C) where
  Hom f g := ∀ α, f α → g α
  id _ := fun _ x => x
  comp f g := fun α x => g α (f α x)

/-- The "slots" functor: shape `Γ ↦ α ↦ Γ.tele ∋ α`. -/
def J {A : Type} (C : Carrier A) : C.Arity ⥤ ArityFunc C where
  obj Γ := ⟨fun α => Γ ∋ α⟩
  map {Γ Δ} (ρ : Γ →ʳ Δ) := fun _ p => ρ p

/-- The "expressions" functor: shape `Γ ↦ α ↦ Expr (Γ.tele ∷ α)`. -/
def T {A : Type} (C : Carrier A) : C.Arity ⥤ ArityFunc C where

  obj Γ := ⟨fun α => Expr (Γ ⋈ α)⟩

  map {Γ Δ} (ρ : Γ →ʳ Δ) := fun α e => ⟦ ρ ⇑ʳ α ⟧ʳ e

  map_id Γ := by
    funext α e
    show ⟦ 𝟙ʳ _ ⇑ʳ α ⟧ʳ e = e
    rw [Renaming.extend_id]
    apply Renaming.act_id

  map_comp {Γ Δ Ξ} (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ξ) := by
    funext α e
    show ⟦ (σ ∘ʳ ρ) ⇑ʳ α ⟧ʳ e = ⟦ σ ⇑ʳ α ⟧ʳ (⟦ ρ ⇑ʳ α ⟧ʳ e)
    rw [Renaming.extend_comp]
    apply Renaming.act_comp

/-- The relative monad of the syntax. -/
def SyntaxMonad {A :Type} (C : Carrier A) : RelativeMonad (J C) where

  map := (T C).obj

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
