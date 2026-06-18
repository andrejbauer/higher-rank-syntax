import HigherRankSyntax.Subst
import HigherRankSyntax.Equations
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

/-- A shape with a `Proper` instance bundled — the category object
type for `SyntaxMonad`. -/
@[ext] structure PShape (C : Carrier) : Type 1 where
  /-- The underlying telescope. -/
  tele : Shape C
  /-- The structural-ops instance for the telescope. -/
  proper : Proper tele

/-- Auto-synthesise `[Proper Γ.tele]` from `Γ : PShape C`. -/
instance (C : Carrier) (Γ : PShape C) : Proper Γ.tele := Γ.proper

/-- Category structure on `PShape C` with renamings between underlying
telescopes as morphisms. -/
instance ShapeCat (C : Carrier) : Category (PShape C) where
  Hom Γ Δ := Γ.tele →ʳ Δ.tele
  id Γ := Renaming.id Γ.tele
  comp f g := g ∘ʳʳ f

/-- The arity-indexed family category: a wrapper around `C.Arity → Type` so we can put
a `Category` instance on it without conflicting with the global `Type → Type` setup. -/
@[ext] structure ArityFunc (C : Carrier) where
  toFun : C.Arity → Type

instance (C : Carrier) : CoeFun (ArityFunc C) (fun _ => C.Arity → Type) :=
  ⟨ArityFunc.toFun⟩

instance (C : Carrier) : Category (ArityFunc C) where
  Hom f g := ∀ α, f α → g α
  id _ := fun _ x => x
  comp f g := fun α x => g α (f α x)

/-- The "slots" functor: shape `Γ ↦ α ↦ Γ.tele ∋ α`. -/
def J (C : Carrier) : PShape C ⥤ ArityFunc C where
  obj Γ := ⟨fun α => Γ.tele ∋ α⟩
  map {Γ Δ} (ρ : Γ.tele →ʳ Δ.tele) := fun _ p => ρ p

/-- The "expressions" functor: shape `Γ ↦ α ↦ Expr (Γ.tele ∷ α)`. -/
def T (C : Carrier) : PShape C ⥤ ArityFunc C where

  obj Γ := ⟨fun α => Expr (Γ.tele ∷ α)⟩

  map {Γ Δ} (ρ : Γ.tele →ʳ Δ.tele) := fun α e => ⟦ ρ ⇑ʳ α ⟧ʳ e

  map_id Γ := by
    funext α e
    show ⟦ (𝟙ʳ : Γ.tele →ʳ Γ.tele) ⇑ʳ α ⟧ʳ e = e
    rw [Renaming.extend_id]
    apply Renaming.actExpr.map_id

  map_comp {Γ Δ Ξ} (ρ : Γ.tele →ʳ Δ.tele) (σ : Δ.tele →ʳ Ξ.tele) := by
    funext α e
    show ⟦ (σ ∘ʳʳ ρ) ⇑ʳ α ⟧ʳ e = ⟦ σ ⇑ʳ α ⟧ʳ (⟦ ρ ⇑ʳ α ⟧ʳ e)
    rw [Renaming.extend_comp]
    apply Renaming.actExpr.map_comp

/-- The relative monad of the syntax. -/
def SyntaxMonad (C : Carrier) : RelativeMonad (J C) where

  map := (T C).obj

  η Γ _ := Expr.η

  lift {Γ Δ} f α e :=
    Subst.act @f (Γ := Shape.nil) ⌊α⌋ e

  unit_right := by
    intro Γ
    funext α e
    apply Subst.act_id

  unit_left := by
    intro Γ Δ f
    funext α p
    symm
    apply Subst.act_η

  comp_lift := by
    intro Γ Δ Ξ f g
    funext α e
    apply Subst.act_comp
