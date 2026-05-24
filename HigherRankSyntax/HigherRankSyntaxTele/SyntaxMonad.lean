import HigherRankSyntaxTele.Subst
import HigherRankSyntaxTele.Equations
import HigherRankSyntaxTele.RelativeMonad.Basic

/-!
# Syntax as a relative monad

`SyntaxMonad C` packages `Expr` over a carrier `C` as a relative monad over the
"slots" functor `J : Shape C ⥤ ArityFunc C`, with `T Γ α = Expr (Γ ⋈ α)`.

With cons-style telescopes, the Kleisli ↔ Subst bridge is cast-free:
`Shape.nil ⋈* X = X` definitionally, so `lift f` is just `Subst.act (toSubst f)`
at `τ = Shape.nil ⋈ α`.
-/


open CategoryTheory

/-- Category structure on `Shape C` with `Renaming`s as morphisms. -/
instance ShapeCat (C : Carrier) : Category (Shape C) where
  Hom Γ Δ := Γ →ʳ Δ
  id Γ := Renaming.id Γ
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

/-- The "slots" functor: shape `Γ ↦ α ↦ Γ ∋ α`. -/
def J (C : Carrier) : Shape C ⥤ ArityFunc C where
  obj Γ := ⟨fun α => Γ ∋ α⟩
  map {Γ Δ} (ρ : Γ →ʳ Δ) := fun _ p => ρ p

/-- The "expressions" functor: shape `Γ ↦ α ↦ Expr (Γ ⋈ α)`. -/
def T (C : Carrier) : Shape C ⥤ ArityFunc C where
  obj Γ := ⟨fun α => Expr (Γ ⋈ α)⟩
  map {Γ Δ} (ρ : Γ →ʳ Δ) := fun α e => ⟦ ρ ⇑ʳ α ⟧ʳ e
  map_id Γ := by
    funext α e
    show ⟦ (𝟙ʳ : Γ →ʳ Γ) ⇑ʳ α ⟧ʳ e = e
    rw [Renaming.extend_id]
    exact Renaming.actExpr.map_id e
  map_comp {Γ Δ Ε} (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ε) := by
    funext α e
    show ⟦ (σ ∘ʳʳ ρ) ⇑ʳ α ⟧ʳ e = ⟦ σ ⇑ʳ α ⟧ʳ (⟦ ρ ⇑ʳ α ⟧ʳ e)
    rw [Renaming.extend_comp]
    exact Renaming.actExpr.map_comp _ _ e

/-- The relative monad of the syntax. -/
def SyntaxMonad (C : Carrier) : RelativeMonad (J C) where
  map := (T C).obj
  η Γ := fun _ p => Expr.η p
  lift {Γ Δ} f := fun α e =>
    (toSubst (fun {β} p => f β p)).act (CTele.cons α CTele.id) e
  unit_right := by
    intro Γ
    funext α e
    exact Subst.act_id Γ α e
  unit_left := by
    intro Γ Δ f
    funext α p
    exact (Subst.act_η (fun {β} p_inner => f β p_inner) α p).symm
  comp_lift := by
    intro Γ Δ Ε f g
    funext α e
    exact Subst.act_kcomp (fun {β} p => f β p) (fun {β} q => g β q) α e
