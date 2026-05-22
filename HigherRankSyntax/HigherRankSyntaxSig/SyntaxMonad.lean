import HigherRankSyntaxSig.Subst
import HigherRankSyntaxSig.RelativeMonad.Basic

/-!
# Syntax as a relative monad

`SyntaxMonad C` packages `Expr` over a carrier `C` as a relative monad over the
"slots" functor `J : Shape C ⥤ ArityFunc C`, with `T Γ α = Expr (Γ ⋈ α)`.

The bridge between Kleisli maps and `Subst` uses two structural renamings to
identify `Γ` with `[] ⋈* Γ = Γ ++ []` (propositionally equal, not definitionally).
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

/-- Wrap a Kleisli map as a `Subst` with empty `pre`. -/
def toSubst {C : Carrier} {Γ Δ : Shape C} (f : (J C).obj Γ ⟶ (T C).obj Δ) : Subst C where
  pre := []
  dom := Γ
  cod := Δ
  sub {β} p :=
    cast (congrArg (fun X : Shape C => Expr (X ⋈ β)) (List.append_nil Δ).symm) (f β p)

/-- Unwrap a `Subst` as a Kleisli map on its source/target shapes.  Pre-slots become
η-expansions of their weakened position in the target; dom-slots use `σ.sub`. -/
def fromSubst {C : Carrier} (σ : Subst C) :
    (J C).obj (σ.pre ⋈* σ.dom) ⟶ (T C).obj (σ.pre ⋈* σ.cod) :=
  fun α p =>
    match classifyDom σ.pre σ.dom p with
    | PreOrDom.pre q => ⟦ (σ.pre ↪ʳ* σ.cod) ⇑ʳ α ⟧ʳ (Expr.η q)
    | PreOrDom.dom q => σ.sub q

/-- The relative monad of the syntax. -/
def SyntaxMonad (C : Carrier) : RelativeMonad (J C) where
  map := (T C).obj
  η Γ := fun _ p => Expr.η p
  lift {Γ Δ} f := fun α e =>
    let σ := toSubst f
    let e' : Expr ((σ.pre ⋈* σ.dom) ⋈* [α]) :=
      cast (congrArg (fun X : Shape C => Expr (X ⋈ α)) (List.append_nil Γ).symm) e
    let r := σ.act [α] e'
    cast (congrArg (fun X : Shape C => Expr (X ⋈ α)) (List.append_nil Δ)) r
  unit_right := by
    intro Γ
    funext α e
    sorry
  unit_left := by
    intro Γ Δ f
    funext α p
    sorry
  comp_lift := sorry
