import HigherRankSyntax.Shape
import HigherRankSyntax.Renaming

/-!
# Expressions of a higher-rank binding signature

`Expr Γ` is the type of expressions in shape `Γ` over a carrier `C`.  The constructor
`ap` takes an arity-typed head slot `p : Γ ∋ α` and a dependent family of children
indexed by `C.Binder α`, each child living in `Γ` extended by the binder's sub-arity.
-/


/-- Expressions in shape `Γ` over a carrier `C`. -/
inductive Expr {C : Carrier} : Shape C → Type where
  /-- An application of a head slot `p : Γ ∋ α` to a dependent family of children, one
      per binder of `α`. -/
  | ap : {Γ : Shape C} → {α : C.Arity} → Γ ∋ α →
         ((i : C.Binder α) → Expr (Γ ∷ i.arity)) → Expr Γ

/-- `Expr.Subterm e' e` holds when `e = ap p args` and `e'` is one of its arguments
`args j`. -/
inductive Expr.Subterm {C : Carrier} :
    (Σ Γ : Shape C, Expr Γ) → (Σ Γ : Shape C, Expr Γ) → Prop where
  | of_arg {Γ : Shape C} {α : C.Arity} (p : Γ ∋ α)
      (args : (i : C.Binder α) → Expr (Γ ∷ i.arity))
      (j : C.Binder α) :
      Expr.Subterm ⟨Γ ∷ j.arity, args j⟩ ⟨Γ, Expr.ap p args⟩

theorem Expr.Subterm.wf {C : Carrier} : WellFounded (@Expr.Subterm C) := by
  refine ⟨fun ⟨Γ, e⟩ => ?_⟩
  induction e with
  | ap p args ih =>
    refine Acc.intro _ ?_
    rintro ⟨_, _⟩ h
    cases h
    exact ih _

instance Expr.Subterm.wellFoundedRelation {C : Carrier} :
    WellFoundedRelation (Σ Γ : Shape C, Expr Γ) where
  rel := @Expr.Subterm C
  wf := Expr.Subterm.wf

/-- The relative monad's target: expressions with free shape `Γ` under one outer α-binder. -/
abbrev Expr.T {C : Carrier} (Γ : Shape C) (α : C.Arity) : Type := Expr (Γ ∷ α)

/-- η-expansion: a variable `p : Γ ∋ α` becomes the fully-applied tree
`ap (.there p) (fun i => η (.here i))`. -/
def Expr.η {C : Carrier} : {Γ : Shape C} → {α : C.Arity} → Γ ∋ α → T Γ α
  | _, α, p => Expr.ap (.there p) (fun i => η (α := i.arity) (.here i))
termination_by Γ α _ => α
decreasing_by exact ⟨_, rfl⟩

/-- Action of a renaming on an expression. -/
def Renaming.actExpr {C : Carrier} : {Γ Δ : Shape C} → (Γ →ʳ Δ) → Expr Γ → Expr Δ
  | _, _, ρ, .ap p args =>
    Expr.ap (ρ p) (fun i => Renaming.actExpr (ρ ⇑ʳ i.arity) (args i))

@[inherit_doc Renaming.actExpr]
notation:60 "⟦" ρ "⟧ʳ " e:61 => Renaming.actExpr ρ e

@[simp]
theorem Renaming.actExpr_ap {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ)
    {α : C.Arity} (p : Γ ∋ α)
    (args : (i : C.Binder α) → Expr (Γ ∷ i.arity)) :
    ⟦ ρ ⟧ʳ (Expr.ap p args)
      = Expr.ap (ρ p) (fun i => ⟦ ρ ⇑ʳ i.arity ⟧ʳ (args i)) := rfl

@[simp]
theorem Renaming.actExpr.map_id {C : Carrier} : ∀ {Γ : Shape C} (e : Expr Γ),
    ⟦ 𝟙ʳ ⟧ʳ e = e
  | _, .ap p args => by
    show Expr.ap p (fun i => ⟦ (𝟙ʳ : _ →ʳ _) ⇑ʳ i.arity ⟧ʳ args i)
      = Expr.ap p args
    congr 1
    funext i
    rw [Renaming.extend_id]
    exact Renaming.actExpr.map_id (args i)

@[simp]
theorem Renaming.actExpr.map_comp {C : Carrier} : ∀ {Γ Δ Ξ : Shape C}
    (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ξ) (e : Expr Γ), ⟦ σ ∘ʳʳ ρ ⟧ʳ e = ⟦ σ ⟧ʳ (⟦ ρ ⟧ʳ e)
  | _, _, _, ρ, σ, .ap p args => by
    show Expr.ap (σ (ρ p)) (fun i => ⟦ (σ ∘ʳʳ ρ) ⇑ʳ i.arity ⟧ʳ args i)
      = Expr.ap (σ (ρ p)) (fun i => ⟦ σ ⇑ʳ i.arity ⟧ʳ (⟦ ρ ⇑ʳ i.arity ⟧ʳ args i))
    congr 1
    funext i
    rw [Renaming.extend_comp]
    exact Renaming.actExpr.map_comp _ _ (args i)
