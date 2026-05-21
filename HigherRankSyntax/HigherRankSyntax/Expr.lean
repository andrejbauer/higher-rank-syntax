import HigherRankSyntax.Shape
import HigherRankSyntax.Renaming

/-!
# Expressions of a higher-rank binding signature

`Expr Γ` is the type of expressions in shape `Γ` over a carrier `C`.  The constructor
`apply` takes an arity-typed head slot `p : Γ ∋ α` and a dependent family of children
indexed by `C.Binder α`, each child living in `Γ` extended by the binder's sub-arity.

`Expr` is the W-type of `Shape ◅ Slot` decorated by the arity index, with the recursive
child's shape index shifted by the action `⋈` — the free relative monad of the decorated
container.
-/


/-- Expressions in shape `Γ` over a carrier `C`. -/
inductive Expr {C : Carrier} : Shape C → Type where
  /-- An application of a head slot `p : Γ ∋ α` to a dependent family of children, one
      per binder of `α`. -/
  | apply : {Γ : Shape C} → {α : C.Arity} → (p : Γ ∋ α) →
            (args : (i : C.Binder α) → Expr (Γ ⋈ i.arity)) → Expr Γ

/-! ## Structural subterm relation

A heterogeneous "one-step child" relation on expressions, packaged as a relation on
`Σ Γ, Expr Γ` so the two sides — which live at different shape indices — share a
homogeneous type. -/

/-- `Expr.Subterm e' e` holds when `e = apply p args` and `e'` is one of its arguments
`args j`. -/
inductive Expr.Subterm {C : Carrier} :
    (Σ Γ : Shape C, Expr Γ) → (Σ Γ : Shape C, Expr Γ) → Prop where
  | of_arg {Γ : Shape C} {α : C.Arity} (p : Γ ∋ α)
      (args : (i : C.Binder α) → Expr (Γ ⋈ i.arity))
      (j : C.Binder α) :
      Expr.Subterm ⟨Γ ⋈ j.arity, args j⟩ ⟨Γ, Expr.apply p args⟩

theorem Expr.Subterm.wf {C : Carrier} : WellFounded (@Expr.Subterm C) := by
  refine ⟨fun ⟨Γ, e⟩ => ?_⟩
  induction e with
  | apply p args ih =>
    refine Acc.intro _ ?_
    rintro ⟨_, _⟩ h
    cases h
    exact ih _

instance Expr.Subterm.wellFoundedRelation {C : Carrier} :
    WellFoundedRelation (Σ Γ : Shape C, Expr Γ) where
  rel := @Expr.Subterm C
  wf := Expr.Subterm.wf

/-! ## J, T, η -/

/-- The variables of arity `α` at `Γ`: alias for `SlotAt Γ α`. -/
abbrev Expr.J {C : Carrier} (Γ : Shape C) (α : C.Arity) : Type := Γ ∋ α

/-- The relative monad's target: expressions with free shape `Γ` under one outer α-binder. -/
abbrev Expr.T {C : Carrier} (Γ : Shape C) (α : C.Arity) : Type := Expr (Γ ⋈ α)

/-- η-expansion: a variable `p : Γ ∋ α` becomes the fully-applied tree
`apply (.there p) (fun i => η (.here i))`, where each binder `i` of `α` recursively
η-expands the bound variable.  Termination descends along the sub-arity relation. -/
def Expr.η {C : Carrier} : {Γ : Shape C} → {α : C.Arity} → (Γ ∋ α) → T Γ α
  | _, α, p => Expr.apply (.there p) (fun i => η (α := i.arity) (.here i))
termination_by Γ α _ => α
decreasing_by exact ⟨_, rfl⟩

/-! ## Renaming action -/

/-- Action of a renaming on an expression. -/
def Renaming.actExpr {C : Carrier} : {Γ Δ : Shape C} → (Γ →ʳ Δ) → Expr Γ → Expr Δ
  | _, _, ρ, .apply p args =>
    Expr.apply (ρ p) (fun i => Renaming.actExpr (ρ ⇑ʳ i.arity) (args i))

/-- Action of a renaming on an expression: `⟦ ρ ⟧ʳ e`. -/
notation:60 "⟦" ρ "⟧ʳ " e:61 => Renaming.actExpr ρ e

/-- Defining equation of `actExpr` on `apply`. -/
@[simp]
theorem Renaming.actExpr_apply {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ)
    {α : C.Arity} (p : Γ ∋ α)
    (args : (i : C.Binder α) → Expr (Γ ⋈ i.arity)) :
    ⟦ ρ ⟧ʳ (Expr.apply p args)
      = Expr.apply (ρ p) (fun i => ⟦ ρ ⇑ʳ i.arity ⟧ʳ (args i)) := rfl

@[simp]
theorem Renaming.actExpr.map_id {C : Carrier} : ∀ {Γ : Shape C} (e : Expr Γ),
    ⟦ 𝟙ʳ ⟧ʳ e = e
  | _, .apply p args => by
    show Expr.apply p (fun i => ⟦ (𝟙ʳ : _ →ʳ _) ⇑ʳ i.arity ⟧ʳ args i)
      = Expr.apply p args
    congr 1
    funext i
    rw [Renaming.extend_id]
    exact Renaming.actExpr.map_id (args i)

@[simp]
theorem Renaming.actExpr.map_comp {C : Carrier} : ∀ {Γ Δ Ε : Shape C}
    (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ε) (e : Expr Γ), ⟦ σ ∘ʳʳ ρ ⟧ʳ e = ⟦ σ ⟧ʳ (⟦ ρ ⟧ʳ e)
  | _, _, _, ρ, σ, .apply p args => by
    show Expr.apply (σ (ρ p)) (fun i => ⟦ (σ ∘ʳʳ ρ) ⇑ʳ i.arity ⟧ʳ args i)
      = Expr.apply (σ (ρ p)) (fun i => ⟦ σ ⇑ʳ i.arity ⟧ʳ (⟦ ρ ⇑ʳ i.arity ⟧ʳ args i))
    congr 1
    funext i
    rw [Renaming.extend_comp]
    exact Renaming.actExpr.map_comp _ _ (args i)

/-! ## J and T as functors -/

/-- Action of a renaming on `J`. -/
def Expr.J.map {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ) {α : C.Arity}
    (v : J Γ α) : J Δ α := ρ v

@[simp] theorem Expr.J.map_id {C : Carrier} {Γ : Shape C} {α : C.Arity}
    (v : J Γ α) : J.map 𝟙ʳ v = v := rfl

@[simp] theorem Expr.J.map_comp {C : Carrier} {Γ Δ Ε : Shape C}
    (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ε) {α : C.Arity} (v : J Γ α) :
    J.map (σ ∘ʳʳ ρ) v = J.map σ (J.map ρ v) := rfl

/-- Action of a renaming on `T`. -/
def Expr.T.map {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ) (α : C.Arity)
    (e : T Γ α) : T Δ α := ⟦ ρ ⇑ʳ α ⟧ʳ e

@[simp] theorem Expr.T.map_id {C : Carrier} {Γ : Shape C} (α : C.Arity) (e : T Γ α) :
    T.map 𝟙ʳ α e = e := by
  show ⟦ (𝟙ʳ : Γ →ʳ Γ) ⇑ʳ α ⟧ʳ e = e
  rw [Renaming.extend_id]
  exact Renaming.actExpr.map_id e

@[simp] theorem Expr.T.map_comp {C : Carrier} {Γ Δ Ε : Shape C}
    (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ε) (α : C.Arity) (e : T Γ α) :
    T.map (σ ∘ʳʳ ρ) α e = T.map σ α (T.map ρ α e) := by
  show ⟦ (σ ∘ʳʳ ρ) ⇑ʳ α ⟧ʳ e = ⟦ σ ⇑ʳ α ⟧ʳ (⟦ ρ ⇑ʳ α ⟧ʳ e)
  rw [Renaming.extend_comp]
  exact Renaming.actExpr.map_comp _ _ e

/-- η is natural: `T.map ρ ∘ η = η ∘ J.map ρ`. -/
@[simp] theorem Expr.T.map_η {C : Carrier} : ∀ {Γ Δ : Shape C} (ρ : Γ →ʳ Δ) (α : C.Arity) (v : J Γ α),
  T.map ρ α (η v) = η (J.map ρ v)
  | _, _, ρ, α, p => by
    unfold η T.map J.map
    rw [Renaming.actExpr]
    congr 1
    funext i
    have ih := T.map_η (ρ ⇑ʳ α) i.arity (SlotAt.here i)
    unfold T.map J.map at ih
    exact ih
termination_by _ _ _ α _ => α
decreasing_by exact ⟨_, rfl⟩

/-- `actExpr`-form restatement of `T.map_η`: `⟦ ρ ⇑ʳ α ⟧ʳ` commutes with `η`. -/
@[simp] theorem Renaming.actExpr_η {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ)
    (α : C.Arity) (v : Expr.J Γ α) :
    ⟦ ρ ⇑ʳ α ⟧ʳ (Expr.η v) = Expr.η (ρ v) :=
  Expr.T.map_η ρ α v
