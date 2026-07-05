import HigherRankSyntax.Dispatch
import Batteries.Tactic.Trans

/-!
# Instantiation lemmas

η-substitutions and one-position instantiation: `act_η_right` (acting on a
current-depth η reproduces it), and the mutual `act_idOfη` (an η-substitution
acts as the identity) / `act_inst_η` (β-for-η) / `act_inst_id` (the identity
instantiation acts as the identity).
-/

variable {A : Type} {C : Carrier A}

/-- Acting on the η-expansion of a current-depth slot reproduces the η. -/
theorem act_η_right
    {Γ Δ Ξ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ))
    (Φ : C.Arity) {α : C.Arity} {τ : C.Ty} (x : Φ ∋[τ] α) :
  σ.act (Φ ⋈ α) ((Expr.η (C.inr x) : Expr ((Γ ⋈ Δ ⋈ Φ) ⋈ α) τ))
    = ((Expr.η (C.inr x) : Expr ((Γ ⋈ Ξ ⋈ Φ) ⋈ α) τ))
  := by
  rw [Expr.η.eq_1, ← C.inr_inl]
  trans
  · apply act_right
  · rw [Expr.η.eq_1, ← C.inr_inl]
    congr 1
    funext Ω υ i
    rw [← C.inr_inr]
    conv => rhs; rw [← C.inr_inr]
    apply act_η_right
termination_by α
decreasing_by exact ⟨_, ⟨i⟩⟩

mutual

/-- An η-substitution acts as the identity. -/
theorem act_idOfη
    {Γ Δ : C.Arity} (σ : Subst Δ (Γ ⋈ Δ))
    (hσ : ∀ {β} {τ} (z : Δ ∋[τ] β), σ z = Expr.η (C.inr z))
    (Φ : C.Arity) {τ : C.Ty} (e : Expr (Γ ⋈ Δ ⋈ Φ) τ) :
  Subst.act σ Φ e = e
  := by
  match e with
  | .ap (α := β) x args =>
    head_cases x with z
    case right =>
      rw [act_right]
      congr 1
      funext Ω υ i
      apply act_idOfη σ hσ
    case middle =>
      rw [act_middle, hσ]
      trans
      · apply act_inst_η
      · congr 1
        funext Ω υ i
        apply act_idOfη σ hσ
    case left =>
      rw [act_left]
      congr 1
      funext Ω υ i
      apply act_idOfη σ hσ
termination_by (Δ, (⟨_, _, e⟩ : Σ Γ : C.Arity, Σ τ : C.Ty, Expr Γ τ))
decreasing_by
  all_goals
    first
    | exact Prod.Lex.left _ _ ⟨_, ⟨z⟩⟩
    | exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)

/-- β-for-η: instantiating an η-expansion exposes the substitution arguments. -/
theorem act_inst_η
    {Γ Ξ : C.Arity} {α : C.Arity} {τ : C.Ty}
    (ι : Subst α (Γ ⋈ Ξ)) (x : Γ ∋[τ] α) :
  ⟦ ι ⟧ˢ ((Expr.η x : Expr (Γ ⋈ α) τ))
    = ((.ap (C.inl x) (fun ⦃_⦄ ⦃_⦄ i => ι i) : Expr (Γ ⋈ Ξ) τ))
  := by
  rw [Expr.η.eq_1, ← C.unit_right (Γ ⋈ α) (C.inl x)]
  trans
  · apply act_left
  · rw [C.unit_right (Γ ⋈ Ξ) (C.inl x)]
    congr 1
    funext β υ j
    rw [Expr.η.eq_1]
    trans
    · apply act_middle
    · nth_rewrite 2 [← act_inst_id β (Γ ⋈ Ξ) 1 (ι j)]
      congr 1
      funext Ω ν k
      apply act_η_right
termination_by (α, (⟨Γ ⋈ α, τ, Expr.η x⟩ : Σ Γ : C.Arity, Σ τ : C.Ty, Expr Γ τ))
decreasing_by exact Prod.Lex.left _ _ ⟨_, ⟨j⟩⟩

/-- The identity instantiation acts as the identity. -/
theorem act_inst_id
    (α : C.Arity) (Γ : C.Arity)
    (Φ : C.Arity) {τ : C.Ty} (e : Expr (Γ ⋈ α ⋈ Φ) τ) :
  Subst.act (Subst.instId Γ α) Φ e = e
  := by
  match e with
  | .ap (α := β) x args =>
    head_cases x with z
    case right =>
      rw [act_right]
      congr 1
      funext Ω υ i
      apply act_inst_id
    case middle =>
      rw [act_middle, Subst.instId]
      trans
      · apply act_inst_η
      · congr 1
        funext Ω υ i
        apply act_inst_id
    case left =>
      rw [act_left]
      congr 1
      funext Ω υ i
      apply act_inst_id
termination_by (α, (⟨_, _, e⟩ : Σ Γ : C.Arity, Σ τ : C.Ty, Expr Γ τ))
decreasing_by
  all_goals
    first
    | exact Prod.Lex.left _ _ ⟨_, ⟨z⟩⟩
    | exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)

end
