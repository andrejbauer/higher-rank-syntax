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
    (Φ : C.Arity) {α} (x : Φ ∋ α) :
  σ.act (Φ ⋈ α) ((Expr.η (C.inl x) : Expr ((Γ ⋈ Δ ⋈ Φ) ⋈ α)))
    = ((Expr.η (C.inl x) : Expr ((Γ ⋈ Ξ ⋈ Φ) ⋈ α)))
  := by
  rw [Expr.η.eq_1, C.inr_inl]
  trans
  · apply act_right
  · rw [Expr.η.eq_1, C.inr_inl]
    congr 1
    funext Ω i
    rw [C.inl_inl]
    conv => rhs; rw [C.inl_inl]
    apply act_η_right
termination_by α
decreasing_by exact ⟨i⟩

mutual

/-- An η-substitution acts as the identity. -/
theorem act_idOfη
    {Γ Δ : C.Arity} (σ : Subst Δ (Γ ⋈ Δ))
    (hσ : ∀ {β} (z : Δ ∋ β), σ z = Expr.η (C.inl z))
    (Φ : C.Arity) (e : Expr (Γ ⋈ Δ ⋈ Φ)) :
  Subst.act σ Φ e = e
  := by
  match e with
  | .ap (α := β) x args =>
    head_cases x with z
    case right =>
      rw [act_right]
      congr 1
      funext Ω i
      apply act_idOfη σ hσ
    case middle =>
      rw [act_left_right, hσ]
      trans
      · apply act_inst_η
      · congr 1
        funext Ω i
        apply act_idOfη σ hσ
    case left =>
      rw [act_left]
      congr 1
      funext Ω i
      apply act_idOfη σ hσ
termination_by (Δ, (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ))
decreasing_by
  all_goals
    first
    | exact Prod.Lex.left _ _ ⟨z⟩
    | exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)

/-- β-for-η: instantiating the η-expansion of a non-substituted variable exposes
the kit's positions. -/
theorem act_inst_η
    {Γ Ξ : C.Arity} {α} (ι : Subst α (Γ ⋈ Ξ)) (x : Γ ∋ α) :
  ⟦ ι ⟧ˢ ((Expr.η x : Expr (Γ ⋈ α)))
    = ((.ap (C.inr x) (fun ⦃_⦄ i => ι i) : Expr (Γ ⋈ Ξ)))
  := by
  rw [Expr.η.eq_1, ← C.unit_left (Γ ⋈ α) (C.inr x)]
  trans
  · apply act_left
  · rw [C.unit_left (Γ ⋈ Ξ) (C.inr x)]
    congr 1
    funext β j
    rw [Expr.η.eq_1]
    trans
    · apply act_left_right
    · nth_rewrite 2 [← act_inst_id β (Γ ⋈ Ξ) 1 (ι j)]
      congr 1
      funext Ω k
      apply act_η_right
termination_by (α, (⟨Γ ⋈ α, Expr.η x⟩ : Σ Γ : C.Arity, Expr Γ))
decreasing_by exact Prod.Lex.left _ _ ⟨j⟩

/-- The identity instantiation acts as the identity. -/
theorem act_inst_id
    (α : C.Arity) (Γ : C.Arity)
    (Φ : C.Arity) (e : Expr (Γ ⋈ α ⋈ Φ)) :
  Subst.act (Subst.instId Γ α) Φ e = e
  := by
  match e with
  | .ap (α := β) x args =>
    head_cases x with z
    case right =>
      rw [act_right]
      congr 1
      funext Ω i
      apply act_inst_id
    case middle =>
      rw [act_left_right, Subst.instId]
      trans
      · apply act_inst_η
      · congr 1
        funext Ω i
        apply act_inst_id
    case left =>
      rw [act_left]
      congr 1
      funext Ω i
      apply act_inst_id
termination_by (α, (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ))
decreasing_by
  all_goals
    first
    | exact Prod.Lex.left _ _ ⟨z⟩
    | exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)

end
