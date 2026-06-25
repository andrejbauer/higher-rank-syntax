import HigherRankSyntax.Dispatch
import Batteries.Tactic.Trans

/-!
# Instantiation lemmas

η-substitutions and one-position instantiation: `act_η_right` (acting on a
current-depth η reproduces it), `act_idOfη` (an η-substitution acts as the
identity), and the mutual `act_inst_η` (β-for-η) / `act_inst_id` (the identity
instantiation acts as the identity).
-/

/-- Acting on the η-expansion of a current-depth slot reproduces the η. -/
theorem act_η_right
    {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity) {α} (x : Φ ∋ α) :
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

/-- An η-substitution acts as the identity, given β-for-η at every domain-slot
arity (`hη`). -/
theorem act_idOfη {A : Type} {C : Carrier A} {Γ Δ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Δ))
    (hσ : ∀ {β} (z : Δ ∋ β), σ z = Expr.η (C.inl z))
    (hη : ∀ {β} (_ : Δ ∋ β) {Θ Ξ : C.Arity}
              (ι : Subst β (Θ ⋈ Ξ)) (x : Θ ∋ β),
            ⟦ ι ⟧ˢ ((Expr.η x : Expr (Θ ⋈ β)))
              = (.ap (C.inr x) (fun ⦃_⦄ i => ι i) : Expr (Θ ⋈ Ξ)))
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
      apply act_idOfη σ hσ hη
    case middle =>
      rw [act_left_right, hσ]
      trans
      · exact hη z _ (C.inl z)
      · congr 1
        funext Ω i
        apply act_idOfη σ hσ hη
    case left =>
      rw [act_left]
      congr 1
      funext Ω i
      apply act_idOfη σ hσ hη
termination_by (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args _

mutual

/-- β-for-η: instantiating the η-expansion of a non-substituted variable exposes
the kit's positions. -/
theorem act_inst_η {A : Type} {C : Carrier A} {Γ Ξ : C.Arity}
    {α} (ι : Subst α (Γ ⋈ Ξ)) (x : Γ ∋ α) :
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
termination_by α
decreasing_by exact ⟨j⟩

/-- The identity instantiation acts as the identity. -/
theorem act_inst_id {A : Type} {C : Carrier A} (α : C.Arity) (Γ : C.Arity)
    (Φ : C.Arity) (e : Expr (Γ ⋈ α ⋈ Φ)) :
  Subst.act (Subst.instId Γ α) Φ e = e
  := act_idOfη (Subst.instId Γ α)
       (fun _ => rfl)
       (fun {β} z {Θ Ξ} ι x => by
          have _ : Nonempty (α ∋ β) := ⟨z⟩
          exact act_inst_η ι x)
       Φ e
termination_by α
decreasing_by exact ‹Nonempty (_ ∋ _)›

end
