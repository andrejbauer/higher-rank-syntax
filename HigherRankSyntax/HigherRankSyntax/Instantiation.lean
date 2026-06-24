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
theorem act_η_right {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity)
    {α} (x : Φ ∋ α) :
  σ.act (Φ ⋈ α)
      ((Expr.η (C.inr x) : Expr ((Γ ⋈ Δ ⋈ Φ) ⋈ α)) :
        Expr (Γ ⋈ Δ ⋈ (Φ ⋈ α)))
    =
      ((Expr.η (C.inr x) : Expr ((Γ ⋈ Ξ ⋈ Φ) ⋈ α)) :
        Expr (Γ ⋈ Ξ ⋈ (Φ ⋈ α)))
  := by
  rw [Expr.η.eq_1]
  rw [← C.inr_inl]
  trans
  · exact act_right σ (Φ ⋈ α) (C.inl x)
      (fun ⦃Ω⦄ i => (Expr.η (C.inr i) : Expr ((Γ ⋈ Δ ⋈ Φ ⋈ α) ⋈ Ω)))
  · rw [Expr.η.eq_1]
    rw [← C.inr_inl]
    congr 1
    funext Ω i
    rw [← C.inr_inr]
    rw [← C.inr_inr]
    exact act_η_right σ (Φ ⋈ α) (x := C.inr i)
termination_by α
decreasing_by exact ⟨i⟩

/-- An η-substitution acts as the identity, given β-for-η at every domain-slot
arity (`hη`). -/
theorem act_idOfη {A : Type} {C : Carrier A} {Γ Δ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Δ))
    (hσ : ∀ {β} (z : Δ ∋ β), σ z = Expr.η (C.inr z))
    (hη : ∀ {β} (_ : Δ ∋ β) {Θ Ξ : C.Arity}
            (ι : Subst β (Θ ⋈ Ξ)) (x : Θ ∋ β),
            ⟦ ι ⟧ˢ ((Expr.η x : Expr (Θ ⋈ β)) : Expr (Θ ⋈ β ⋈ 1))
              =
            ((.ap (C.inl x) (fun ⦃_⦄ i => ι i) : Expr (Θ ⋈ Ξ)) :
              Expr (Θ ⋈ Ξ ⋈ 1)))
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
      exact act_idOfη σ hσ hη (Φ ⋈ Ω) (args i)
    case middle =>
      rw [act_left_right, hσ]
      trans
      · exact hη z _ (C.inr z)
      · congr 1
        funext Ω i
        exact act_idOfη σ hσ hη (Φ ⋈ Ω) (args i)
    case left =>
      rw [act_left]
      congr 1
      funext Ω i
      exact act_idOfη σ hσ hη (Φ ⋈ Ω) (args i)
termination_by (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args _

mutual

/-- β-for-η: instantiating the η-expansion of a non-substituted variable exposes
the kit's positions. -/
theorem act_inst_η {A : Type} {C : Carrier A} {Γ Ξ : C.Arity}
    {α} (ι : Subst α (Γ ⋈ Ξ)) (x : Γ ∋ α) :
  ⟦ ι ⟧ˢ ((Expr.η x : Expr (Γ ⋈ α)) : Expr (Γ ⋈ α ⋈ 1))
    =
      ((.ap (C.inl x) (fun ⦃_⦄ i => ι i) : Expr (Γ ⋈ Ξ)) :
        Expr (Γ ⋈ Ξ ⋈ 1))
  := by
  rw [Expr.η.eq_1]
  rw [← C.unit_right (Γ ⋈ α) (C.inl x)]
  trans
  · exact act_left ι 1 x
      (fun ⦃Ω⦄ i =>
        ((Expr.η (C.inr i) : Expr ((Γ ⋈ α) ⋈ Ω)) :
          Expr ((Γ ⋈ α ⋈ 1) ⋈ Ω)))
  · rw [C.unit_right (Γ ⋈ Ξ) (C.inl x)]
    congr 1
    funext β j
    rw [Expr.η.eq_1]
    trans
    · exact act_left_right ι (1 ⋈ β) j
        (fun ⦃Ω⦄ k =>
          ((Expr.η (C.inr k) : Expr (((Γ ⋈ α) ⋈ β) ⋈ Ω)) :
            Expr ((Γ ⋈ α ⋈ (1 ⋈ β)) ⋈ Ω)))
    · conv => rhs; rw [← act_inst_id β (Γ ⋈ Ξ) 1 (ι j)]
      congr 1
      funext Ω k
      exact act_η_right ι β (x := k)
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
