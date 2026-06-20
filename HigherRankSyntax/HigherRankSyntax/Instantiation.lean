import HigherRankSyntax.Dispatch
import Batteries.Tactic.Trans

/-!
# Instantiation lemmas

η-substitutions and one-binder instantiation: `act_η_right` (acting on a
current-depth η reproduces it), `act_idOfη` (an η-substitution acts as the
identity), and the mutual `act_inst_η` (β-for-η) / `act_inst_id` (the identity
instantiation acts as the identity).
-/

/-- Acting on the η-expansion of a current-depth slot reproduces the η. -/
theorem act_η_right {C : Carrier} {Γ Δ Ξ : Shape C} [Proper Δ] [Proper Ξ]
    (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : Shape C) [Proper Φ]
    {α} (x : Φ ∋ α) :
  σ.act (Φ ∷ α) (.η (ι₂ x)) = .η (ι₂ x)
  := by
  rw [Expr.η.eq_1]
  trans
  · exact act_ap_right σ (Φ ∷ α) (.there x) (fun i => Expr.η (.here i))
  · rw [Expr.η.eq_1]
    congr 1
    funext i
    exact act_η_right σ (Φ ∷ α) (x := .here i)
termination_by α
decreasing_by exact ⟨i, rfl⟩

/-- An η-substitution — one with `σ z = η (ι₂ z)` — acts as the identity, given
β-for-η at every domain-slot arity (`hη`). -/
theorem act_idOfη {C : Carrier} {Γ Δ : Shape C} [Proper Δ]
    (σ : Subst Δ (Γ ⋈ Δ))
    (hσ : ∀ {β} (z : Δ ∋ β), σ z = Expr.η (ι₂ z))
    (hη : ∀ {β} (_ : Δ ∋ β) {Θ Ξ : Shape C} [Proper Ξ]
            (ι : Subst ⌊β⌋ (Θ ⋈ Ξ)) (x : Θ ∋ β),
            ⟦ ι ⟧ˢ (.η x) = .ap (Proper.inl Θ x) (fun i => ι (.here i)))
    (Φ : Shape C) [Proper Φ] (e : Expr (Γ ⋈ Δ ⋈ Φ)) :
  Subst.act σ Φ e = e
  := by
  match e with
  | .ap (α := β) x args =>
    head_cases x with z
    case right => rw [act_ap_right]; congr 1; funext i; exact act_idOfη σ hσ hη (Φ ∷ i.arity) (args i)
    case middle =>
      rw [act_ap_middle, hσ]
      trans
      · exact hη z _ (ι₂ z)
      · congr 1; funext i; exact act_idOfη σ hσ hη (Φ ∷ i.arity) (args i)
    case left => rw [act_ap_left]; congr 1; funext i; exact act_idOfη σ hσ hη (Φ ∷ i.arity) (args i)
termination_by (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args _

mutual

/-- β-for-η: instantiating the η-expansion of a non-substituted variable exposes
the kit's binders. -/
theorem act_inst_η {C : Carrier} {Γ Ξ : Shape C} [Proper Ξ]
    {α} (ι : Subst ⌊α⌋ (Γ ⋈ Ξ)) (x : Γ ∋ α) :
  ⟦ ι ⟧ˢ (.η x) = .ap (Proper.inl Γ x) (fun i => ι (.here i))
  := by
  rw [Expr.η.eq_1]
  trans
  · exact act_ap_left ι Shape.nil x (fun i => Expr.η (.here i))
  · congr 1
    funext j
    rw [Expr.η.eq_1]
    trans
    · exact act_ap_middle ι ⌊j.arity⌋ (.here j) (fun k => Expr.η (.here k))
    · conv => rhs; rw [← act_inst_id j.arity (Γ ⋈ Ξ) Shape.nil (ι (.here j))]
      congr 1
      funext _ q
      cases q with
      | here k => exact act_η_right ι ⌊j.arity⌋ (x := .here k)
      | there w => nomatch w
termination_by α
decreasing_by exact ⟨j, rfl⟩

/-- The identity instantiation acts as the identity. -/
theorem act_inst_id {C : Carrier} (α : C.Arity) (Γ : Shape C) (Φ : Shape C) [Proper Φ]
    (e : Expr (Γ ∷ α ⋈ Φ)) :
  Subst.act (Subst.instId Γ α) Φ e = e
  := act_idOfη (Subst.instId Γ α)
       (fun z => by cases z with | here i => rfl | there w => nomatch w)
       (fun z => by cases z with | here i => exact act_inst_η | there w => nomatch w)
       Φ e
termination_by α
decreasing_by exact ⟨i, rfl⟩

end
