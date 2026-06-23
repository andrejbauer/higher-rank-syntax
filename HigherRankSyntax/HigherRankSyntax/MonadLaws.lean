import HigherRankSyntax.Instantiation
import HigherRankSyntax.Interchange
import Batteries.Tactic.Trans

/-!
# The three relative-monad laws for `Subst.act`

* `act_id` — the identity substitution acts as the identity (unit_right).
* `act_η` — acting on an η-expansion applies the substitution (unit_left).
* `act_comp` — action by a composite factors (comp_lift).
-/

/-- **`act_id`** — the identity substitution acts as the identity (unit_right). -/
theorem act_id {C : Carrier} (Γ : Shape C) [Proper Γ] (Φ : Shape C) [Proper Φ]
    (e : Expr (Γ ⋈ Φ)) :
  Subst.act (Subst.id Γ) (Γ := Shape.nil) Φ e = e
  := act_idOfη (Γ := Shape.nil) (Subst.id Γ)
       (fun z => by rw [Proper.inr_nil_id]; rfl)
       (fun _ => act_inst_η) Φ e

/-- **`act_η`** — acting on an η-expansion reduces to applying `σ` (unit_left). -/
theorem act_η {C : Carrier} {Δ Ξ : Shape C} [Proper Δ] [Proper Ξ]
    (σ : Subst Δ Ξ) (α : C.Arity) (x : Δ ∋ α) :
  σ.act (Γ := Shape.nil) ⌊α⌋ (.η x) = σ x
  := by
  rw [Expr.η.eq_1]
  obtain ⟨y, rfl⟩ | ⟨z, _⟩ := Proper.cover Shape.nil x
  · trans
    · exact act_left_right (Γ := Shape.nil) σ ⌊α⌋ y (fun i => Expr.η (.here i))
    · rw [Proper.inr_nil_id]
      conv => rhs; rw [← act_inst_id α Ξ Shape.nil (σ y)]
      congr 1
      funext _ q
      cases q with
      | here k => exact act_η_right (Γ := Shape.nil) σ ⌊α⌋ (x := .here k)
      | there w => nomatch w
  · nomatch z

/-- **`act_comp`** — action by a composite factors (comp_lift). -/
theorem act_comp {C : Carrier} {Γ Δ Θ Ξ : Shape C} [Proper Δ] [Proper Θ] [Proper Ξ]
    (σ : Subst Δ (Γ ⋈ Θ)) (θ : Subst Θ (Γ ⋈ Ξ)) (Φ : Shape C) [Proper Φ]
    (e : Expr (Γ ⋈ Δ ⋈ Φ)) :
  Subst.act (Subst.comp σ θ) Φ e = θ.act Φ (σ.act Φ e)
  := by
  match e with
  | .ap (α := β) x args =>
    head_cases x with z
    case right =>
      simp only [act_right]
      congr 1; funext i; exact act_comp σ θ (Φ ∷ i.arity) (args i)
    case middle =>
      rw [act_left_right, act_left_right, act_interchange]
      congr 1
      funext _ q
      cases q with
      | here i => exact act_comp σ θ (Φ ∷ i.arity) (args i)
      | there w => nomatch w
    case left =>
      simp only [act_left]
      congr 1; funext i; exact act_comp σ θ (Φ ∷ i.arity) (args i)
termination_by (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args _
