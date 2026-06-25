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
theorem act_id {A : Type} {C : Carrier A} (Γ Φ : C.Arity) (e : Expr (Γ ⋈ Φ)) :
  Subst.act (Subst.id Γ) (Γ := 1) Φ e = e
  := act_idOfη (Γ := 1) (Subst.id Γ)
       (fun z => by rw [C.unit_right Γ z]; rfl)
       (fun _ => act_inst_η) Φ e

/-- **`act_η`** — acting on an η-expansion reduces to applying `σ` (unit_left). -/
theorem act_η
    {A : Type} {C : Carrier A} {Δ Ξ : C.Arity}
    (σ : Subst Δ Ξ) (Θ : C.Arity) (x : Δ ∋ Θ) :
  σ.act (Γ := 1) Θ (.η x) = σ x
  := by
  rw [Expr.η.eq_1]
  trans
  · convert act_left_right (Γ := 1) σ Θ x (fun {_} i => Expr.η (C.inl i)) using 2
    · congr 1
      rw [C.unit_right Δ x]
  · calc
      _ = Subst.act (Subst.instId Ξ Θ) 1 (σ x) := by
            congr 1
            funext Ω i
            apply act_η_right
      _ = σ x := by apply act_inst_id

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
