import HigherRankSyntax.Dispatch
import Batteries.Tactic.Trans

/-!
# The substitution commuting square

`act_interchange` states that acting by `σ` commutes with instantiating a
substitution `κ` (pushed forward along `σ`).  It is the engine of `act_comp`
(comp_lift).  `act_interchange_lift` is the one-binder companion produced when
`σ` fires on a domain head.
-/

/-- Push `κ` forward along `σ`: `(pushforward σ κ) x = σ.act (κ x)` at the
passive depth determined by the filler. -/
abbrev pushforward {C : Carrier} {Γ Δ Ξ Θ Ω : Shape C}
    [Proper Δ] [Proper Ξ] [Proper Ω] [Proper Θ]
    (σ : Subst Δ (Γ ⋈ Ξ)) (κ : Subst Θ (Γ ⋈ Δ ⋈ Ω)) :
    Subst Θ (Γ ⋈ Ξ ⋈ Ω) :=
  fun {β} x => σ.act (Ω ∷ β) (κ x)

attribute [local instance] Proper.compose
-- set_option pp.explicit true
/-- **`act_interchange`** — acting by `θ` commutes with instantiating `κ`:
acting on `κ.act Φ e` equals instantiating by the pushed-forward `κ` after acting
on `e`.  `Φ` is the depth of opened binders, grown by the recursion. -/
theorem act_interchange {C : Carrier} {Γ Θ Ξ Ψ Ω : Shape C}
    [Proper Θ] [Proper Ξ] [Proper Ψ] [Proper Ω]
    (θ : Subst Θ (Γ ⋈ Ξ))
    (κ : Subst Ψ (Γ ⋈ Θ ⋈ Ω))
    (Φ : Shape C) [Proper Φ]
    (e : Expr (Γ ⋈ Θ ⋈ Ψ ⋈ Φ)) :
  θ.act (Ω ⋈ Φ) (κ.act Φ e) = Subst.act (pushforward θ κ) Φ (θ.act (Ψ ⋈ Φ) e)
  := by
  match e with
  | .ap (α := γ) x args =>
    head_cases x with z
    case right => sorry
    case middle => sorry
    case left => sorry
