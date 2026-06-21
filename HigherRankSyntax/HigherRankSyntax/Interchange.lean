import HigherRankSyntax.Dispatch
import Batteries.Tactic.Trans
import Mathlib.Tactic.Convert

/-!
# The substitution commuting square

`act_interchange.aux` is the general square: acting by `σ` commutes with
instantiating `κ` (pushed forward along `σ`).  `act_interchange` is its
`Θ = nil`, `Φ = nil` instance, used by `act_comp`.
-/

/-- Push `κ` forward along `σ`: `(pushforward σ κ) x = σ.act (κ x)` at the
passive depth determined by the filler. -/
abbrev pushforward {C : Carrier} {Γ Δ Ξ Θ Ω : Shape C}
    [Proper Δ] [Proper Ξ] [Proper Ω] [Proper Θ]
    (σ : Subst Δ (Γ ⋈ Ξ)) (κ : Subst Θ (Γ ⋈ Δ ⋈ Ω)) :
    Subst Θ (Γ ⋈ Ξ ⋈ Ω) :=
  fun {β} x => σ.act (Ω ∷ β) (κ x)

attribute [local instance] Proper.compose

/-- `Subst.act` does not depend on the chosen `Proper` witness for its depth. -/
theorem Subst.act_irrel {C : Carrier} {Γ Δ Ξ : Shape C} [Proper Δ] [Proper Ξ]
    (σ : Subst Δ (Γ ⋈ Ξ)) {Φ : Shape C} (i i' : Proper Φ) (e : Expr (Γ ⋈ Δ ⋈ Φ)) :
    @Subst.act C Γ Δ Ξ _ _ σ Φ i e = @Subst.act C Γ Δ Ξ _ _ σ Φ i' e
  := by
  haveI := Proper.subsingleton Φ
  rw [Subsingleton.elim i i']

/-- `σ.act` on a head from the suffix telescope `Φ`, injected past an intermediate
telescope `Λ` that `σ` does not touch: the head is rebuilt over the new codomain and
the action descends into the arguments.  Generalizes `act_ap_right` (`Λ = Shape.nil`). -/
theorem act_ap_suffix {C : Carrier} {Γ Δ Ξ : Shape C} [Proper Δ] [Proper Ξ]
    (σ : Subst Δ (Γ ⋈ Ξ)) (Λ Φ : Shape C) [Proper Λ] [Proper Φ]
    {α} (z : Φ ∋ α)
    (args : (i : C.Binder α) → Expr (Γ ⋈ Δ ⋈ Λ ⋈ Φ ∷ i.arity)) :
  σ.act (Λ ⋈ Φ) (Expr.ap (Proper.inr (Γ ⋈ Δ ⋈ Λ) z) args)
    = Expr.ap (Proper.inr (Γ ⋈ Ξ ⋈ Λ) z) (fun j => σ.act (Λ ⋈ (Φ ∷ j.arity)) (args j))
  := by
  sorry

/-- Acting by `σ` commutes with instantiating `κ` (pushed forward along `σ`). -/
theorem act_interchange.aux {C : Carrier} {Γ Δ Ξ Θ Ψ Ω : Shape C}
    [Proper Δ] [Proper Ξ] [Proper Θ] [Proper Ψ] [Proper Ω]
    (σ : Subst Δ (Γ ⋈ Ξ))
    (κ : Subst Ψ (Γ ⋈ Δ ⋈ Θ ⋈ Ω))
    (Φ : Shape C) [Proper Φ]
    (e : Expr (Γ ⋈ Δ ⋈ Θ ⋈ Ψ ⋈ Φ)) :
  σ.act (Θ ⋈ Ω ⋈ Φ) (κ.act Φ e)
    = Subst.act (Γ := Γ ⋈ Ξ ⋈ Θ) (Δ := Ψ) (Ξ := Ω)
        (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ (σ.act (Θ ⋈ Ψ ⋈ Φ) e)
  := by
  match e with
  | .ap (α := β) x args =>
    head_cases x with z
    case right =>             -- z : Φ  (rebuild: both acts pass through)
      rw [act_ap_right]                              -- κ fires (head already matches)
      convert act_ap_suffix σ (Θ ⋈ Ω) Φ z _ using 2
      convert congrArg _ (act_ap_suffix σ (Θ ⋈ Ψ) Φ z args) using 2
      symm
      convert act_ap_right (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω) (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ z _ using 2
      congr 1
      funext i
      exact act_interchange.aux σ κ (Φ ∷ i.arity) (args i)
    case middle =>             -- z : Ψ  (κ fires)
      rw [act_ap_middle]       -- LHS = σ.act (Θ⋈Ω⋈Φ) (⟦argκ⟧ˢ (κ z))
      -- recursive call: interchange σ past argκ on the expr (κ z)
      --   cow : σ.act (Θ⋈Ω⋈Φ) (⟦argκ⟧ˢ (κ z))
      --       = ⟦pushforward σ argκ⟧ˢ (σ.act (Θ⋈Ω⋈⌊β⌋) (κ z))
      -- have cow := act_interchange.aux (Θ := Θ ⋈ Ω) (Ψ := ⌊β⌋) (Ω := Φ) σ
      --   (fun | _, .here i => κ.act (Φ ∷ i.arity) (args i)) Shape.nil (κ z)
      sorry
    case left =>
      head_cases z with w
      case right =>            -- w : Θ  (rebuild: both acts pass through)
        -- recursive call: per-argument interchange
        -- have cow := fun (i : C.Binder β) => act_interchange.aux σ κ (Φ ∷ i.arity) (args i)
        sorry
      case middle =>           -- w : Δ  (σ fires)
        -- recursive call: per-argument interchange (σ-fire likely needs more)
        -- have cow := fun (i : C.Binder β) => act_interchange.aux σ κ (Φ ∷ i.arity) (args i)
        sorry
      case left =>             -- w : Γ  (rebuild: both acts pass through)
        -- recursive call: per-argument interchange
        -- have cow := fun (i : C.Binder β) => act_interchange.aux σ κ (Φ ∷ i.arity) (args i)
        sorry
termination_by (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by
  exact .of_arg x args i

/-- Acting by `θ` commutes with instantiating `κ`: substituting `κ` then acting
by `θ` equals acting by `θ` then substituting the pushed-forward `κ`. -/
theorem act_interchange {C : Carrier} {Γ Θ Ξ Ψ Ω : Shape C}
    [Proper Θ] [Proper Ξ] [Proper Ψ] [Proper Ω]
    (θ : Subst Θ (Γ ⋈ Ξ)) (κ : Subst Ψ (Γ ⋈ Θ ⋈ Ω))
    (e : Expr (Γ ⋈ Θ ⋈ Ψ)) :
  θ.act Ω (κ.act Shape.nil e)
    = Subst.act (pushforward θ κ) Shape.nil (θ.act Ψ e)
  := by
  convert act_interchange.aux (Θ := Shape.nil) θ κ Shape.nil e
  · apply Subsingleton.elim
  · congr <;> apply Subsingleton.elim
