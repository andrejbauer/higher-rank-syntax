import HigherRankSyntax.Dispatch

/-!
# The substitution commuting square

`act_interchange` states that acting by `σ` commutes with instantiating a
substitution `κ` (pushed forward along `σ`).  It is the engine of `act_comp`
(comp_lift).  `act_interchange_lift` is the one-binder companion produced when
`σ` fires on a domain head.
-/

/-- The one-binder instantiation built from a family of arguments. -/
abbrev instOne {C : Carrier} {Γ : Shape C} (α : C.Arity) (Ξ : Shape C)
    (f : (i : C.Binder α) → Expr (Γ ⋈ Ξ ∷ i.arity)) : Subst C ⌊α⌋ (Γ ⋈ Ξ) :=
  (fun | .here i => f i)

/-- Push `κ` forward along `σ`: `(pushforward σ κ) x = σ.act (κ x)` at the
passive depth determined by the filler. -/
abbrev pushforward {C : Carrier} {Γ Δ Ξ Θ Ω : Shape C}
    [Proper Δ] [Proper Ξ] [Proper Ω] [Proper Θ]
    (σ : Subst C Δ (Γ ⋈ Ξ)) (κ : Subst C Θ (Γ ⋈ Δ ⋈ Ω)) :
    Subst C Θ (Γ ⋈ Ξ ⋈ Ω) :=
  fun {β} x => σ.act (Ω ∷ β) (κ x)

/-- **`act_interchange`** — acting by `θ` commutes with instantiating `κ`:
acting on `⟦κ⟧ e` equals instantiating by the pushed-forward `κ` after acting on
`e`. -/
theorem act_interchange {C : Carrier} {Γ Θ Ξ Ψ Ω : Shape C}
    [Proper Θ] [Proper Ξ] [Proper Ψ] [Proper Ω]
    (θ : Subst C Θ (Γ ⋈ Ξ))
    (κ : Subst C Ψ (Γ ⋈ Θ ⋈ Ω))
    (e : Expr (Γ ⋈ Θ ⋈ Ψ)) :
  θ.act Ω (⟦ κ ⟧ˢ e) = ⟦ pushforward θ κ ⟧ˢ (θ.act Ψ e)
  := sorry

/-- **`act_interchange_lift`** — the one-binder companion: instantiating a freshly
opened `β`-binder and then applying `κ` equals pushing `κ` into each filler. -/
theorem act_interchange_lift {C : Carrier} {Γ Φ Ψ Ω : Shape C}
    [Proper Φ] [Proper Ψ] [Proper Ω]
    {υ : List C.Arity}
    (hΨ : Proper (Φ ⋈ Ψ)) (hΩ : Proper (Φ ⋈ Ω))
    (cohΨ : Proper.AppendCoherence hΨ) (cohΩ : Proper.AppendCoherence hΩ)
    (κ : Subst C Ψ (Γ ⋈ Φ ⋈ Ω))
    {β : C.Arity} (χ : List C.Arity)
    (η : (j : C.Binder β) → Expr (Γ ⋈ Φ ⋈ Ψ ⋈ Tele.ofList υ ∷ j.arity))
    (e : Expr (Γ ∷ β ⋈ Tele.ofList χ)) :
  κ.act (Tele.ofList υ ⋈ Tele.ofList χ)
      (Subst.act (instOne β (Φ ⋈ Ψ ⋈ Tele.ofList υ) η) (Tele.ofList χ) e)
    = Subst.act (instOne β (Φ ⋈ Ω ⋈ Tele.ofList υ)
        (fun j => κ.act (Tele.ofList υ ∷ j.arity) (η j))) (Tele.ofList χ) e
  := sorry
