import HigherRankSyntax.Subst

/-!
# Head dispatch and computation rules for `Subst.act`

`threewayOn` classifies an application head by its origin; the `head_cases` macro
drives a proof through that split; the `act_ap_*` lemmas are the one-step
computation rules each branch uses to fire `Subst.act`.
-/

/-- Slot eliminator for `Γ ⋈ Δ ⋈ Ξ`: split a head slot by its origin — current
depth `Ξ` (`right`), substitution domain `Δ` (`middle`), or prefix `Γ` (`left`). -/
@[elab_as_elim]
theorem threewayOn {C : Carrier} {Γ Δ Ξ : Shape C} [Proper Δ] [Proper Ξ]
    {α : C.Arity} {motive : Γ ⋈ Δ ⋈ Ξ ∋ α → Prop}
    (right : (z : Ξ ∋ α) → motive (ι₂ z))
    (middle : (z : Δ ∋ α) → motive (ι₁ (ι₂ z)))
    (left : (z : Γ ∋ α) → motive (ι₁ (ι₁ z)))
    (x : Γ ⋈ Δ ⋈ Ξ ∋ α) : motive x := by
  obtain ⟨y, rfl⟩ := Subst.isReinject x
  cases y with
  | right z => exact right z
  | middle z => exact middle z
  | left z => exact left z

/-- Split a head `x` into its three origin cases `right`/`middle`/`left`, binding
the classified slot as `z`.  The decomposition is read off the goal; `using Γ`
pins the prefix when it would collapse (e.g. an empty prefix). -/
macro "head_cases " x:term " with " z:ident : tactic =>
  `(tactic| refine threewayOn (fun $z => ?right) (fun $z => ?middle) (fun $z => ?left) $x)

/-- `head_cases … using Γ` — variant pinning the prefix `Γ`. -/
macro "head_cases " x:term " with " z:ident " using " pre:term : tactic =>
  `(tactic| refine threewayOn (Γ := $pre) (fun $z => ?right) (fun $z => ?middle) (fun $z => ?left) $x)

/-! ## Computation rules for `Subst.act` on a classified head -/

/-- `σ.act` on a current-depth head. -/
theorem act_ap_right {C : Carrier} {Γ Δ Ξ : Shape C} [Proper Δ] [Proper Ξ]
    (σ : Subst C Δ (Γ ⋈ Ξ)) (Φ : Shape C) [Proper Φ]
    {α} (x : Φ ∋ α)
    (args : (i : C.Binder α) → Expr (Γ ⋈ Δ ⋈ Φ ∷ i.arity)) :
  σ.act Φ (.ap (ι₂ x) args) = .ap (ι₂ x) (fun j => σ.act (Φ ∷ j.arity) (args j))
  := by
  conv => lhs; unfold Subst.act
  rw [Subst.threeway_inr]

/-- `σ.act` on a substitution-domain head fires the instantiation. -/
theorem act_ap_middle {C : Carrier} {Γ Δ Ξ : Shape C} [Proper Δ] [Proper Ξ]
    (σ : Subst C Δ (Γ ⋈ Ξ)) (Φ : Shape C) [Proper Φ]
    {α} (y : Δ ∋ α)
    (args : (i : C.Binder α) → Expr (Γ ⋈ Δ ⋈ Φ ∷ i.arity)) :
  σ.act Φ (.ap (ι₁ (ι₂ y)) args)
    = ⟦ ((fun | .here i => σ.act (Φ ∷ i.arity) (args i)) : Subst C ⌊α⌋ (Γ ⋈ Ξ ⋈ Φ)) ⟧ˢ (σ y)
  := by
  conv => lhs; unfold Subst.act
  rw [Subst.threeway_inl_dom]
  rfl

/-- `σ.act` on a prefix head rebuilds the head. -/
theorem act_ap_left {C : Carrier} {Γ Δ Ξ : Shape C} [Proper Δ] [Proper Ξ]
    (σ : Subst C Δ (Γ ⋈ Ξ)) (Φ : Shape C) [Proper Φ]
    {α} (z : Γ ∋ α)
    (args : (i : C.Binder α) → Expr (Γ ⋈ Δ ⋈ Φ ∷ i.arity)) :
  σ.act Φ (.ap (ι₁ (ι₁ z)) args)
    = .ap (ι₁ (ι₁ z)) (fun j => σ.act (Φ ∷ j.arity) (args j))
  := by
  conv => lhs; unfold Subst.act
  rw [Subst.threeway_inl_pre]
