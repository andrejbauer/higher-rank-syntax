import HigherRankSyntax.Subst

/-!
# Head dispatch and computation rules for `Subst.act`

`threewayOn` classifies an application head by its origin; the `head_cases`
macro drives a proof through that split.
-/

variable {A : Type} {C : Carrier A}

/-- Slot eliminator for `Γ ⋈ Δ ⋈ Ξ`: split a head slot by its origin — current
depth `Ξ` (`right`), substitution domain `Δ` (`middle`), or prefix `Γ` (`left`). -/
@[elab_as_elim]
theorem threewayOn {Γ Δ Ξ : C.Arity}
    {α : C.Arity} {τ : C.Ty} {motive : Γ ⋈ Δ ⋈ Ξ ∋[τ] α → Prop}
    (right : (z : Ξ ∋[τ] α) → motive (C.inl z))
    (middle : (z : Δ ∋[τ] α) → motive (C.inr (C.inl z)))
    (left : (z : Γ ∋[τ] α) → motive (C.inr (C.inr z)))
  (x : Γ ⋈ Δ ⋈ Ξ ∋[τ] α) : motive x
  := by
  obtain ⟨y, rfl⟩ := Subst.isReinject x
  cases y with
  | right z => exact right z
  | middle z => exact middle z
  | left z => exact left z

/-- Split a head `x` into its three origin cases `right`/`middle`/`left`, binding
the classified slot as `z`. -/
macro "head_cases " x:term " with " z:ident : tactic =>
  `(tactic| refine threewayOn (fun $z => ?right) (fun $z => ?middle) (fun $z => ?left) $x)

/-! ## Computation rules for `Subst.act` on a classified head -/

/-- `σ.act` on a current-depth head. -/
theorem act_right {Γ Δ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity)
    {α : C.Arity} {τ : C.Ty} (x : Φ ∋[τ] α)
    (args : Expr.Args (Γ ⋈ Δ ⋈ Φ) α) :
  σ.act Φ (.ap (C.inl x) args)
    = .ap (C.inl x) (fun {_} {_} j => σ.act (Φ ⋈ _) (args j))
  := by
  conv_lhs => unfold Subst.act
  simp

/-- `σ.act` on a substitution-domain head. -/
theorem act_middle {Γ Δ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity) {α : C.Arity} {τ : C.Ty}
    (y : Δ ∋[τ] α) (args : Expr.Args (Γ ⋈ Δ ⋈ Φ) α) :
  σ.act Φ (.ap (C.inr (C.inl y)) args)
    = ⟦ (fun {_} {_} i => σ.act (Φ ⋈ _) (args i)) ⟧ˢ (σ y)
  := by
  conv_lhs => unfold Subst.act
  simp

/-- `σ.act` on a prefix head rebuilds the head. -/
theorem act_left {Γ Δ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity)
    {α : C.Arity} {τ : C.Ty} (z : Γ ∋[τ] α)
    (args : Expr.Args (Γ ⋈ Δ ⋈ Φ) α) :
  σ.act Φ (.ap (C.inr (C.inr z)) args)
    = .ap (C.inr (C.inr z)) (fun {_} {_} j => σ.act (Φ ⋈ _) (args j))
  := by
  conv_lhs => unfold Subst.act
  simp
