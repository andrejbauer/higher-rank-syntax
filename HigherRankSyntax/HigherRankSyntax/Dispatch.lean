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
theorem threewayOn {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
    {α : C.Arity} {motive : Γ ⋈ Δ ⋈ Ξ ∋ α → Prop}
    (right : (z : Ξ ∋ α) → motive (C.inl z))
    (middle : (z : Δ ∋ α) → motive (C.inr (C.inl z)))
    (left : (z : Γ ∋ α) → motive (C.inr (C.inr z)))
  (x : Γ ⋈ Δ ⋈ Ξ ∋ α) : motive x
  := by
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

/-! ## Computation rules for `Subst.act` on a classified head -/

/-- `σ.act` on a current-depth head. -/
theorem act_right {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity)
    {α} (x : Φ ∋ α) (args : Expr.Args (Γ ⋈ Δ ⋈ Φ) α) :
  σ.act Φ (.ap (C.inl x) args)
    = .ap (C.inl x) (fun {_} j => σ.act (Φ ⋈ _) (args j))
  := by
  conv_lhs => unfold Subst.act
  simp

/-- `σ.act` on a substitution-domain head fires the instantiation. -/
theorem act_left_right {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity) {α} (y : Δ ∋ α)
    (args : Expr.Args (Γ ⋈ Δ ⋈ Φ) α) :
  σ.act Φ (.ap (C.inr (C.inl y)) args)
    = ⟦ (fun {_} i => σ.act (Φ ⋈ _) (args i)) ⟧ˢ (σ y)
  := by
  conv_lhs => unfold Subst.act
  simp

/-- `σ.act` on a prefix head rebuilds the head. -/
theorem act_left {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity)
    {α} (z : Γ ∋ α)
    (args : Expr.Args (Γ ⋈ Δ ⋈ Φ) α) :
  σ.act Φ (.ap (C.inr (C.inr z)) args)
    = .ap (C.inr (C.inr z)) (fun {_} j => σ.act (Φ ⋈ _) (args j))
  := by
  conv_lhs => unfold Subst.act
  simp
