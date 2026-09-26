import HigherRankSyntax.Subst

/-!
# Case analysis on slots of `Γ ⋈ Δ ⋈ Ξ`, and `Subst.act` on each kind of head

`threewayOn` is case analysis on a slot of `Γ ⋈ Δ ⋈ Ξ`: a slot of `Ξ`, of `Δ`, or of
`Γ`; the tactic `head_cases` applies it.  `act_right`, `act_middle` and `act_left`
compute `Subst.act` on an application whose head is in each case.
-/

/-- Case analysis on a slot of `Γ ⋈ Δ ⋈ Ξ`: it is `C.inr z` with `z : Ξ ∋ α`
(`right`), `C.inl (C.inr z)` with `z : Δ ∋ α` (`middle`), or `C.inl (C.inl z)` with
`z : Γ ∋ α` (`left`). -/
@[elab_as_elim]
theorem threewayOn
    {Γ Δ Ξ : C.Arity} {α : C.Arity} {motive : Γ ⋈ Δ ⋈ Ξ ∋ α → Prop}
    (right : (z : Ξ ∋ α) → motive (C.inr z))
    (middle : (z : Δ ∋ α) → motive (C.inl (C.inr z)))
    (left : (z : Γ ∋ α) → motive (C.inl (C.inl z)))
    (x : Γ ⋈ Δ ⋈ Ξ ∋ α) :
  motive x
  := by
  obtain ⟨y, rfl⟩ := Subst.isReinject x
  cases y with
  | right z => apply right
  | middle z => apply middle
  | left z => apply left

/-- `head_cases x with z` applies `threewayOn` to the slot `x`, leaving the goals
`right`, `middle` and `left`, each with the slot `z`. -/
macro "head_cases " x:term " with " z:ident : tactic =>
  `(tactic| refine threewayOn (fun $z => ?right) (fun $z => ?middle) (fun $z => ?left) $x)

/-! ## `Subst.act` on each kind of head -/

/-- `σ.act Φ` keeps a head `C.inr x` with `x : Φ ∋ α` and acts on each argument by
`σ.act (Φ ⋈ _)`. -/
theorem act_right
    {Γ Δ Ξ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity)
    {α : C.Arity} (x : Φ ∋ α) (args : Expr.Args (Γ ⋈ Δ ⋈ Φ) α) :
  σ.act Φ (.ap (C.inr x) args)
    = .ap (C.inr x) (fun {_} j => σ.act (Φ ⋈ _) (args j))
  := by
  rw [Subst.act.eq_def]
  simp only [Subst.threeway_right]

/-- `σ.act Φ` on an application headed by `C.inl (C.inr y)` with `y : Δ ∋ α` is `σ y`
with each slot `i` of `α` substituted by `σ.act (Φ ⋈ _) (args i)`. -/
theorem act_middle
    {Γ Δ Ξ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity)
    {α : C.Arity} (y : Δ ∋ α) (args : Expr.Args (Γ ⋈ Δ ⋈ Φ) α) :
  σ.act Φ (.ap (C.inl (C.inr y)) args)
    = Subst.act (Γ := Γ ⋈ Ξ)
        (fun {_} i => σ.act (Φ ⋈ _) (args i)) 1 (σ y)
  := by
  rw [Subst.act.eq_def]
  simp only [Subst.threeway_middle]

/-- `σ.act Φ` keeps a head `C.inl (C.inl z)` with `z : Γ ∋ α` and acts on each argument
by `σ.act (Φ ⋈ _)`. -/
theorem act_left
    {Γ Δ Ξ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity)
    {α : C.Arity} (z : Γ ∋ α) (args : Expr.Args (Γ ⋈ Δ ⋈ Φ) α) :
  σ.act Φ (.ap (C.inl (C.inl z)) args)
    = .ap (C.inl (C.inl z)) (fun {_} j => σ.act (Φ ⋈ _) (args j))
  := by
  rw [Subst.act.eq_def]
  simp only [Subst.threeway_left]
