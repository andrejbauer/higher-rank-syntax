import HigherRankSyntax.Action.Subst

/-!
# Equational theorems for the substitution walkers

η-side lemmas, the relative-monad laws (`unit_right`, `unit_left`,
`comp_lift`), the embedding `lift_toSubst` of renamings as substitutions, and
the `lift`–`inst` commutation lemma `lift_inst_commute`.
-/

namespace Action

/-! ## Naturality of `extendList` against `tauSlot` -/

@[simp] private theorem extendList_tauSlot {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ) :
    ∀ (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
      (i : C.Binder β),
      ρ.extendList (τ_above ++ β :: τ_below)
          (tauSlot Γ τ_above β τ_below i)
        = tauSlot Δ τ_above β τ_below i
  | [],        _, _,       _ => rfl
  | _ :: rest, β, τ_below, i => by
    show Slot.there (ρ.extendList (rest ++ β :: τ_below)
            (tauSlot Γ rest β τ_below i))
       = Slot.there (tauSlot Δ rest β τ_below i)
    rw [extendList_tauSlot ρ rest β τ_below i]

/-! ## InstWeaken: factoring a renaming out of `inst.aux` -/

/-- `inst.aux` with a non-identity ρ equals first renaming via `ρ ⇑ʳ α` (extended through
the τ-stack) and then `inst.aux` with the identity renaming. -/
private theorem inst_aux_factor_ren {C : Carrier} :
    ∀ {Δ Ξ : Shape C} (α : C.Arity) (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
      (τ : List C.Arity) (e : Expr ((Δ ⋈ α) ⋈* τ)),
      inst.aux α ρ ι τ e
        = inst.aux α 𝟙ʳ ι τ (⟦ (ρ ⇑ʳ α).extendList τ ⟧ʳ e)
  | Δ, Ξ, α, ρ, ι, τ, Expr.apply' p α_h h args => by
    have ih_arg : ∀ (j : C.Binder α_h),
        inst.aux α ρ ι (j.arity :: τ) (args j)
          = inst.aux α 𝟙ʳ ι (j.arity :: τ)
              (⟦ (ρ ⇑ʳ α).extendList (j.arity :: τ) ⟧ʳ (args j)) := by
      intro j
      exact inst_aux_factor_ren α ρ ι (j.arity :: τ) (args j)
    cases classify τ p with
    | ext i =>
      simp only [inst_aux_ext_eq, Renaming.actExpr_apply', extendList_tauSlot]
      congr 1
      funext j
      exact ih_arg j
    | base q =>
      cases q with
      | there r =>
        simp only [inst_aux_base_there_eq, Renaming.actExpr_apply',
          Renaming.extendList_weakenList, Renaming.extend_there,
          Renaming.id_apply]
        congr 1
        funext j
        exact ih_arg j
      | here j =>
        have hs : j.arity = α_h :=
          (((Δ ⋈ α) ↪ʳ τ).arity (.here j)).symm.trans h
        cases hs
        simp only [inst_aux_base_here_eq, Renaming.actExpr_apply',
          Renaming.extendList_weakenList, Renaming.extend_here]
        congr 1
        funext k
        exact ih_arg k
termination_by _ _ _ _ _ τ e => (⟨_ ⋈* τ, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by exact Expr.Subterm.of_arg p α_h h args j

/-! ## η-side lemmas for `inst.aux` -/

private theorem inst_aux_η_tauSlot {C : Carrier} :
    ∀ {Δ Ξ : Shape C} (α : C.Arity) (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
      (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
      (i : C.Binder β),
      inst.aux α ρ ι (i.arity :: (τ_above ++ β :: τ_below))
        (Expr.η ⟨tauSlot (Δ ⋈ α) τ_above β τ_below i, tauSlot_arity (Δ ⋈ α) τ_above β τ_below i⟩)
        =
      Expr.η ⟨tauSlot Ξ τ_above β τ_below i, tauSlot_arity Ξ τ_above β τ_below i⟩
  | Δ, Ξ, α, ρ, ι, τ_above, β, τ_below, i => by
    unfold Expr.η
    change inst.aux α ρ ι ((i.arity :: τ_above) ++ β :: τ_below)
        (Expr.apply' (tauSlot (Δ ⋈ α) (i.arity :: τ_above) β τ_below i)
          i.arity (tauSlot_arity (Δ ⋈ α) (i.arity :: τ_above) β τ_below i)
          (fun k =>
            Expr.η ⟨.here k, rfl⟩))
        =
      Expr.apply' (tauSlot Ξ (i.arity :: τ_above) β τ_below i)
        i.arity (tauSlot_arity Ξ (i.arity :: τ_above) β τ_below i)
        (fun k =>
          Expr.η ⟨.here k, rfl⟩)
    rw [inst_aux_ext_eq]
    congr 1
    funext k
    exact inst_aux_η_tauSlot α ρ ι [] i.arity (τ_above ++ β :: τ_below) k
termination_by _ _ _ _ _ _ _ _ i => i.arity
decreasing_by exact ⟨_, rfl⟩

private theorem inst_aux_η_inv_of {C : Carrier} (Δ : Shape C) (α : C.Arity)
    (hη : ∀ (j : C.Binder α) {Δ' Ξ' : Shape C}
      (ρ : Δ' →ʳ Ξ') (ι : Inst j.arity Ξ') (v : Expr.J Δ' j.arity),
      inst.aux j.arity ρ ι [] (Expr.η v)
        = Expr.apply' (ρ v.val) j.arity ((ρ.arity v.val).trans v.property) ι) :
    ∀ (τ : List C.Arity) (e : Expr ((Δ ⋈ α) ⋈* τ)),
      inst.aux α (Δ ↪ʳ [α]) (η_fillers Δ α) τ e = e
  | τ, Expr.apply' p α_h h args => by
    have ih_arg : ∀ (j : C.Binder α_h),
        inst.aux α (Δ ↪ʳ [α]) (η_fillers Δ α)
          (j.arity :: τ) (args j) = args j := by
      intro j
      exact inst_aux_η_inv_of Δ α hη (j.arity :: τ) (args j)
    cases classify τ p with
    | ext i =>
      rw [inst_aux_ext_eq]
      congr 1
      funext j
      exact ih_arg j
    | base q =>
      cases q with
      | there r =>
        rw [inst_aux_base_there_eq]
        congr 1
        funext j
        exact ih_arg j
      | here j =>
        have hs : j.arity = α_h :=
          (((Δ ⋈ α) ↪ʳ τ).arity (.here j)).symm.trans h
        cases hs
        rw [inst_aux_base_here_eq]
        change inst.aux j.arity ((Δ ⋈ α) ↪ʳ τ)
            (fun k => inst.aux α (Δ ↪ʳ [α]) (η_fillers Δ α)
              (k.arity :: τ) (args k)) []
            (Expr.η ⟨.here j, rfl⟩)
          = Expr.apply' (((Δ ⋈ α) ↪ʳ τ) (.here j))
            j.arity h args
        rw [hη j (Δ' := Δ ⋈ α) (Ξ' := (Δ ⋈ α) ⋈* τ)
          (ρ := ((Δ ⋈ α) ↪ʳ τ))
          (ι := fun k =>
            inst.aux α (Δ ↪ʳ [α]) (η_fillers Δ α)
              (k.arity :: τ) (args k)) (v := ⟨.here j, rfl⟩)]
        congr 1
        funext k
        exact ih_arg k
termination_by τ e => (⟨(Δ ⋈ α) ⋈* τ, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by exact Expr.Subterm.of_arg p α_h h args j

private theorem inst_aux_η_bundle {C : Carrier} (α : C.Arity) :
    (∀ {Δ Ξ : Shape C} (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
      (v : Expr.J Δ α),
      inst.aux α ρ ι [] (Expr.η v)
        = Expr.apply' (ρ v.val) α ((ρ.arity v.val).trans v.property) ι)
    ∧
    (∀ (Δ : Shape C) (τ : List C.Arity) (e : Expr ((Δ ⋈ α) ⋈* τ)),
      inst.aux α (Δ ↪ʳ [α]) (η_fillers Δ α) τ e = e) := by
  refine C.subWf.induction (C := fun α =>
    (∀ {Δ Ξ : Shape C} (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
      (v : Expr.J Δ α),
      inst.aux α ρ ι [] (Expr.η v)
        = Expr.apply' (ρ v.val) α ((ρ.arity v.val).trans v.property) ι)
    ∧
    (∀ (Δ : Shape C) (τ : List C.Arity) (e : Expr ((Δ ⋈ α) ⋈* τ)),
      inst.aux α (Δ ↪ʳ [α]) (η_fillers Δ α) τ e = e)) α ?_
  intro α ih
  constructor
  · intro Δ Ξ ρ ι v
    rcases v with ⟨p, hp⟩
    unfold Expr.η
    change inst.aux α ρ ι []
        (Expr.apply' (((Δ ⋈ α) ↪ʳ []) (.there p))
          α hp (fun i => Expr.η ⟨.here i, rfl⟩))
        = Expr.apply' (ρ p) α ((ρ.arity p).trans hp) ι
    rw [inst_aux_base_there_eq]
    congr 1
    funext i
    unfold Expr.η
    change inst.aux α ρ ι [i.arity]
        (Expr.apply' (((Δ ⋈ α) ↪ʳ [i.arity]) (.here i))
          i.arity rfl
          (fun k => Expr.η ⟨.here k, rfl⟩))
        = ι i
    rw [inst_aux_base_here_eq]
    change inst.aux i.arity (Ξ ↪ʳ [i.arity])
        (fun k : C.Binder i.arity => inst.aux α ρ ι (k.arity :: [i.arity])
          (Expr.η ⟨.here k, rfl⟩)) [] (ι i)
      = ι i
    have hargs : (fun k : C.Binder i.arity => inst.aux α ρ ι (k.arity :: [i.arity])
          (Expr.η ⟨.here k, rfl⟩))
        = η_fillers Ξ i.arity := by
      funext k
      unfold η_fillers
      exact inst_aux_η_tauSlot α ρ ι [] i.arity [] k
    rw [hargs]
    exact (ih i.arity ⟨i, rfl⟩).2 Ξ [] (ι i)
  · intro Δ
    exact inst_aux_η_inv_of Δ α (fun j => (ih j.arity ⟨j, rfl⟩).1)

private theorem inst_aux_η {C : Carrier} {Δ Ξ : Shape C}
    (α : C.Arity) (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
    (v : Expr.J Δ α) :
    inst.aux α ρ ι [] (Expr.η v)
      =
    Expr.apply' (ρ v.val) α ((ρ.arity v.val).trans v.property) ι :=
  (inst_aux_η_bundle α).1 ρ ι v

private theorem inst_aux_η_inv {C : Carrier} (Δ : Shape C) (α : C.Arity) :
    ∀ (τ : List C.Arity) (e : Expr ((Δ ⋈ α) ⋈* τ)),
      inst.aux α (Δ ↪ʳ [α]) (η_fillers Δ α) τ e = e :=
  (inst_aux_η_bundle α).2 Δ

/-! ## η-side lemma for `lift.aux` -/

private theorem lift_aux_η_tauSlot {C : Carrier} :
    ∀ {Γ Δ : Shape C} (σ : Subst Γ Δ)
      (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
      (i : C.Binder β),
      lift.aux σ (i.arity :: (τ_above ++ β :: τ_below))
        (Expr.η ⟨tauSlot Γ τ_above β τ_below i, tauSlot_arity Γ τ_above β τ_below i⟩)
        =
      Expr.η ⟨tauSlot Δ τ_above β τ_below i, tauSlot_arity Δ τ_above β τ_below i⟩
  | Γ, Δ, σ, τ_above, β, τ_below, i => by
    unfold Expr.η
    change lift.aux σ ((i.arity :: τ_above) ++ β :: τ_below)
        (Expr.apply' (tauSlot Γ (i.arity :: τ_above) β τ_below i)
          i.arity (tauSlot_arity Γ (i.arity :: τ_above) β τ_below i)
          (fun k =>
            Expr.η ⟨.here k, rfl⟩))
        =
      Expr.apply' (tauSlot Δ (i.arity :: τ_above) β τ_below i)
        i.arity (tauSlot_arity Δ (i.arity :: τ_above) β τ_below i)
        (fun k =>
          Expr.η ⟨.here k, rfl⟩)
    rw [lift_aux_ext_eq]
    congr 1
    funext k
    exact lift_aux_η_tauSlot σ [] i.arity (τ_above ++ β :: τ_below) k
termination_by _ _ _ _ _ _ i => i.arity
decreasing_by exact ⟨_, rfl⟩

/-! ## Left unit law -/

private theorem unit_left.aux {C : Carrier} {Γ Δ : Shape C}
    (σ : Subst Γ Δ) :
    ∀ {α : C.Arity} (v : Expr.J Γ α),
      lift.aux σ [α] (Expr.η v)
        =
      (match v with | ⟨p, hp⟩ => match hp with | rfl => σ p)
  | α, ⟨p, hp⟩ => by
    cases hp
    unfold Expr.η
    change lift.aux σ [p.arity]
        (Expr.apply' ((Γ ↪ʳ [p.arity]) p)
          p.arity rfl
          (fun i => Expr.η ⟨.here i, rfl⟩))
        = σ p
    rw [lift_aux_base_eq]
    change inst.aux p.arity (Δ ↪ʳ [p.arity])
        (fun i : C.Binder p.arity =>
          lift.aux σ (i.arity :: [p.arity])
            (Expr.η ⟨.here i, rfl⟩)) [] (σ p)
      = σ p
    have hargs : (fun i : C.Binder p.arity =>
          lift.aux σ (i.arity :: [p.arity])
            (Expr.η ⟨.here i, rfl⟩))
        = η_fillers Δ p.arity := by
      funext i
      unfold η_fillers
      exact lift_aux_η_tauSlot σ [] p.arity [] i
    rw [hargs]
    exact inst_aux_η_inv Δ p.arity [] (σ p)

theorem unit_left {C : Carrier} {Γ Δ : Shape C}
    (f : ∀ α : C.Arity, Expr.J Γ α → Expr.T Δ α) :
    ∀ {α : C.Arity} (v : Expr.J Γ α),
      f α v = Subst.lift (fun s => f s.arity ⟨s, rfl⟩) (Expr.η v)
  | _, ⟨p, hp⟩ => by
    cases hp
    symm
    exact unit_left.aux (fun s => f s.arity ⟨s, rfl⟩) ⟨p, rfl⟩

/-! ## Embedding renamings as substitutions -/

/-- Walker-level form of `lift_toSubst`: lifting `ρ.toSubst` through τ acts as the
iterated extension of `ρ` through τ. -/
private theorem lift_toSubst.aux {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ) :
    ∀ (τ : List C.Arity) (e : Expr (Γ ⋈* τ)),
      lift.aux ρ.toSubst τ e = ⟦ ρ.extendList τ ⟧ʳ e
  | τ, Expr.apply' p α_h h args => by
    have ih_arg : ∀ (j : C.Binder α_h),
        lift.aux ρ.toSubst (j.arity :: τ) (args j)
          = ⟦ ρ.extendList (j.arity :: τ) ⟧ʳ (args j) := by
      intro j
      exact lift_toSubst.aux ρ (j.arity :: τ) (args j)
    cases classify τ p with
    | ext i =>
      simp only [lift_aux_ext_eq, Renaming.actExpr_apply', extendList_tauSlot]
      congr 1
      funext j
      exact ih_arg j
    | base q =>
      have hs : q.arity = α_h :=
        ((Γ ↪ʳ τ).arity q).symm.trans h
      cases hs
      rw [lift_aux_base_eq]
      show inst.aux q.arity (Δ ↪ʳ τ)
            (fun j => lift.aux ρ.toSubst (j.arity :: τ) (args j)) []
            (Expr.η ⟨ρ q, ρ.arity q⟩)
          = ⟦ ρ.extendList τ ⟧ʳ
              Expr.apply' ((Γ ↪ʳ τ) q) q.arity h args
      rw [inst_aux_η]
      simp only [Renaming.actExpr_apply', Renaming.extendList_weakenList]
      congr 1
      funext j
      exact ih_arg j
termination_by τ e => (⟨Γ ⋈* τ, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by exact Expr.Subterm.of_arg p α_h h args j

/-- Substituting via a renaming embedded as a substitution is the renaming action:
`ρ.toSubst.lift e = ⟦ ρ ⇑ʳ α ⟧ʳ e`. -/
theorem lift_toSubst {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ)
    {α : C.Arity} (e : Expr (Γ ⋈ α)) :
    ρ.toSubst.lift e = ⟦ ρ ⇑ʳ α ⟧ʳ e :=
  lift_toSubst.aux ρ [α] e

/-! ## Right unit law -/

/-- Right unit law: lifting the η-substitution is the identity. -/
theorem unit_right {C : Carrier} {Γ : Shape C}
    (α : C.Arity) (e : Expr.T Γ α) :
    Subst.lift (fun q => Expr.η ⟨q, rfl⟩) e = e :=
  (lift_toSubst 𝟙ʳ e).trans (by simp)

/-! ## Commutation of `lift` past `inst` -/

/-- Walking `inst.aux α (weakenList Δ τ) ι [] e` with `lift.aux θ τ` equals
instantiating with the `lift`ed instantiation data into the `lift`ed expression. -/
private theorem lift_inst_commute {C : Carrier} :
    ∀ {Δ Ε : Shape C} (θ : Subst Δ Ε) (α : C.Arity)
      (τ : List C.Arity) (ι : Inst α (Δ ⋈* τ)) (e : Expr (Δ ⋈ α)),
      lift.aux θ τ (inst.aux α (Δ ↪ʳ τ) ι [] e)
        =
      inst.aux α (Ε ↪ʳ τ)
        (fun j => lift.aux θ (j.arity :: τ) (ι j))
        [] (θ.lift e) := by
  sorry

/-! ## Composition law -/

private theorem comp_lift.aux {C : Carrier} {Γ Δ Ε : Shape C}
    (σ : Subst Γ Δ) (θ : Subst Δ Ε) :
    ∀ (τ : List C.Arity) (e : Expr (Γ ⋈* τ)),
      lift.aux (σ ˢ∘ˢ θ) τ e = lift.aux θ τ (lift.aux σ τ e)
  | τ, Expr.apply' p α_h h args => by
    have ih_arg : ∀ (j : C.Binder α_h),
        lift.aux (σ ˢ∘ˢ θ) (j.arity :: τ) (args j)
          = lift.aux θ (j.arity :: τ) (lift.aux σ (j.arity :: τ) (args j)) := by
      intro j
      exact comp_lift.aux σ θ (j.arity :: τ) (args j)
    cases classify τ p with
    | ext i =>
      simp only [lift_aux_ext_eq]
      congr 1
      funext j
      exact ih_arg j
    | base q =>
      have hs : q.arity = α_h :=
        ((Γ ↪ʳ τ).arity q).symm.trans h
      cases hs
      simp only [lift_aux_base_eq]
      rw [lift_inst_commute]
      congr 1
      funext j
      exact ih_arg j
termination_by τ e => (⟨Γ ⋈* τ, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by exact Expr.Subterm.of_arg p α_h h args j

/-- Composition of Kleisli extensions: substituting via σ then via θ equals substituting
via the composed substitution `σ ˢ∘ˢ θ`. -/
theorem comp_lift {C : Carrier} {Γ Δ Ε : Shape C}
    (σ : Subst Γ Δ) (θ : Subst Δ Ε) :
    ∀ {α : C.Arity} (e : Expr (Γ ⋈ α)),
      Subst.lift (fun q => θ.lift (σ q)) e
        =
      θ.lift (σ.lift e) := by
  intro α e
  exact comp_lift.aux σ θ [α] e

end Action
