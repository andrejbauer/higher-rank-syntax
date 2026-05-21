import HigherRankSyntax.Subst

/-!
# Equational theorems for the substitution walkers

η-side lemmas, the relative-monad laws (`unit_right`, `unit_left`,
`comp_lift`), the embedding `lift_toSubst` of renamings as substitutions, and
the `lift`–`inst` commutation lemma `lift_inst_commute`.
-/


/-! ## Naturality of `extendList` against `tauSlot` -/

@[simp] private theorem extendList_tauSlot {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ) :
    ∀ (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
      (i : C.Binder β),
      ρ.extendList (τ_above ++ β :: τ_below)
          (tauSlot Γ τ_above β τ_below i)
        = tauSlot Δ τ_above β τ_below i
  | [],        _, _,       _ => rfl
  | _ :: rest, β, τ_below, i => by
    show SlotAt.there (ρ.extendList (rest ++ β :: τ_below)
            (tauSlot Γ rest β τ_below i))
       = SlotAt.there (tauSlot Δ rest β τ_below i)
    rw [extendList_tauSlot ρ rest β τ_below i]

/-! ## How `Subst.extendList` acts on classified slots -/

/-- `σ.extendList τ` at a `tauSlot` η-expands to the corresponding `tauSlot` on the
codomain side. -/
private theorem subst_extendList_tauSlot {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ) :
    ∀ (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
      (i : C.Binder β),
      (σ.extendList (τ_above ++ β :: τ_below))
          (tauSlot Γ τ_above β τ_below i)
        = Expr.η (tauSlot Δ τ_above β τ_below i)
  | [],        _, _,       _ => rfl
  | a :: rest, β, τ_below, i => by
    show ⟦ Renaming.weaken (Δ ⋈* (rest ++ β :: τ_below)) a ⇑ʳ i.arity ⟧ʳ
            ((σ.extendList (rest ++ β :: τ_below)) (tauSlot Γ rest β τ_below i))
        = Expr.η (tauSlot Δ (a :: rest) β τ_below i)
    rw [subst_extendList_tauSlot σ rest β τ_below i, Renaming.actExpr_η]
    rfl

/-- `σ.extendList τ` at a Γ-slot weakened through τ equals σ acting on the slot,
then weakened through τ on the codomain side. -/
private theorem subst_extendList_weakenList {C : Carrier} {Γ Δ : Shape C}
    (σ : Subst Γ Δ) :
    ∀ (τ : List C.Arity) {α : C.Arity} (q : Γ ∋ α),
      (σ.extendList τ) ((Γ ↪ʳ τ) q) = ⟦ (Δ ↪ʳ τ) ⇑ʳ α ⟧ʳ (σ q)
  | [],        α, q => by
    show σ q = ⟦ (𝟙ʳ : Δ →ʳ Δ) ⇑ʳ α ⟧ʳ (σ q)
    rw [Renaming.extend_id, Renaming.actExpr.map_id]
  | β :: rest, α, q => by
    show ⟦ Renaming.weaken (Δ ⋈* rest) β ⇑ʳ α ⟧ʳ
            ((σ.extendList rest) ((Γ ↪ʳ rest) q))
        = ⟦ (Renaming.weaken (Δ ⋈* rest) β ∘ʳ (Δ ↪ʳ rest)) ⇑ʳ α ⟧ʳ (σ q)
    rw [subst_extendList_weakenList σ rest q,
        ← Renaming.actExpr.map_comp, Renaming.extend_comp]

/-! ## F2 — substitution after renaming -/

/-- **RenSub fusion** (Allais et al. F2): walking `lift.aux σ τ` after a renaming
`⟦ ρ.extendList τ ⟧ʳ` equals walking `lift.aux (ρ ʳ∘ˢ σ) τ` directly.  The renaming
is absorbed into the substitution by pre-composition. -/
private theorem subst_after_ren {C : Carrier} :
    ∀ {Γ Γ' Δ : Shape C} (ρ : Γ →ʳ Γ') (σ : Subst Γ' Δ)
      (τ : List C.Arity) (e : Expr (Γ ⋈* τ)),
      lift.aux σ τ (⟦ ρ.extendList τ ⟧ʳ e)
        = lift.aux (ρ ʳ∘ˢ σ) τ e
  | Γ, Γ', Δ, ρ, σ, τ, .apply (α := α_h) p args => by
    have ih_arg : ∀ (k : C.Binder α_h),
        lift.aux σ (k.arity :: τ)
            (⟦ ρ.extendList (k.arity :: τ) ⟧ʳ (args k))
          = lift.aux (ρ ʳ∘ˢ σ) (k.arity :: τ) (args k) :=
      fun k => subst_after_ren ρ σ (k.arity :: τ) (args k)
    cases classify τ p with
    | ext i =>
      simp only [Renaming.actExpr_apply, extendList_tauSlot, lift_aux_ext_eq]
      congr 1
      funext k
      exact ih_arg k
    | base q =>
      simp only [Renaming.actExpr_apply, Renaming.extendList_weakenList,
                 lift_aux_base_eq]
      congr 1
      funext k
      exact ih_arg k
termination_by _ _ _ _ _ τ e => (⟨_ ⋈* τ, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by exact Expr.Subterm.of_arg _ _ _

/-! ## InstWeaken: factoring a renaming out of `inst.aux` -/

/-- `inst.aux` with a non-identity ρ equals first renaming via `ρ ⇑ʳ α` (extended through
the τ-stack) and then `inst.aux` with the identity renaming. -/
private theorem inst_aux_factor_ren {C : Carrier} :
    ∀ {Δ Ξ : Shape C} (α : C.Arity) (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
      (τ : List C.Arity) (e : Expr ((Δ ⋈ α) ⋈* τ)),
      inst.aux α ρ ι τ e
        = inst.aux α 𝟙ʳ ι τ (⟦ (ρ ⇑ʳ α).extendList τ ⟧ʳ e)
  | Δ, Ξ, α, ρ, ι, τ, .apply (α := α_h) p args => by
    have ih_arg : ∀ (j : C.Binder α_h),
        inst.aux α ρ ι (j.arity :: τ) (args j)
          = inst.aux α 𝟙ʳ ι (j.arity :: τ)
              (⟦ (ρ ⇑ʳ α).extendList (j.arity :: τ) ⟧ʳ (args j)) := by
      intro j
      exact inst_aux_factor_ren α ρ ι (j.arity :: τ) (args j)
    cases classify τ p with
    | ext i =>
      simp only [inst_aux_ext_eq, Renaming.actExpr_apply, extendList_tauSlot]
      congr 1
      funext j
      exact ih_arg j
    | base q =>
      cases q with
      | there r =>
        simp only [inst_aux_base_there_eq, Renaming.actExpr_apply,
          Renaming.extendList_weakenList, Renaming.extend_there,
          Renaming.id_apply]
        congr 1
        funext j
        exact ih_arg j
      | here j =>
        simp only [inst_aux_base_here_eq, Renaming.actExpr_apply,
          Renaming.extendList_weakenList, Renaming.extend_here]
        congr 1
        funext k
        exact ih_arg k
termination_by _ _ _ _ _ τ e => (⟨_ ⋈* τ, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by exact Expr.Subterm.of_arg p args j

/-! ## Renaming naturality of `inst.aux` -/

/-- Inner statement of `inst_aux_rename_id`, parametrised by the smaller-α induction
hypothesis.  Structural induction on `e` (no α-decrease in this layer). -/
private theorem inst_aux_rename_id_inner {C : Carrier} {Δ Δ' : Shape C} (α : C.Arity)
    (ih_α : ∀ (j : C.Binder α) {Δ_ Δ'_ : Shape C} (ρ_ : Δ_ →ʳ Δ'_)
              (ι_ : Inst j.arity Δ_) (τ_ : List C.Arity)
              (e_ : Expr ((Δ_ ⋈ j.arity) ⋈* τ_)),
            ⟦ ρ_.extendList τ_ ⟧ʳ (inst.aux j.arity 𝟙ʳ ι_ τ_ e_)
              = inst.aux j.arity 𝟙ʳ (fun k => ⟦ ρ_ ⇑ʳ k.arity ⟧ʳ (ι_ k)) τ_
                  (⟦ (ρ_ ⇑ʳ j.arity).extendList τ_ ⟧ʳ e_))
    (ρ : Δ →ʳ Δ') (ι : Inst α Δ) :
    ∀ (τ : List C.Arity) (e : Expr ((Δ ⋈ α) ⋈* τ)),
      ⟦ ρ.extendList τ ⟧ʳ (inst.aux α 𝟙ʳ ι τ e)
        = inst.aux α 𝟙ʳ (fun k => ⟦ ρ ⇑ʳ k.arity ⟧ʳ (ι k)) τ
            (⟦ (ρ ⇑ʳ α).extendList τ ⟧ʳ e)
  | τ, .apply (α := α_h) p args => by
    have ih_arg : ∀ (k : C.Binder α_h),
        ⟦ ρ.extendList (k.arity :: τ) ⟧ʳ
            (inst.aux α 𝟙ʳ ι (k.arity :: τ) (args k))
          = inst.aux α 𝟙ʳ (fun j => ⟦ ρ ⇑ʳ j.arity ⟧ʳ (ι j))
              (k.arity :: τ)
              (⟦ (ρ ⇑ʳ α).extendList (k.arity :: τ) ⟧ʳ (args k)) :=
      fun k => inst_aux_rename_id_inner α ih_α ρ ι (k.arity :: τ) (args k)
    cases classify τ p with
    | ext i =>
      simp only [inst_aux_ext_eq, Renaming.actExpr_apply, extendList_tauSlot]
      congr 1
      funext k
      exact ih_arg k
    | base q =>
      cases q with
      | there r =>
        simp only [inst_aux_base_there_eq, Renaming.actExpr_apply,
                   Renaming.extendList_weakenList, Renaming.extend_there,
                   Renaming.id_apply]
        congr 1
        funext k
        exact ih_arg k
      | here j =>
        -- LHS: unfold .here, factor (Δ↪ʳτ) out.
        rw [inst_aux_base_here_eq, inst_aux_factor_ren j.arity (Δ ↪ʳ τ)]
        simp only [Renaming.extendList_nil]
        -- RHS: unfold renaming + .here, factor (Δ'↪ʳτ) out.
        rw [Renaming.actExpr_apply, Renaming.extendList_weakenList,
            Renaming.extend_here, inst_aux_base_here_eq,
            inst_aux_factor_ren j.arity (Δ' ↪ʳ τ)]
        simp only [Renaming.extendList_nil]
        -- Apply ih_α at j ∈ Binder α to commute the outer renaming through
        -- the inner inst.aux j.arity.
        have ih_j := ih_α j (ρ.extendList τ)
              (fun k => inst.aux α 𝟙ʳ ι (k.arity :: τ) (args k)) []
              (⟦ (Δ ↪ʳ τ) ⇑ʳ j.arity ⟧ʳ (ι j))
        simp only [Renaming.extendList_nil] at ih_j
        refine ih_j.trans ?_
        -- Goal: inst.aux j.arity 𝟙ʳ Λ_LHS [] (⟦ρ.extendList τ ⇑ʳ j.arity⟧ʳ (⟦(Δ↪ʳτ) ⇑ʳ j.arity⟧ʳ ι j))
        --     = inst.aux j.arity 𝟙ʳ Λ_RHS [] (⟦(Δ' ↪ʳ τ) ⇑ʳ j.arity⟧ʳ (⟦ρ ⇑ʳ j.arity⟧ʳ ι j))
        congr 1
        · -- Λ_LHS = Λ_RHS (function position)
          funext k
          exact ih_arg k
        · -- value position equality via renaming naturality
          rw [← Renaming.actExpr.map_comp]
          show Renaming.actExpr (((ρ.extendList τ) ⇑ʳ j.arity) ∘ʳ
                                  ((Δ ↪ʳ τ) ⇑ʳ j.arity)) (ι j) = _
          rw [← Renaming.extend_comp (Δ ↪ʳ τ) (ρ.extendList τ) j.arity,
              Renaming.weakenList_naturality,
              Renaming.extend_comp ρ (Δ' ↪ʳ τ) j.arity,
              Renaming.actExpr.map_comp]
          rfl
termination_by τ e => (⟨(Δ ⋈ α) ⋈* τ, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by exact Expr.Subterm.of_arg _ _ _

/-- **Inst-Ren naturality** (at the identity-renaming form): pushing a renaming `ρ.extendList τ`
past `inst.aux α 𝟙ʳ ι τ` factors into a renamed instantiation on the result plus a renaming
on the input.  Recurses on `α` via `subWf`, wrapping the structural-on-`e`
`inst_aux_rename_id_inner`. -/
private theorem inst_aux_rename_id {C : Carrier} {Δ Δ' : Shape C}
    (α : C.Arity) (ρ : Δ →ʳ Δ') (ι : Inst α Δ)
    (τ : List C.Arity) (e : Expr ((Δ ⋈ α) ⋈* τ)) :
    ⟦ ρ.extendList τ ⟧ʳ (inst.aux α 𝟙ʳ ι τ e)
      = inst.aux α 𝟙ʳ (fun k => ⟦ ρ ⇑ʳ k.arity ⟧ʳ (ι k)) τ
          (⟦ (ρ ⇑ʳ α).extendList τ ⟧ʳ e) :=
  inst_aux_rename_id_inner α
    (fun j _ _ ρ_ ι_ τ_ e_ => inst_aux_rename_id j.arity ρ_ ι_ τ_ e_) ρ ι τ e
termination_by α
decreasing_by exact ⟨j, rfl⟩

/-! ## η-side lemmas for `inst.aux` -/

private theorem inst_aux_η_tauSlot {C : Carrier} :
    ∀ {Δ Ξ : Shape C} (α : C.Arity) (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
      (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
      (i : C.Binder β),
      inst.aux α ρ ι (i.arity :: (τ_above ++ β :: τ_below))
        (Expr.η (tauSlot (Δ ⋈ α) τ_above β τ_below i))
        =
      Expr.η (tauSlot Ξ τ_above β τ_below i)
  | Δ, Ξ, α, ρ, ι, τ_above, β, τ_below, i => by
    unfold Expr.η
    change inst.aux α ρ ι ((i.arity :: τ_above) ++ β :: τ_below)
        (Expr.apply (tauSlot (Δ ⋈ α) (i.arity :: τ_above) β τ_below i)
          (fun k => Expr.η (.here k)))
        =
      Expr.apply (tauSlot Ξ (i.arity :: τ_above) β τ_below i)
        (fun k => Expr.η (.here k))
    rw [inst_aux_ext_eq]
    congr 1
    funext k
    exact inst_aux_η_tauSlot α ρ ι [] i.arity (τ_above ++ β :: τ_below) k
termination_by _ _ _ _ _ _ _ _ i => i.arity
decreasing_by exact ⟨_, rfl⟩

private theorem inst_aux_η_inv_of {C : Carrier} (Δ : Shape C) (α : C.Arity)
    (hη : ∀ (j : C.Binder α) {Δ' Ξ' : Shape C}
      (ρ : Δ' →ʳ Ξ') (ι : Inst j.arity Ξ') (v : Δ' ∋ j.arity),
      inst.aux j.arity ρ ι [] (Expr.η v)
        = Expr.apply (ρ v) ι) :
    ∀ (τ : List C.Arity) (e : Expr ((Δ ⋈ α) ⋈* τ)),
      inst.aux α (Δ ↪ʳ [α]) (η_fillers Δ α) τ e = e
  | τ, .apply (α := α_h) p args => by
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
        rw [inst_aux_base_here_eq]
        change inst.aux j.arity (Δ ⋈ α ↪ʳ τ)
            (fun k => inst.aux α (Δ ↪ʳ [α]) (η_fillers Δ α)
              (k.arity :: τ) (args k)) []
            (Expr.η (.here j))
          = Expr.apply ((Δ ⋈ α ↪ʳ τ) (.here j)) args
        rw [hη j (Δ' := Δ ⋈ α) (Ξ' := (Δ ⋈ α) ⋈* τ)
          (ρ := Δ ⋈ α ↪ʳ τ)
          (ι := fun k =>
            inst.aux α (Δ ↪ʳ [α]) (η_fillers Δ α)
              (k.arity :: τ) (args k)) (v := .here j)]
        congr 1
        funext k
        exact ih_arg k
termination_by τ e => (⟨(Δ ⋈ α) ⋈* τ, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by exact Expr.Subterm.of_arg p args j

private theorem inst_aux_η_bundle {C : Carrier} (α : C.Arity) :
    (∀ {Δ Ξ : Shape C} (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
      (v : Δ ∋ α),
      inst.aux α ρ ι [] (Expr.η v) = Expr.apply (ρ v) ι)
    ∧
    (∀ (Δ : Shape C) (τ : List C.Arity) (e : Expr ((Δ ⋈ α) ⋈* τ)),
      inst.aux α (Δ ↪ʳ [α]) (η_fillers Δ α) τ e = e) := by
  refine C.subWf.induction (C := fun α =>
    (∀ {Δ Ξ : Shape C} (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ) (v : Δ ∋ α),
      inst.aux α ρ ι [] (Expr.η v) = Expr.apply (ρ v) ι)
    ∧
    (∀ (Δ : Shape C) (τ : List C.Arity) (e : Expr ((Δ ⋈ α) ⋈* τ)),
      inst.aux α (Δ ↪ʳ [α]) (η_fillers Δ α) τ e = e)) α ?_
  intro α ih
  constructor
  · intro Δ Ξ ρ ι v
    unfold Expr.η
    change inst.aux α ρ ι []
        (Expr.apply ((Δ ⋈ α ↪ʳ []) (.there v))
          (fun i => Expr.η (.here i)))
        = Expr.apply (ρ v) ι
    rw [inst_aux_base_there_eq]
    congr 1
    funext i
    unfold Expr.η
    change inst.aux α ρ ι [i.arity]
        (Expr.apply ((Δ ⋈ α ↪ʳ [i.arity]) (.here i))
          (fun k => Expr.η (.here k)))
        = ι i
    rw [inst_aux_base_here_eq]
    change inst.aux i.arity (Ξ ↪ʳ [i.arity])
        (fun k : C.Binder i.arity => inst.aux α ρ ι (k.arity :: [i.arity])
          (Expr.η (.here k))) [] (ι i)
      = ι i
    have hargs : (fun k : C.Binder i.arity => inst.aux α ρ ι (k.arity :: [i.arity])
          (Expr.η (.here k)))
        = η_fillers Ξ i.arity := by
      funext k
      unfold η_fillers
      exact inst_aux_η_tauSlot α ρ ι [] i.arity [] k
    rw [hargs]
    exact (ih i.arity ⟨i, rfl⟩).2 Ξ [] (ι i)
  · intro Δ
    exact inst_aux_η_inv_of Δ α (fun j => (ih j.arity ⟨j, rfl⟩).1)

private theorem inst_aux_η {C : Carrier} {Δ Ξ : Shape C}
    (α : C.Arity) (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ) (v : Δ ∋ α) :
    inst.aux α ρ ι [] (Expr.η v) = Expr.apply (ρ v) ι :=
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
        (Expr.η (tauSlot Γ τ_above β τ_below i))
        =
      Expr.η (tauSlot Δ τ_above β τ_below i)
  | Γ, Δ, σ, τ_above, β, τ_below, i => by
    unfold Expr.η
    change lift.aux σ ((i.arity :: τ_above) ++ β :: τ_below)
        (Expr.apply (tauSlot Γ (i.arity :: τ_above) β τ_below i)
          (fun k => Expr.η (.here k)))
        =
      Expr.apply (tauSlot Δ (i.arity :: τ_above) β τ_below i)
        (fun k => Expr.η (.here k))
    rw [lift_aux_ext_eq]
    congr 1
    funext k
    exact lift_aux_η_tauSlot σ [] i.arity (τ_above ++ β :: τ_below) k
termination_by _ _ _ _ _ _ i => i.arity
decreasing_by exact ⟨_, rfl⟩

/-! ## Left unit law -/

private theorem unit_left.aux {C : Carrier} {Γ Δ : Shape C}
    (σ : Subst Γ Δ) :
    ∀ {α : C.Arity} (v : Γ ∋ α),
      lift.aux σ [α] (Expr.η v) = σ v
  | α, p => by
    unfold Expr.η
    change lift.aux σ [α]
        (Expr.apply ((Γ ↪ʳ [α]) p) (fun i => Expr.η (.here i)))
        = σ p
    rw [lift_aux_base_eq]
    change inst.aux α (Δ ↪ʳ [α])
        (fun i : C.Binder α =>
          lift.aux σ (i.arity :: [α])
            (Expr.η (.here i))) [] (σ p)
      = σ p
    have hargs : (fun i : C.Binder α =>
          lift.aux σ (i.arity :: [α])
            (Expr.η (.here i)))
        = η_fillers Δ α := by
      funext i
      unfold η_fillers
      exact lift_aux_η_tauSlot σ [] α [] i
    rw [hargs]
    exact inst_aux_η_inv Δ α [] (σ p)

theorem unit_left {C : Carrier} {Γ Δ : Shape C}
    (f : ∀ α : C.Arity, (Γ ∋ α) → Expr.T Δ α) :
    ∀ {α : C.Arity} (v : Γ ∋ α),
      f α v = Subst.lift (fun s => f _ s) (Expr.η v)
  | _, p => by
    symm
    exact unit_left.aux (fun s => f _ s) p

/-! ## Embedding renamings as substitutions -/

/-- Walker-level form of `lift_toSubst`. -/
private theorem lift_toSubst.aux {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ) :
    ∀ (τ : List C.Arity) (e : Expr (Γ ⋈* τ)),
      lift.aux ρ.toSubst τ e = ⟦ Renaming.extendList ρ τ ⟧ʳ e
  | τ, .apply (α := α_h) p args => by
    have ih_arg : ∀ (j : C.Binder α_h),
        lift.aux ρ.toSubst (j.arity :: τ) (args j)
          = ⟦ Renaming.extendList ρ (j.arity :: τ) ⟧ʳ (args j) := by
      intro j
      exact lift_toSubst.aux ρ (j.arity :: τ) (args j)
    cases classify τ p with
    | ext i =>
      simp only [lift_aux_ext_eq, Renaming.actExpr_apply, extendList_tauSlot]
      congr 1
      funext j
      exact ih_arg j
    | base q =>
      rw [lift_aux_base_eq]
      show inst.aux α_h (Δ ↪ʳ τ)
            (fun j => lift.aux ρ.toSubst (j.arity :: τ) (args j)) []
            (Expr.η (ρ q))
          = ⟦ Renaming.extendList ρ τ ⟧ʳ
              Expr.apply ((Γ ↪ʳ τ) q) args
      rw [inst_aux_η]
      simp only [Renaming.actExpr_apply, Renaming.extendList_weakenList]
      congr 1
      funext j
      exact ih_arg j
termination_by τ e => (⟨Γ ⋈* τ, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by exact Expr.Subterm.of_arg p args j

/-- Substituting via a renaming embedded as a substitution is the renaming action. -/
theorem lift_toSubst {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ)
    {α : C.Arity} (e : Expr (Γ ⋈ α)) :
    Subst.lift ρ.toSubst e = ⟦ ρ ⇑ʳ α ⟧ʳ e :=
  lift_toSubst.aux ρ [α] e

/-! ## Right unit law -/

theorem unit_right {C : Carrier} {Γ : Shape C}
    (α : C.Arity) (e : Expr.T Γ α) :
    Subst.lift (fun {α} q => @Expr.η _ _ α q) e = e :=
  (lift_toSubst 𝟙ʳ e).trans (by simp)

/-! ## LiftFactor: absorbing the lift-stack into the substitution -/

/-- The τ = [] case of `lift_aux_base_eq`: at an empty lift-stack, every head slot is a
Γ-slot, and the renaming `Δ ↪ʳ []` collapses to `𝟙ʳ`. -/
private theorem lift_aux_nil_apply {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
    {α : C.Arity} (p : Γ ∋ α)
    (args : (j : C.Binder α) → Expr (Γ ⋈ j.arity)) :
    lift.aux σ [] (Expr.apply p args)
      = inst.aux α 𝟙ʳ (fun j => lift.aux σ [j.arity] (args j)) [] (σ p) := by
  show lift.aux σ [] (Expr.apply ((Γ ↪ʳ []) p) args) = _
  exact lift_aux_base_eq σ [] p args

/-- Walking `lift.aux σ τ` over an outer τ-stack equals walking `lift.aux (σ.extendList τ) []`
with an empty stack. -/
private theorem lift_aux_via_extendList {C : Carrier} :
    ∀ {Γ Δ : Shape C} (σ : Subst Γ Δ) (τ : List C.Arity) (e : Expr (Γ ⋈* τ)),
      lift.aux σ τ e = lift.aux (σ.extendList τ) [] e
  | Γ, Δ, σ, τ, .apply (α := α_h) p args => by
    have hΛ : (fun k : C.Binder α_h => lift.aux σ (k.arity :: τ) (args k))
            = (fun k : C.Binder α_h =>
                lift.aux (σ.extendList τ) [k.arity] (args k)) := by
      funext k
      have hL := lift_aux_via_extendList σ (k.arity :: τ) (args k)
      have hR := lift_aux_via_extendList (σ.extendList τ) [k.arity] (args k)
      rw [hL, hR]
      rfl
    cases classify τ p with
    | ext i =>
      rename_i ta b tb
      rw [lift_aux_ext_eq]
      refine Eq.trans ?_ (lift_aux_nil_apply (σ.extendList (ta ++ b :: tb))
        (tauSlot Γ ta b tb i) args).symm
      rw [subst_extendList_tauSlot]
      simp only [Shape.extList_nil]
      rw [inst_aux_η]
      simp only [Renaming.id_apply]
      rw [← hΛ]
    | base q =>
      rw [lift_aux_base_eq, inst_aux_factor_ren α_h (Δ ↪ʳ τ)]
      simp only [Renaming.extendList_nil]
      refine Eq.trans ?_ (lift_aux_nil_apply (σ.extendList τ)
        ((Γ ↪ʳ τ) q) args).symm
      rw [subst_extendList_weakenList, ← hΛ]
      rfl
termination_by _ _ _ τ e => (⟨_ ⋈* τ, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg _ _ _

/-! ## Commutation of `lift` past `inst` -/

/-- **L5**: lift past inst commutation, generalized to arbitrary inst-walker stack ρ. -/
private theorem lift_inst_commute {C : Carrier} :
    ∀ {Δ Ε : Shape C} (θ : Subst Δ Ε) (α : C.Arity)
      (τ ρ : List C.Arity) (ι : Inst α (Δ ⋈* τ))
      (e : Expr ((Δ ⋈ α) ⋈* ρ)),
      lift.aux θ (ρ ++ τ)
        (Shape.extList_append Δ ρ τ ▸ inst.aux α (Δ ↪ʳ τ) ι ρ e)
        =
      Shape.extList_append Ε ρ τ ▸
        inst.aux α (Ε ↪ʳ τ)
          (fun j => lift.aux θ (j.arity :: τ) (ι j))
          ρ
          ((Shape.extList_append Ε ρ [α]) ▸
            lift.aux θ (ρ ++ [α])
              (Shape.extList_append Δ ρ [α] ▸ e)) := by
  sorry

/-! ## Composition law -/

private theorem comp_lift.aux {C : Carrier} {Γ Δ Ε : Shape C}
    (σ : Subst Γ Δ) (θ : Subst Δ Ε) :
    ∀ (τ : List C.Arity) (e : Expr (Γ ⋈* τ)),
      lift.aux (σ ˢ∘ˢ θ) τ e = lift.aux θ τ (lift.aux σ τ e)
  | τ, .apply (α := α_h) p args => by
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
      simp only [lift_aux_base_eq]
      have hL :
          lift.aux θ τ (inst.aux α_h (Δ ↪ʳ τ)
            (fun j => lift.aux σ (j.arity :: τ) (args j)) [] (σ q))
            = inst.aux α_h (Ε ↪ʳ τ)
              (fun j => lift.aux θ (j.arity :: τ) (lift.aux σ (j.arity :: τ) (args j)))
              [] (θ.lift (σ q)) :=
        lift_inst_commute θ α_h τ []
          (fun j => lift.aux σ (j.arity :: τ) (args j)) (σ q)
      rw [hL]
      congr 1
      funext j
      exact ih_arg j
termination_by τ e => (⟨Γ ⋈* τ, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by exact Expr.Subterm.of_arg p args j

/-- Composition of Kleisli extensions. -/
theorem comp_lift {C : Carrier} {Γ Δ Ε : Shape C}
    (σ : Subst Γ Δ) (θ : Subst Δ Ε) :
    ∀ {α : C.Arity} (e : Expr (Γ ⋈ α)),
      Subst.lift (fun q => θ.lift (σ q)) e
        =
      θ.lift (σ.lift e) := by
  intro α e
  exact comp_lift.aux σ θ [α] e
