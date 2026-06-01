import HigherRankSyntax.Subst

/-!
# Equations of the substitution action

Auxiliary equations for the three relative-monad laws, built from
**computation lemmas**: each takes `Subst.act` on an `Expr.ap` with a
specific head (τ-side, dom-side, pre-side) and reduces the classify
dispatch to a clean right-hand side.  The reflection lemmas
`ProperTele.classify_inr` / `classify_inl` are the rewriting handles.

## The three monad laws

* `Subst.act_id` — `(Subst.id Γ).act τ e = e` (unit_right).
* `Subst.act_η` — `(toSubst f).act (⌊α⌋) (Expr.η p) = f p` (unit_left).
* `Subst.act_kcomp` — Kleisli composition factors (comp_lift).
-/


/-! ## Computation lemmas — `Subst.act` on a specific apply head -/

/-- Computing `σ.act` on an apply whose head is right-injected into the
τ-side: collapses to the S-side reconstruction. -/
theorem Subst.act_ap_inr {C : Carrier} {pre dom cod : Shape C}
    [ProperTele dom] [ProperTele cod]
    (σ : Subst C pre dom cod) (τ : Shape C) [ProperTele τ]
    {α : C.Arity} (x : τ ∋ α)
    (args : (i : C.Binder α) →
      Expr (pre ⋈* dom ⋈* τ ⋈ i.arity)) :
    σ.act τ (.ap ((ProperTele.inr (pre ⋈* dom)) x) args)
      = .ap ((ProperTele.inr (pre ⋈* cod)) x)
          (fun j => σ.act (τ ⋈ j.arity) (args j)) := by
  have h := @Subst.act.eq_1 C pre dom cod inferInstance inferInstance σ τ inferInstance α
              ((ProperTele.inr (pre ⋈* dom)) x) args
  rw [ProperTele.classify_inr (pre ⋈* dom)] at h
  exact h

/-- Computing `σ.act` on an apply whose head is left-injected below τ and
classified to the dom side: fires the dom-branch instantiation. -/
theorem Subst.act_ap_inl_dom {C : Carrier} {pre dom cod : Shape C}
    [ProperTele dom] [ProperTele cod]
    (σ : Subst C pre dom cod) (τ : Shape C) [ProperTele τ]
    {α : C.Arity} (y : dom ∋ α)
    (args : (i : C.Binder α) →
      Expr (pre ⋈* dom ⋈* τ ⋈ i.arity)) :
    σ.act τ (.ap
              ((ProperTele.inl (pre ⋈* dom))
                ((ProperTele.inr pre) y)) args)
      = ⟦Subst.inst (⌊α⌋) (fun q => match q with
            | .here i => σ.act (τ ⋈ i.arity) (args i))⟧ˢ (σ y) := by
  have h := @Subst.act.eq_1 C pre dom cod inferInstance inferInstance σ τ inferInstance α
              ((ProperTele.inl (pre ⋈* dom))
                ((ProperTele.inr pre) y)) args
  rw [ProperTele.classify_inl (pre ⋈* dom)] at h
  unfold Subst.classifyDom at h
  rw [ProperTele.classify_inr pre] at h
  exact h

/-- Computing `σ.act` on an apply whose head is left-injected below τ and
classified to the pre side: rebuilds the head in the pre branch. -/
theorem Subst.act_ap_inl_pre {C : Carrier} {pre dom cod : Shape C}
    [ProperTele dom] [ProperTele cod]
    (σ : Subst C pre dom cod) (τ : Shape C) [ProperTele τ]
    {α : C.Arity} (z : pre ∋ α)
    (args : (i : C.Binder α) →
      Expr (pre ⋈* dom ⋈* τ ⋈ i.arity)) :
    σ.act τ (.ap
              ((ProperTele.inl (pre ⋈* dom))
                ((ProperTele.inl pre) z)) args)
      = .ap
          ((ProperTele.inl (pre ⋈* cod))
            ((Subst.weakenCod σ) z))
          (fun i => σ.act (τ ⋈ i.arity) (args i)) := by
  have h := @Subst.act.eq_1 C pre dom cod inferInstance inferInstance σ τ inferInstance α
              ((ProperTele.inl (pre ⋈* dom))
                ((ProperTele.inl pre) z)) args
  rw [ProperTele.classify_inl (pre ⋈* dom)] at h
  unfold Subst.classifyDom at h
  rw [ProperTele.classify_inl pre] at h
  exact h

/-! ## Auxiliary: η-action on a right-injected slot -/

/-- Acting on the η-expansion of a right-injected (S-side) slot reproduces
the η in the target shape.  By WF recursion on the slot's arity `α`; uses
`act_apply_inr` as a black-box computation lemma. -/
theorem Subst.act_η_inr {C : Carrier} {pre dom cod : Shape C}
    [ProperTele dom] [ProperTele cod]
    (σ : Subst C pre dom cod) (τ : Shape C) [ProperTele τ]
    {α : C.Arity} (x : τ ∋ α) :
    σ.act (τ ⋈ α)
        (.η ((ProperTele.inr (pre ⋈* dom)) x))
      = .η ((ProperTele.inr (pre ⋈* cod)) x) := by
  rw [Expr.η.eq_1]
  -- `.there ((inr τ) x) = (inr (τ ⋈ α)) (.there x)` holds
  -- definitionally (instCons.inr); `change` accepts the defeq.
  change σ.act (τ ⋈ α)
      (.ap ((ProperTele.inr (pre ⋈* dom))
                     (.there x))
                  (fun i => .η (.here i))) = _
  rw [Subst.act_ap_inr σ (τ ⋈ α) (.there x)]
  rw [Expr.η.eq_1]
  congr 1
  funext i
  exact Subst.act_η_inr σ (τ ⋈ α)
          (x := @ListSlotAt.here C α τ.toList i)
termination_by α
decreasing_by exact ⟨i, rfl⟩

/-! ## Instantiation laws: identity action and β-for-η -/

/-- Identity instantiation acts as the identity, given the β-for-η
property at the immediate sub-arities of the head arity.  The proof
recurses over the expression. -/
private theorem Subst.act_inst.idOf {C : Carrier} (α : C.Arity) (Δ : Shape C)
    (hη : ∀ (i : C.Binder α), ∀ {pre cod : Shape C} [ProperTele cod]
      (ι : ∀ {β : C.Arity}, (⌊i.arity⌋) ∋ β → Expr (pre ⋈* cod ⋈ β))
      (p : pre ∋ i.arity),
      ⟦Subst.inst (⌊i.arity⌋) ι⟧ˢ (.η p)
        = .ap ((ProperTele.inl pre) p) (fun j => ι (.here j))) :
    ∀ (τ : Shape C) [ProperTele τ] (e : Expr ((Δ ⋈ α) ⋈* τ)),
      (Subst.instId Δ α).act τ e = e
  | τ, _, .ap (α := β) head argFam => by
      have ih_all : ∀ (k : C.Binder β),
          (Subst.instId Δ α).act (τ ⋈ k.arity) (argFam k) = argFam k :=
        fun k => Subst.act_inst.idOf α Δ hη (τ ⋈ k.arity) (argFam k)
      rcases ProperTele.cover (Δ ⋈ α) head with ⟨y, h_y⟩ | ⟨y, h_y⟩
      · subst h_y
        refine (Subst.act_ap_inr (Subst.instId Δ α) τ y argFam).trans ?_
        congr
        funext k
        exact ih_all k
      · subst h_y
        rcases ProperTele.cover Δ y with ⟨z, h_z⟩ | ⟨z, h_z⟩
        · subst h_z
          cases z with
          | here i =>
              refine (Subst.act_ap_inl_dom
                (Subst.instId Δ α) τ (.here i) argFam).trans ?_
              rw [show (Subst.instId Δ α).sub (.here i)
                    = @Expr.η C (Δ ⋈ α) i.arity (.here i) from rfl]
              refine (hη i (pre := Δ ⋈ α) (cod := τ)
                (ι := _) (p := .here i)).trans ?_
              change
                Expr.ap ((ProperTele.inl (Δ ⋈ α))
                    (.here i))
                  (fun k => (Subst.instId Δ α).act (τ ⋈ k.arity) (argFam k))
                =
                Expr.ap ((ProperTele.inl (Δ ⋈ α))
                    (.here i)) argFam
              congr 1
              funext k
              exact ih_all k
          | there z' => nomatch z'
        · subst h_z
          refine (Subst.act_ap_inl_pre (Subst.instId Δ α) τ z argFam).trans ?_
          change
            Expr.ap ((ProperTele.inl (Δ ⋈ α))
                ((ProperTele.inl Δ) z))
              (fun k => (Subst.instId Δ α).act (τ ⋈ k.arity) (argFam k))
            =
            Expr.ap ((ProperTele.inl (Δ ⋈ α))
                ((ProperTele.inl Δ) z)) argFam
          congr 1
          funext k
          exact ih_all k
termination_by τ _ e => (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg head argFam _

-- β-for-η and identity-act, proved together by well-founded recursion on
-- arities: β-for-η at α invokes identity-act at i.arity ≺ α, and identity-act
-- at α invokes β-for-η at i.arity ≺ α (via `idOf`'s hypothesis).
mutual

/-- β-for-η for a one-binder instantiation: instantiating the η-expansion
of a pre-slot exposes the kit. -/
theorem Subst.act_inst.η {C : Carrier} {pre cod : Shape C} [ProperTele cod]
    {α : C.Arity}
    (ι : ∀ {β : C.Arity}, (⌊α⌋) ∋ β →
      Expr (pre ⋈* cod ⋈ β))
    (p : pre ∋ α) :
    ⟦Subst.inst (⌊α⌋) ι⟧ˢ (.η p)
      =
    .ap ((ProperTele.inl pre) p)
      (fun i => ι (.here i)) := by
  rw [Expr.η.eq_1]
  change ⟦Subst.inst (⌊α⌋) ι⟧ˢ
      (.ap ((ProperTele.inl (pre ⋈* (⌊α⌋)))
        ((ProperTele.inl pre) p)) (fun i => .η (.here i))) = _
  rw [Subst.act_ap_inl_pre]
  change
    Expr.ap ((Subst.inst (⌊α⌋) ι).weakenCod p)
      (fun i => (Subst.inst (⌊α⌋) ι).act
        (⌊i.arity⌋) (.η (.here i)))
    =
    Expr.ap ((ProperTele.inl pre) p)
      (fun i => ι (.here i))
  change
    Expr.ap ((ProperTele.inl pre) p)
      (fun i => (Subst.inst (⌊α⌋) ι).act
        (⌊i.arity⌋) (.η (.here i)))
    =
    Expr.ap ((ProperTele.inl pre) p)
      (fun i => ι (.here i))
  congr
  funext i
  rw [Expr.η.eq_1]
  change (Subst.inst (⌊α⌋) ι).act (⌊i.arity⌋)
      (.ap ((ProperTele.inl (pre ⋈* (⌊α⌋)))
        ((ProperTele.inr pre) (.here i)))
        (fun k =>
          @Expr.η C
            ((pre ⋈* (⌊α⌋)) ⋈* (⌊i.arity⌋))
            k.arity (.here k))) = _
  rw [Subst.act_ap_inl_dom]
  rw [show (Subst.inst (⌊α⌋) ι).sub (.here i)
        = ι (.here i) from rfl]
  have hfill : ∀ (k : C.Binder i.arity),
      (Subst.inst (⌊α⌋) ι).act
        ((⌊i.arity⌋) ⋈ k.arity)
          (@Expr.η C
            ((pre ⋈* (⌊α⌋)) ⋈* (⌊i.arity⌋))
            k.arity (.here k))
      =
        @Expr.η C
          ((pre ⋈* cod) ⋈* (⌊i.arity⌋))
          k.arity (.here k) := by
    intro k
    exact Subst.act_η_inr (Subst.inst (⌊α⌋) ι)
      (⌊i.arity⌋) (x := .here k)
  simp only [hfill]
  change ⟦Subst.instId (pre ⋈* cod) i.arity⟧ˢ
    (ι (.here i)) = ι (.here i)
  exact Subst.act_inst.id i.arity (pre ⋈* cod) Shape.nil
    (ι (.here i))
termination_by α
decreasing_by exact ⟨i, rfl⟩

/-- Identity instantiation acts as the identity. -/
theorem Subst.act_inst.id {C : Carrier} (α : C.Arity) (Δ : Shape C) :
    ∀ (τ : Shape C) [ProperTele τ] (e : Expr ((Δ ⋈ α) ⋈* τ)),
      (Subst.instId Δ α).act τ e = e :=
  fun τ _ e =>
    Subst.act_inst.idOf α Δ (fun i => Subst.act_inst.η) τ e
termination_by α
decreasing_by exact ⟨i, rfl⟩

end

/-! ## Monad laws -/

/-- **`act_id`** — the identity substitution acts as the identity.
Translates to `lift η = 𝟙` (unit_right).  Generalised over τ so the
recursive call on each arg fits the same statement. -/
theorem Subst.act_id {C : Carrier} (Γ : Shape C) [ProperTele Γ]
    (τ : Shape C) [ProperTele τ]
    (e : Expr (Γ ⋈* τ)) :
    (Subst.id Γ).act τ e = e := by
  match e with
  | .ap (α := β) x args =>
    rcases ProperTele.cover Γ x with
      ⟨y, h_y⟩ | ⟨y, h_y⟩
    · -- head = inr x; the τ-side branch fires.
      subst h_y
      refine (Subst.act_ap_inr (Subst.id Γ) τ y args).trans ?_
      congr ; funext k ; apply Subst.act_id
    · -- head = inl y; y : Γ ∋ β.  Cover y at base Shape.nil:
      -- inl-from-nil is empty, so y is necessarily in the right image.
      subst h_y
      rcases ProperTele.cover Shape.nil y with ⟨y, h_q⟩ | ⟨z, _⟩
      · subst h_q
        refine (Subst.act_ap_inl_dom (Subst.id Γ) τ y args).trans ?_
        -- Simplify (Subst.id Γ) y = Expr.η y (rfl via toSubst_sub).
        show ⟦Subst.inst (⌊β⌋) (fun q => match q with
              | .here k => (Subst.id Γ).act (τ ⋈ k.arity) (args k))⟧ˢ
              (.η y) = _
        -- IH on each argument:
        have h_args : ∀ (k : C.Binder β),
            (Subst.id Γ).act (τ ⋈ k.arity) (args k) = args k :=
          fun k => Subst.act_id Γ (τ ⋈ k.arity) (args k)
        -- Simplify (inr Shape.nil) y = y on the RHS.
        rw [ProperTele.inr_nil_id y]
        refine (Subst.act_inst.η
          (pre := Γ) (cod := τ) (α := β) (ι := _) (p := y)).trans ?_
        change
          Expr.ap ((ProperTele.inl Γ) y)
            (fun k => (Subst.id Γ).act (τ ⋈ k.arity) (args k))
          =
          Expr.ap ((ProperTele.inl Γ) y) args
        congr 1
        funext k
        exact h_args k
      · exact nomatch z
termination_by (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args _

/-- **`act_η`** — acting on an η-expansion reduces to applying `f`.
Translates to `lift f ∘ η = f` (unit_left). -/
theorem Subst.act_η {C : Carrier} {Γ Δ : Shape C} [ProperTele Γ] [ProperTele Δ]
    (f : ∀ {β : C.Arity}, Γ ∋ β → Expr (Δ ⋈ β))
    (α : C.Arity) (p : Γ ∋ α) :
    (toSubst f).act (⌊α⌋) (.η p) = f p := by
  rw [Expr.η.eq_1]
  -- `.there p = (weaken_{⌊α⌋} _) p` by instCons.weaken (rfl).
  -- Cover p at base Shape.nil: p must be in the right image (inl-from-nil empty).
  rcases ProperTele.cover Shape.nil p with ⟨y, h_q⟩ | ⟨z, _⟩
  · subst h_q
    show (toSubst f).act (⌊α⌋)
        (.ap ((ProperTele.inl (Shape.nil ⋈* Γ))
                      ((ProperTele.inr Shape.nil) y))
                    (fun i => .η (.here i))) = _
    rw [Subst.act_ap_inl_dom (toSubst f) (⌊α⌋) y]
    have hfill : ∀ (i : C.Binder α),
        (toSubst f).act ((⌊α⌋) ⋈ i.arity)
          (@Expr.η C
            ((Shape.nil ⋈* Γ) ⋈* (⌊α⌋))
            i.arity (.here i))
        =
        @Expr.η C
          ((Shape.nil ⋈* Δ) ⋈* (⌊α⌋))
          i.arity (.here i) := by
      intro i
      exact Subst.act_η_inr (toSubst f) (⌊α⌋)
        (x := .here i)
    simp only [hfill]
    rw [toSubst_sub]
    rw [ProperTele.inr_nil_id y]
    change ⟦Subst.instId Δ α⟧ˢ (f y) = f y
    exact Subst.act_inst.id α Δ Shape.nil (f y)
  · exact nomatch z

private theorem Expr.Subterm.of_arg_ofList_cons {C : Carrier} {Γ : Shape C}
    (ρ : List C.Arity) {α : C.Arity}
    (head : Γ ⋈* Tele.ofList ρ ∋ α)
    (args : (i : C.Binder α) →
      Expr (Γ ⋈* Tele.ofList ρ ⋈ i.arity))
    (j : C.Binder α) :
    Expr.Subterm
      ⟨Γ ⋈* Tele.ofList (j.arity :: ρ), args j⟩
      ⟨Γ ⋈* Tele.ofList ρ, .ap head args⟩ := by
  simpa [Shape.extList, Shape.ext, Tele.comp, Tele.ofList] using
    (Expr.Subterm.of_arg head args j)

private theorem ListSlotAt.sub_single {C : Carrier} {α β : C.Arity}
    (x : (⌊α⌋ : Shape C) ∋ β) : Carrier.Sub β α := by
  cases x with
  | here i => exact ⟨i, rfl⟩
  | there z => nomatch z

/-! ## Statement facades for the interchange lemmas -/

/-- One-binder instantiation, written in binder-indexed form rather than
singleton-slot form. -/
private abbrev Subst.act_inst.instOne {C : Carrier} {pre cod : Shape C}
    (α : C.Arity)
    (fill : (i : C.Binder α) → Expr (pre ⋈* cod ⋈ i.arity)) :
    Subst C pre (⌊α⌋) cod :=
  Subst.inst (⌊α⌋) (fun q => match q with
  | .here i => fill i)

private abbrev Subst.act_inst.UnderList.actThenInst {C : Carrier}
    {pre dom cod τ : Shape C} [ProperTele dom] [ProperTele cod] [ProperTele τ]
    (σ : Subst C pre dom cod)
    {α : C.Arity}
    (ρ υ : List C.Arity)
    (ι : ∀ {β : C.Arity}, (⌊α⌋) ∋ β →
      Expr (pre ⋈* dom ⋈* τ ⋈* Tele.ofList ρ ⋈ β))
    (e : Expr ((pre ⋈* dom ⋈* τ ⋈ α) ⋈* Tele.ofList υ)) :=
  let κ' : Subst C (pre ⋈* cod ⋈* τ) (⌊α⌋) (Tele.ofList ρ) :=
    Subst.act_inst.instOne α (fun i =>
      σ.act ((τ ⋈* Tele.ofList ρ) ⋈ i.arity) (ι (.here i)))
  κ'.act (Tele.ofList υ)
    (σ.act ((τ ⋈ α) ⋈* Tele.ofList υ) e)

private abbrev Subst.act_inst.UnderList.instThenAct {C : Carrier}
    {pre dom cod τ : Shape C} [ProperTele dom] [ProperTele cod] [ProperTele τ]
    (σ : Subst C pre dom cod)
    {α : C.Arity}
    (ρ υ : List C.Arity)
    (ι : ∀ {β : C.Arity}, (⌊α⌋) ∋ β →
      Expr (pre ⋈* dom ⋈* τ ⋈* Tele.ofList ρ ⋈ β))
    (e : Expr ((pre ⋈* dom ⋈* τ ⋈ α) ⋈* Tele.ofList υ)) :=
  let κ : Subst C (pre ⋈* dom ⋈* τ) (⌊α⌋) (Tele.ofList ρ) :=
    Subst.act_inst.instOne α (fun i => ι (.here i))
  σ.act ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ)
    (κ.act (Tele.ofList υ) e)

private abbrev Subst.act_inst.PreLift.sequential {C : Carrier}
    {pre τ : Shape C} [ProperTele τ]
    {α β : C.Arity}
    (ρ υ χ : List C.Arity)
    (ι : ∀ {δ : C.Arity}, (⌊α⌋) ∋ δ →
      Expr (pre ⋈* τ ⋈* Tele.ofList ρ ⋈ δ))
    (η : (j : C.Binder β) →
      Expr ((pre ⋈* τ ⋈ α) ⋈* Tele.ofList υ ⋈ j.arity))
    (e : Expr ((pre ⋈ β) ⋈* Tele.ofList χ)) :=
  let κ : Subst C (pre ⋈* τ) (⌊α⌋) (Tele.ofList ρ) :=
    Subst.act_inst.instOne α (fun i => ι (.here i))
  let lam : Subst C pre (⌊β⌋) ((τ ⋈ α) ⋈* Tele.ofList υ) :=
    Subst.act_inst.instOne β η
  κ.act ((Tele.ofList υ : Shape C) ⋈* Tele.ofList χ)
    (lam.act (Tele.ofList χ) e)

private abbrev Subst.act_inst.PreLift.fused {C : Carrier}
    {pre τ : Shape C} [ProperTele τ]
    {α β : C.Arity}
    (ρ υ χ : List C.Arity)
    (ι : ∀ {δ : C.Arity}, (⌊α⌋) ∋ δ →
      Expr (pre ⋈* τ ⋈* Tele.ofList ρ ⋈ δ))
    (η : (j : C.Binder β) →
      Expr ((pre ⋈* τ ⋈ α) ⋈* Tele.ofList υ ⋈ j.arity))
    (e : Expr ((pre ⋈ β) ⋈* Tele.ofList χ)) :=
  let κ : Subst C (pre ⋈* τ) (⌊α⌋) (Tele.ofList ρ) :=
    Subst.act_inst.instOne α (fun i => ι (.here i))
  let lam' : Subst C pre (⌊β⌋)
      ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ) :=
    Subst.act_inst.instOne β (fun j =>
      κ.act (Tele.ofList υ ⋈ j.arity) (η j))
  lam'.act (Tele.ofList χ) e

private abbrev Subst.act_inst.PreNaturality.sequential {C : Carrier}
    {pre dom cod : Shape C} [ProperTele dom] [ProperTele cod]
    (σ : Subst C pre dom cod)
    {α : C.Arity}
    (ρ υ : List C.Arity)
    (ι : ∀ {β : C.Arity}, (⌊α⌋) ∋ β →
      Expr (pre ⋈* dom ⋈* Tele.ofList ρ ⋈ β))
    (e : Expr ((pre ⋈ α) ⋈* Tele.ofList υ)) :=
  let κ : Subst C pre (⌊α⌋) (dom ⋈* Tele.ofList ρ) :=
    Subst.act_inst.instOne α (fun i => ι (.here i))
  σ.act ((Tele.ofList ρ : Shape C) ⋈* Tele.ofList υ)
    (κ.act (Tele.ofList υ) e)

private abbrev Subst.act_inst.PreNaturality.fused {C : Carrier}
    {pre dom cod : Shape C} [ProperTele dom] [ProperTele cod]
    (σ : Subst C pre dom cod)
    {α : C.Arity}
    (ρ υ : List C.Arity)
    (ι : ∀ {β : C.Arity}, (⌊α⌋) ∋ β →
      Expr (pre ⋈* dom ⋈* Tele.ofList ρ ⋈ β))
    (e : Expr ((pre ⋈ α) ⋈* Tele.ofList υ)) :=
  let κ' : Subst C pre (⌊α⌋) (cod ⋈* Tele.ofList ρ) :=
    Subst.act_inst.instOne α (fun i =>
      σ.act (Tele.ofList ρ ⋈ i.arity) (ι (.here i)))
  κ'.act (Tele.ofList υ) e

private abbrev Subst.act_inst.Interchange.actThenInst {C : Carrier}
    {pre dom cod τ : Shape C} [ProperTele dom] [ProperTele cod] [ProperTele τ]
    (σ : Subst C pre dom cod)
    {α : C.Arity}
    (ι : ∀ {β : C.Arity}, (⌊α⌋) ∋ β →
      Expr (pre ⋈* dom ⋈* τ ⋈ β))
    (ρ : List C.Arity)
    (e : Expr (pre ⋈* dom ⋈* (⌊α⌋) ⋈* Tele.ofList ρ)) :=
  let κ' : Subst C (pre ⋈* cod) (⌊α⌋) τ :=
    Subst.act_inst.instOne α (fun i =>
      σ.act (τ ⋈ i.arity) (ι (.here i)))
  κ'.act (Tele.ofList ρ)
    (σ.act ((⌊α⌋) ⋈* Tele.ofList ρ) e)

private abbrev Subst.act_inst.Interchange.instThenAct {C : Carrier}
    {pre dom cod τ : Shape C} [ProperTele dom] [ProperTele cod] [ProperTele τ]
    (σ : Subst C pre dom cod)
    {α : C.Arity}
    (ι : ∀ {β : C.Arity}, (⌊α⌋) ∋ β →
      Expr (pre ⋈* dom ⋈* τ ⋈ β))
    (ρ : List C.Arity)
    (e : Expr (pre ⋈* dom ⋈* (⌊α⌋) ⋈* Tele.ofList ρ)) :=
  let κ : Subst C (pre ⋈* dom) (⌊α⌋) τ :=
    Subst.act_inst.instOne α (fun i => ι (.here i))
  σ.act (τ ⋈* Tele.ofList ρ)
    (κ.act (Tele.ofList ρ) e)

/-- Two active substitution-domain fuels, considered up to swapping.  The mutual
interchange proof either descends in one fuel component or keeps the fuel fixed
and descends into an expression argument. -/
private structure InterchangeFuel (C : Carrier) where
  fst : DomMeasure C
  snd : DomMeasure C

private inductive InterchangeFuel.Lt {C : Carrier} :
    InterchangeFuel C → InterchangeFuel C → Prop where
  | left {a b a' : DomMeasure C}
      (h : WellFoundedRelation.rel a' a) :
      InterchangeFuel.Lt ⟨a', b⟩ ⟨a, b⟩
  | right {a b b' : DomMeasure C}
      (h : WellFoundedRelation.rel b' b) :
      InterchangeFuel.Lt ⟨a, b'⟩ ⟨a, b⟩
  | left_swap {a b a' : DomMeasure C}
      (h : WellFoundedRelation.rel a' a) :
      InterchangeFuel.Lt ⟨b, a'⟩ ⟨a, b⟩
  | right_swap {a b b' : DomMeasure C}
      (h : WellFoundedRelation.rel b' b) :
      InterchangeFuel.Lt ⟨b', a⟩ ⟨a, b⟩

private theorem InterchangeFuel.Lt.accPair {C : Carrier}
    (a b : DomMeasure C) :
    Acc (InterchangeFuel.Lt (C := C)) ⟨a, b⟩ ∧
      Acc (InterchangeFuel.Lt (C := C)) ⟨b, a⟩ := by
  let wf : WellFounded
      (WellFoundedRelation.rel : DomMeasure C → DomMeasure C → Prop) :=
    WellFoundedRelation.wf
  exact WellFounded.induction wf a (C := fun a =>
      ∀ b : DomMeasure C,
        Acc (InterchangeFuel.Lt (C := C)) ⟨a, b⟩ ∧
          Acc (InterchangeFuel.Lt (C := C)) ⟨b, a⟩)
    (fun a IHa b =>
      WellFounded.induction wf b (C := fun b =>
          Acc (InterchangeFuel.Lt (C := C)) ⟨a, b⟩ ∧
            Acc (InterchangeFuel.Lt (C := C)) ⟨b, a⟩)
        (fun b IHb => by
          constructor
          · refine Acc.intro _ ?_
            intro y hy
            cases y with
            | mk y₀ y₁ =>
                cases hy with
                | left h =>
                    exact (IHa y₀ h b).1
                | right h =>
                    exact (IHb y₁ h).1
                | left_swap h =>
                    exact (IHa y₁ h b).2
                | right_swap h =>
                    exact (IHb y₀ h).2
          · refine Acc.intro _ ?_
            intro y hy
            cases y with
            | mk y₀ y₁ =>
                cases hy with
                | left h =>
                    exact (IHb y₀ h).2
                | right h =>
                    exact (IHa y₁ h b).2
                | left_swap h =>
                    exact (IHb y₁ h).1
                | right_swap h =>
                    exact (IHa y₀ h b).1))
    b

private theorem InterchangeFuel.Lt.wf {C : Carrier} :
    WellFounded (InterchangeFuel.Lt (C := C)) := by
  refine ⟨fun f => ?_⟩
  cases f with
  | mk a b =>
      exact (InterchangeFuel.Lt.accPair a b).1

private instance {C : Carrier} : WellFoundedRelation (InterchangeFuel C) where
  rel := InterchangeFuel.Lt
  wf := InterchangeFuel.Lt.wf

mutual

private theorem Subst.act_inst.underListAt {C : Carrier}
    {pre dom cod τ : Shape C} [ProperTele dom] [ProperTele cod] [ProperTele τ]
    (σ : Subst C pre dom cod)
    {α : C.Arity}
    (ρ υ : List C.Arity)
    (ι : ∀ {β : C.Arity}, (⌊α⌋) ∋ β →
      Expr (pre ⋈* dom ⋈* τ ⋈* Tele.ofList ρ ⋈ β))
    (e : Expr ((pre ⋈* dom ⋈* τ ⋈ α) ⋈* Tele.ofList υ)) :
    Subst.act_inst.UnderList.actThenInst σ ρ υ ι e =
    Subst.act_inst.UnderList.instThenAct σ ρ υ ι e := by
  let κ : Subst C (pre ⋈* dom ⋈* τ) (⌊α⌋) (Tele.ofList ρ) :=
    Subst.inst (⌊α⌋) (fun q => match q with
    | .here i => ι (.here i))
  let κ' : Subst C (pre ⋈* cod ⋈* τ) (⌊α⌋) (Tele.ofList ρ) :=
    Subst.inst (⌊α⌋) (fun q => match q with
    | .here i =>
        σ.act ((τ ⋈* Tele.ofList ρ) ⋈ i.arity) (ι (.here i)))
  change κ'.act (Tele.ofList υ)
      (σ.act ((τ ⋈ α) ⋈* Tele.ofList υ) e)
    =
    σ.act ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ)
      (κ.act (Tele.ofList υ) e)
  match e with
  | .ap (α := β) head args =>
    rcases @ProperTele.cover C ((τ ⋈ α) ⋈* Tele.ofList υ)
        (by exact ProperTele.extendList (τ ⋈ α) υ)
        (pre ⋈* dom) β head with
      ⟨top, h_top⟩ | ⟨below, h_below⟩
    · subst h_top
      rcases @ProperTele.cover C (Tele.ofList υ)
          (by exact ProperTele.ofList υ)
          (τ ⋈ α) β top with
        ⟨xυ, h_xυ⟩ | ⟨xt, h_xt⟩
      · subst h_xυ
        refine (congrArg (κ'.act (Tele.ofList υ))
          (Subst.act_ap_inr σ
            ((τ ⋈ α) ⋈* Tele.ofList υ)
            ((ProperTele.inr (τ ⋈ α)) xυ) args)).trans ?_
        rw [ProperTele.extendList_inr_inr (τ ⋈ α) υ (pre ⋈* cod) xυ]
        refine (Subst.act_ap_inr κ' (Tele.ofList υ) xυ
          (fun j => σ.act (((τ ⋈ α) ⋈* Tele.ofList υ) ⋈ j.arity)
            (args j))).trans ?_
        have hκ :
            κ.act (Tele.ofList υ)
              (.ap
                ((ProperTele.inr ((pre ⋈* dom) ⋈* (τ ⋈ α))) xυ)
                args)
            =
            .ap
              ((ProperTele.inr ((pre ⋈* dom ⋈* τ) ⋈* Tele.ofList ρ)) xυ)
              (fun j => κ.act (Tele.ofList υ ⋈ j.arity) (args j)) := by
          exact Subst.act_ap_inr κ (Tele.ofList υ) xυ args
        have hκ_nested :
            κ.act (Tele.ofList υ)
              (.ap
                ((ProperTele.inr (pre ⋈* dom))
                  ((ProperTele.inr (τ ⋈ α)) xυ))
                args)
            =
            .ap
              ((ProperTele.inr ((pre ⋈* dom ⋈* τ) ⋈* Tele.ofList ρ)) xυ)
              (fun j => κ.act (Tele.ofList υ ⋈ j.arity) (args j)) := by
          rw [ProperTele.extendList_inr_inr (τ ⋈ α) υ (pre ⋈* dom) xυ]
          exact hκ
        refine Eq.trans ?_ (congrArg
          (σ.act ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ))
          hκ_nested).symm
        change .ap
            ((ProperTele.inr ((pre ⋈* cod) ⋈* (τ ⋈* Tele.ofList ρ))) xυ)
            (fun j => κ'.act (Tele.ofList υ ⋈ j.arity)
              (σ.act (((τ ⋈ α) ⋈* Tele.ofList υ) ⋈ j.arity) (args j)))
          =
          σ.act ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ)
            (.ap
              ((ProperTele.inr ((pre ⋈* dom) ⋈* (τ ⋈* Tele.ofList ρ))) xυ)
              (fun j => κ.act (Tele.ofList υ ⋈ j.arity) (args j)))
        have hσ :
            σ.act ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ)
              (.ap
                ((ProperTele.inr ((pre ⋈* dom) ⋈* (τ ⋈* Tele.ofList ρ))) xυ)
                (fun j => κ.act (Tele.ofList υ ⋈ j.arity) (args j)))
            =
            .ap
              ((ProperTele.inr ((pre ⋈* cod) ⋈* (τ ⋈* Tele.ofList ρ))) xυ)
              (fun j =>
                σ.act (((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ) ⋈ j.arity)
                  (κ.act (Tele.ofList υ ⋈ j.arity) (args j))) := by
          rw [← ProperTele.extendList_inr_inr
            (τ ⋈* Tele.ofList ρ) υ (pre ⋈* dom) xυ]
          rw [Subst.act_ap_inr σ
            ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ)
            ((ProperTele.inr (τ ⋈* Tele.ofList ρ)) xυ)
            (fun j => κ.act (Tele.ofList υ ⋈ j.arity) (args j))]
          rw [ProperTele.extendList_inr_inr
            (τ ⋈* Tele.ofList ρ) υ (pre ⋈* cod) xυ]
        refine Eq.trans ?_ hσ.symm
        congr 1
        funext j
        change κ'.act (Tele.ofList (j.arity :: υ))
            (σ.act ((τ ⋈ α) ⋈* Tele.ofList (j.arity :: υ)) (args j))
          =
          σ.act ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList (j.arity :: υ))
            (κ.act (Tele.ofList (j.arity :: υ)) (args j))
        exact Subst.act_inst.underListAt σ ρ (j.arity :: υ) ι (args j)
      · subst h_xt
        rcases @ProperTele.cover C (⌊α⌋) inferInstance
            τ β xt with
          ⟨xα, h_xα⟩ | ⟨xτ, h_xτ⟩
        · subst h_xα
          have hfillTop : ∀ (j : C.Binder β),
              κ'.act (Tele.ofList υ ⋈ j.arity)
                  (σ.act ((((τ ⋈ α) ⋈* Tele.ofList υ) ⋈ j.arity))
                    (args j))
                =
              σ.act ((((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ) ⋈ j.arity))
                  (κ.act (Tele.ofList υ ⋈ j.arity) (args j)) := by
            intro j
            change κ'.act (Tele.ofList (j.arity :: υ))
                (σ.act ((τ ⋈ α) ⋈* Tele.ofList (j.arity :: υ)) (args j))
              =
              σ.act ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList (j.arity :: υ))
                (κ.act (Tele.ofList (j.arity :: υ)) (args j))
            exact Subst.act_inst.underListAt σ ρ (j.arity :: υ) ι (args j)
          refine (congrArg (κ'.act (Tele.ofList υ))
            (Subst.act_ap_inr σ
              ((τ ⋈ α) ⋈* Tele.ofList υ)
              ((ProperTele.inl (τ ⋈ α))
                ((ProperTele.inr τ) xα))
              args)).trans ?_
          have hheadCod :
              ((ProperTele.inr (pre ⋈* cod))
                (((ProperTele.inl (τ ⋈ α)) :
                    (τ ⋈ α) →ʳ (τ ⋈ α) ⋈* Tele.ofList υ)
                  ((ProperTele.inr τ) xα)))
              =
              ((ProperTele.inl ((pre ⋈* cod) ⋈* (τ ⋈ α)))
                ((ProperTele.inr (pre ⋈* cod))
                  ((ProperTele.inr τ) xα))) :=
            ProperTele.extendList_inr_inl
              (τ ⋈ α) υ (pre ⋈* cod)
              ((ProperTele.inr τ) xα)
          refine (congrArg
            (fun head => κ'.act (Tele.ofList υ)
              (.ap head
                (fun j => σ.act (((τ ⋈ α) ⋈* Tele.ofList υ) ⋈ j.arity)
                  (args j))))
            hheadCod).trans ?_
          have hheadCod' :
              (((ProperTele.inl ((pre ⋈* cod) ⋈* (τ ⋈ α))) :
                  ((pre ⋈* cod) ⋈* (τ ⋈ α)) →ʳ
                    ((pre ⋈* cod) ⋈* (τ ⋈ α)) ⋈* Tele.ofList υ)
                ((ProperTele.inr (pre ⋈* cod))
                  ((ProperTele.inr τ) xα)))
              =
              (((ProperTele.inl ((pre ⋈* cod ⋈* τ) ⋈* (⌊α⌋))) :
                  ((pre ⋈* cod ⋈* τ) ⋈* (⌊α⌋)) →ʳ
                    ((pre ⋈* cod ⋈* τ) ⋈* (⌊α⌋)) ⋈* Tele.ofList υ)
                ((ProperTele.inr (pre ⋈* cod ⋈* τ)) xα)) := by
            change
              (((ProperTele.inl ((pre ⋈* cod) ⋈* (τ ⋈ α))) :
                  ((pre ⋈* cod) ⋈* (τ ⋈ α)) →ʳ
                    ((pre ⋈* cod) ⋈* (τ ⋈ α)) ⋈* Tele.ofList υ)
                ((ProperTele.inr (pre ⋈* cod))
                  ((ProperTele.inr τ) xα)))
              =
              (((ProperTele.inl ((pre ⋈* cod ⋈* τ) ⋈* (⌊α⌋))) :
                  ((pre ⋈* cod ⋈* τ) ⋈* (⌊α⌋)) →ʳ
                    ((pre ⋈* cod ⋈* τ) ⋈* (⌊α⌋)) ⋈* Tele.ofList υ)
                ((ProperTele.inr (pre ⋈* cod ⋈* τ)) xα))
            cases xα with
            | here i => rfl
            | there z => nomatch z
          refine (congrArg
            (fun head => κ'.act (Tele.ofList υ)
              (.ap head
                (fun j => σ.act (((τ ⋈ α) ⋈* Tele.ofList υ) ⋈ j.arity)
                  (args j))))
            hheadCod').trans ?_
          refine (Subst.act_ap_inl_dom κ' (Tele.ofList υ)
            xα
            (fun j => σ.act (((τ ⋈ α) ⋈* Tele.ofList υ) ⋈ j.arity)
              (args j))).trans ?_
          have hκ'sub :
              κ'.sub xα = σ.act ((τ ⋈* Tele.ofList ρ) ⋈ β) (ι xα) := by
            cases xα with
            | here i => rfl
            | there z => nomatch z
          rw [hκ'sub]
          have hheadDom :
              ((ProperTele.inr (pre ⋈* dom))
                (((ProperTele.inl (τ ⋈ α)) :
                    (τ ⋈ α) →ʳ (τ ⋈ α) ⋈* Tele.ofList υ)
                  ((ProperTele.inr τ) xα)))
              =
              ((ProperTele.inl ((pre ⋈* dom) ⋈* (τ ⋈ α)))
                ((ProperTele.inr (pre ⋈* dom))
                  ((ProperTele.inr τ) xα))) :=
            ProperTele.extendList_inr_inl
              (τ ⋈ α) υ (pre ⋈* dom)
              ((ProperTele.inr τ) xα)
          have hheadDom' :
              (((ProperTele.inl ((pre ⋈* dom) ⋈* (τ ⋈ α))) :
                  ((pre ⋈* dom) ⋈* (τ ⋈ α)) →ʳ
                    ((pre ⋈* dom) ⋈* (τ ⋈ α)) ⋈* Tele.ofList υ)
                ((ProperTele.inr (pre ⋈* dom))
                  ((ProperTele.inr τ) xα)))
              =
              (((ProperTele.inl ((pre ⋈* dom ⋈* τ) ⋈* (⌊α⌋))) :
                  ((pre ⋈* dom ⋈* τ) ⋈* (⌊α⌋)) →ʳ
                    ((pre ⋈* dom ⋈* τ) ⋈* (⌊α⌋)) ⋈* Tele.ofList υ)
                ((ProperTele.inr (pre ⋈* dom ⋈* τ)) xα)) := by
            change
              (((ProperTele.inl ((pre ⋈* dom) ⋈* (τ ⋈ α))) :
                  ((pre ⋈* dom) ⋈* (τ ⋈ α)) →ʳ
                    ((pre ⋈* dom) ⋈* (τ ⋈ α)) ⋈* Tele.ofList υ)
                ((ProperTele.inr (pre ⋈* dom))
                  ((ProperTele.inr τ) xα)))
              =
              (((ProperTele.inl ((pre ⋈* dom ⋈* τ) ⋈* (⌊α⌋))) :
                  ((pre ⋈* dom ⋈* τ) ⋈* (⌊α⌋)) →ʳ
                    ((pre ⋈* dom ⋈* τ) ⋈* (⌊α⌋)) ⋈* Tele.ofList υ)
                ((ProperTele.inr (pre ⋈* dom ⋈* τ)) xα))
            cases xα with
            | here i => rfl
            | there z => nomatch z
          have hκ :=
            (congrArg
              (fun head => κ.act (Tele.ofList υ) (.ap head args))
              hheadDom).trans
            ((congrArg
              (fun head => κ.act (Tele.ofList υ) (.ap head args))
              hheadDom').trans
            (Subst.act_ap_inl_dom κ (Tele.ofList υ) xα args))
          refine Eq.trans ?_
            (congrArg (σ.act ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ))
              hκ).symm
          have hκsub : κ.sub xα = ι xα := by
            cases xα with
            | here i => rfl
            | there z => nomatch z
          rw [hκsub]
          let ιβ : ∀ {δ : C.Arity}, (⌊β⌋) ∋ δ →
              Expr (pre ⋈* dom ⋈* (τ ⋈* Tele.ofList ρ) ⋈*
                Tele.ofList υ ⋈ δ) :=
            fun q => match q with
            | .here j => κ.act (Tele.ofList υ ⋈ j.arity) (args j)
          simp only [hfillTop]
          simpa only [ιβ] using
            (Subst.act_inst.underListAt
              (τ := τ ⋈* Tele.ofList ρ) σ υ [] (ι := ιβ)
              (e := ι xα))
        · subst h_xτ
          refine (congrArg (κ'.act (Tele.ofList υ))
            (Subst.act_ap_inr σ
              ((τ ⋈ α) ⋈* Tele.ofList υ)
              ((ProperTele.inl (τ ⋈ α))
                ((ProperTele.inl τ) xτ))
              args)).trans ?_
          change κ'.act (Tele.ofList υ)
              (.ap
                ((ProperTele.inr (pre ⋈* cod))
                  ((ProperTele.inl (τ ⋈ α))
                    ((ProperTele.inl τ) xτ)))
                (fun j => σ.act (((τ ⋈ α) ⋈* Tele.ofList υ) ⋈ j.arity)
                  (args j)))
            =
            σ.act ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ)
              (κ.act (Tele.ofList υ)
                (.ap
                  ((ProperTele.inr (pre ⋈* dom))
                    ((ProperTele.inl (τ ⋈ α))
                      ((ProperTele.inl τ) xτ)))
                  args))
          rw [ProperTele.extendList_inr_inl
            (τ ⋈ α) υ (pre ⋈* cod) ((ProperTele.inl τ) xτ)]
          refine (Subst.act_ap_inl_pre κ' (Tele.ofList υ)
            ((ProperTele.inr (pre ⋈* cod)) xτ)
            (fun j => σ.act (((τ ⋈ α) ⋈* Tele.ofList υ) ⋈ j.arity)
              (args j))).trans ?_
          have hκ :
              κ.act (Tele.ofList υ)
                (.ap
                  ((ProperTele.inr (pre ⋈* dom))
                    ((ProperTele.inl (τ ⋈ α))
                      ((ProperTele.inl τ) xτ)))
                  args)
              =
              .ap
                ((ProperTele.inl ((pre ⋈* dom ⋈* τ) ⋈* Tele.ofList ρ))
                  ((ProperTele.inl (pre ⋈* dom ⋈* τ))
                    ((ProperTele.inr (pre ⋈* dom)) xτ)))
                (fun j => κ.act (Tele.ofList υ ⋈ j.arity) (args j)) := by
            rw [ProperTele.extendList_inr_inl
              (τ ⋈ α) υ (pre ⋈* dom) ((ProperTele.inl τ) xτ)]
            exact Subst.act_ap_inl_pre κ (Tele.ofList υ)
              ((ProperTele.inr (pre ⋈* dom)) xτ) args
          refine Eq.trans ?_
            (congrArg (σ.act ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ)) hκ).symm
          unfold Subst.weakenCod
          rw [← ProperTele.extendList_inr_inl τ ρ (pre ⋈* dom) xτ]
          change .ap
              ((ProperTele.inl (pre ⋈* cod ⋈* τ ⋈* Tele.ofList ρ))
                ((ProperTele.inl (pre ⋈* cod ⋈* τ))
                  ((ProperTele.inr (pre ⋈* cod)) xτ)))
              (fun j => κ'.act (Tele.ofList υ ⋈ j.arity)
                (σ.act (((τ ⋈ α) ⋈* Tele.ofList υ) ⋈ j.arity) (args j)))
            =
            σ.act ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ)
              (.ap
                ((ProperTele.inl ((pre ⋈* dom) ⋈* (τ ⋈* Tele.ofList ρ)))
                  ((ProperTele.inr (pre ⋈* dom))
                    ((ProperTele.inl τ) xτ)))
                (fun j => κ.act (Tele.ofList υ ⋈ j.arity) (args j)))
          rw [← ProperTele.extendList_inr_inl
            (τ ⋈* Tele.ofList ρ) υ (pre ⋈* dom)
            ((ProperTele.inl τ) xτ)]
          refine Eq.trans ?_ (Subst.act_ap_inr σ
            ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ)
            ((ProperTele.inl (τ ⋈* Tele.ofList ρ))
              ((ProperTele.inl τ) xτ))
            (fun j => κ.act (Tele.ofList υ ⋈ j.arity) (args j))).symm
          rw [← ProperTele.extendList_inr_inl τ ρ (pre ⋈* cod) xτ]
          change Expr.ap
              ((ProperTele.inl (pre ⋈* cod ⋈* (τ ⋈* Tele.ofList ρ)))
                ((ProperTele.inr (pre ⋈* cod))
                  ((ProperTele.inl τ) xτ)))
              (fun j => κ'.act (Tele.ofList υ ⋈ j.arity)
                (σ.act (((τ ⋈ α) ⋈* Tele.ofList υ) ⋈ j.arity) (args j)))
            =
            Expr.ap
              ((ProperTele.inr (pre ⋈* cod))
                ((ProperTele.inl (τ ⋈* Tele.ofList ρ))
                  ((ProperTele.inl τ) xτ)))
              (fun j =>
                σ.act (((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ) ⋈ j.arity)
                  (κ.act (Tele.ofList υ ⋈ j.arity) (args j)))
          rw [← ProperTele.extendList_inr_inl
            (τ ⋈* Tele.ofList ρ) υ (pre ⋈* cod)
            ((ProperTele.inl τ) xτ)]
          congr 1
          funext j
          change κ'.act (Tele.ofList (j.arity :: υ))
              (σ.act ((τ ⋈ α) ⋈* Tele.ofList (j.arity :: υ)) (args j))
            =
            σ.act ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList (j.arity :: υ))
              (κ.act (Tele.ofList (j.arity :: υ)) (args j))
          exact Subst.act_inst.underListAt σ ρ (j.arity :: υ) ι (args j)
    · subst h_below
      rcases ProperTele.cover pre below with ⟨z, h_z⟩ | ⟨z, h_z⟩
      · subst h_z
        refine (congrArg (κ'.act (Tele.ofList υ))
          (Subst.act_ap_inl_dom σ
            ((τ ⋈ α) ⋈* Tele.ofList υ) z args)).trans ?_
        let η : (j : C.Binder β) →
            Expr (((pre ⋈* cod) ⋈* τ ⋈ α) ⋈* Tele.ofList υ ⋈ j.arity) :=
          fun j => σ.act (((τ ⋈ α) ⋈* Tele.ofList υ) ⋈ j.arity) (args j)
        let ιcod : ∀ {δ : C.Arity}, (⌊α⌋) ∋ δ →
            Expr ((pre ⋈* cod) ⋈* τ ⋈* Tele.ofList ρ ⋈ δ) :=
          fun q => match q with
          | .here i => σ.act ((τ ⋈* Tele.ofList ρ) ⋈ i.arity)
              (ι (.here i))
        refine (Subst.act_inst.preNaturalityLiftAt
          (pre := pre ⋈* cod) (τ := τ) ρ υ []
          (ι := ιcod) (η := η) (e := σ z)).trans ?_
        have hfill : ∀ (j : C.Binder β),
            κ'.act (Tele.ofList υ ⋈ j.arity)
                (σ.act (((τ ⋈ α) ⋈* Tele.ofList υ) ⋈ j.arity)
                  (args j))
              =
            σ.act (((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ) ⋈ j.arity)
                (κ.act (Tele.ofList υ ⋈ j.arity) (args j)) := by
          intro j
          change κ'.act (Tele.ofList (j.arity :: υ))
              (σ.act ((τ ⋈ α) ⋈* Tele.ofList (j.arity :: υ)) (args j))
            =
            σ.act ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList (j.arity :: υ))
              (κ.act (Tele.ofList (j.arity :: υ)) (args j))
          exact Subst.act_inst.underListAt σ ρ (j.arity :: υ) ι (args j)
        simp only [η, ιcod]
        let ζ₀ : ∀ {δ : C.Arity}, (⌊β⌋) ∋ δ →
            Expr ((pre ⋈* cod) ⋈*
              ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ) ⋈ δ) :=
          fun q => match q with
          | .here j =>
              κ'.act (Tele.ofList υ ⋈ j.arity)
                (σ.act (((τ ⋈ α) ⋈* Tele.ofList υ) ⋈ j.arity)
                  (args j))
        let ζ₁ : ∀ {δ : C.Arity}, (⌊β⌋) ∋ δ →
            Expr ((pre ⋈* cod) ⋈*
              ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ) ⋈ δ) :=
          fun q => match q with
          | .here j =>
              σ.act (((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ) ⋈ j.arity)
                (κ.act (Tele.ofList υ ⋈ j.arity) (args j))
        have hζ :
            (fun {δ : C.Arity} (q : (⌊β⌋) ∋ δ) => ζ₀ q)
              =
            (fun {δ : C.Arity} (q : (⌊β⌋) ∋ δ) => ζ₁ q) := by
          funext δ q
          cases q with
          | here j =>
              exact hfill j
          | there q => nomatch q
        change ⟦Subst.inst (C := C) (pre := pre ⋈* cod)
              (dom := ⌊β⌋)
              (cod := (τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ)
              ζ₀⟧ˢ (σ z)
            =
            σ.act ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ)
              (κ.act (Tele.ofList υ)
                (.ap
                  (((ProperTele.inl (pre ⋈* dom)) :
                      (pre ⋈* dom) →ʳ
                        (pre ⋈* dom) ⋈* ((τ ⋈ α) ⋈* Tele.ofList υ))
                    ((ProperTele.inr pre) z))
                  args))
        rw [hζ]
        have hκ :
            κ.act (Tele.ofList υ)
              (.ap
                (((ProperTele.inl (pre ⋈* dom)) :
                    (pre ⋈* dom) →ʳ
                      (pre ⋈* dom) ⋈* ((τ ⋈ α) ⋈* Tele.ofList υ))
                  ((ProperTele.inr pre) z))
                args)
            =
            .ap
              ((ProperTele.inl ((pre ⋈* dom ⋈* τ) ⋈* Tele.ofList ρ))
                ((ProperTele.inl (pre ⋈* dom ⋈* τ))
                  ((ProperTele.inl (pre ⋈* dom))
                    ((ProperTele.inr pre) z))))
              (fun j => κ.act (Tele.ofList υ ⋈ j.arity) (args j)) := by
          rw [ProperTele.extendList_inl
            (τ ⋈ α) υ (pre ⋈* dom) ((ProperTele.inr pre) z)]
          exact Subst.act_ap_inl_pre κ (Tele.ofList υ)
            ((ProperTele.inl (pre ⋈* dom))
              ((ProperTele.inr pre) z)) args
        refine Eq.trans ?_
          (congrArg (σ.act ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ)) hκ).symm
        rw [← ProperTele.extendList_inl τ ρ (pre ⋈* dom)
          ((ProperTele.inr pre) z)]
        change ⟦Subst.inst (C := C) (pre := pre ⋈* cod)
              (dom := ⌊β⌋)
              (cod := (τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ)
              (fun {δ} q => ζ₁ (δ := δ) q)⟧ˢ (σ z)
            =
            σ.act ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ)
              (.ap
                ((ProperTele.inl
                    (pre ⋈* dom ⋈* (τ ⋈* Tele.ofList ρ)))
                  (((ProperTele.inl (pre ⋈* dom)) :
                      (pre ⋈* dom) →ʳ
                        pre ⋈* dom ⋈* (τ ⋈* Tele.ofList ρ))
                    ((ProperTele.inr pre) z)))
                (fun j => κ.act (Tele.ofList υ ⋈ j.arity) (args j)))
        rw [← ProperTele.extendList_inl
          (τ ⋈* Tele.ofList ρ) υ (pre ⋈* dom)
          ((ProperTele.inr pre) z)]
        exact (Subst.act_ap_inl_dom σ
          ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ) z
          (fun j => κ.act (Tele.ofList υ ⋈ j.arity) (args j))).symm
      · subst h_z
        refine (congrArg (κ'.act (Tele.ofList υ))
          (Subst.act_ap_inl_pre σ
            ((τ ⋈ α) ⋈* Tele.ofList υ) z args)).trans ?_
        rw [ProperTele.extendList_inl
          (τ ⋈ α) υ (pre ⋈* cod) ((Subst.weakenCod σ) z)]
        refine (Subst.act_ap_inl_pre κ' (Tele.ofList υ)
          ((ProperTele.inl (pre ⋈* cod))
            ((Subst.weakenCod σ) z))
          (fun j => σ.act (((τ ⋈ α) ⋈* Tele.ofList υ) ⋈ j.arity)
            (args j))).trans ?_
        have hκ :
            κ.act (Tele.ofList υ)
              (.ap
                (((ProperTele.inl (pre ⋈* dom)) :
                    (pre ⋈* dom) →ʳ
                      (pre ⋈* dom) ⋈* ((τ ⋈ α) ⋈* Tele.ofList υ))
                  ((ProperTele.inl pre) z))
                args)
            =
            .ap
              ((ProperTele.inl ((pre ⋈* dom ⋈* τ) ⋈* Tele.ofList ρ))
                ((ProperTele.inl (pre ⋈* dom ⋈* τ))
                  ((ProperTele.inl (pre ⋈* dom))
                    ((ProperTele.inl pre) z))))
              (fun j => κ.act (Tele.ofList υ ⋈ j.arity) (args j)) := by
          rw [ProperTele.extendList_inl
            (τ ⋈ α) υ (pre ⋈* dom) ((ProperTele.inl pre) z)]
          exact Subst.act_ap_inl_pre κ (Tele.ofList υ)
            ((ProperTele.inl (pre ⋈* dom))
              ((ProperTele.inl pre) z)) args
        refine Eq.trans ?_
          (congrArg (σ.act ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ)) hκ).symm
        unfold Subst.weakenCod
        rw [← ProperTele.extendList_inl τ ρ (pre ⋈* cod)
          ((ProperTele.inl pre) z)]
        change (.ap
            ((ProperTele.inl
                (pre ⋈* cod ⋈* (τ ⋈* Tele.ofList ρ)))
              (((ProperTele.inl (pre ⋈* cod)) :
                  (pre ⋈* cod) →ʳ
                    pre ⋈* cod ⋈* (τ ⋈* Tele.ofList ρ))
                ((ProperTele.inl pre) z)))
            (fun i => κ'.act (Tele.ofList υ ⋈ i.arity)
              (σ.act (((τ ⋈ α) ⋈* Tele.ofList υ) ⋈ i.arity)
                (args i)))
          =
          σ.act ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ)
            (.ap
              ((ProperTele.inl (pre ⋈* dom ⋈* τ ⋈* Tele.ofList ρ))
                ((ProperTele.inl (pre ⋈* dom ⋈* τ))
                  ((ProperTele.inl (pre ⋈* dom))
                    ((ProperTele.inl pre) z))))
              (fun j => κ.act (Tele.ofList υ ⋈ j.arity) (args j))))
        rw [← ProperTele.extendList_inl
          (τ ⋈* Tele.ofList ρ) υ (pre ⋈* cod)
          ((ProperTele.inl pre) z)]
        rw [← ProperTele.extendList_inl τ ρ (pre ⋈* dom)
          ((ProperTele.inl pre) z)]
        change .ap
            (((ProperTele.inl (pre ⋈* cod)) :
                (pre ⋈* cod) →ʳ
                  (pre ⋈* cod) ⋈*
                    ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ))
              ((ProperTele.inl pre) z))
            (fun i => κ'.act (Tele.ofList υ ⋈ i.arity)
              (σ.act (((τ ⋈ α) ⋈* Tele.ofList υ) ⋈ i.arity)
                (args i)))
          =
          σ.act ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ)
            (.ap
              ((ProperTele.inl
                  (pre ⋈* dom ⋈* (τ ⋈* Tele.ofList ρ)))
                (((ProperTele.inl (pre ⋈* dom)) :
                    (pre ⋈* dom) →ʳ
                      pre ⋈* dom ⋈* (τ ⋈* Tele.ofList ρ))
                  ((ProperTele.inl pre) z)))
              (fun j => κ.act (Tele.ofList υ ⋈ j.arity) (args j)))
        rw [← ProperTele.extendList_inl
          (τ ⋈* Tele.ofList ρ) υ (pre ⋈* dom)
          ((ProperTele.inl pre) z)]
        refine Eq.trans ?_
          (Subst.act_ap_inl_pre σ
            ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ) z
            (fun j => κ.act (Tele.ofList υ ⋈ j.arity) (args j))).symm
        congr 1
        funext j
        change κ'.act (Tele.ofList (j.arity :: υ))
            (σ.act ((τ ⋈ α) ⋈* Tele.ofList (j.arity :: υ)) (args j))
          =
          σ.act ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList (j.arity :: υ))
            (κ.act (Tele.ofList (j.arity :: υ)) (args j))
        exact Subst.act_inst.underListAt σ ρ (j.arity :: υ) ι (args j)
termination_by
  ((⟨⟨dom.toList⟩, ⟨[α]⟩⟩ : InterchangeFuel C),
    (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ))
decreasing_by
  all_goals
    subst_vars
    first
      | refine Prod.Lex.left _ _ (InterchangeFuel.Lt.right ?_)
        exact DomLt.step α (List.Mem.head _) β (ListSlotAt.sub_single xα)
      | refine Prod.Lex.left _ _ (InterchangeFuel.Lt.left ?_)
        obtain ⟨βdom, hmem, hsub⟩ := SlotAt.subWitness z
        exact DomLt.step βdom hmem _ hsub
      | refine Prod.Lex.right _ ?_
        exact Expr.Subterm.of_arg_ofList_cons υ _ «args✝» _
      | refine Prod.Lex.right _ ?_
        exact Expr.Subterm.of_arg_ofList_cons υ _ args _

private theorem Subst.act_inst.preNaturalityLiftAt {C : Carrier}
    {pre τ : Shape C} [ProperTele τ]
    {α β : C.Arity}
    (ρ υ χ : List C.Arity)
    (ι : ∀ {δ : C.Arity}, (⌊α⌋) ∋ δ →
      Expr (pre ⋈* τ ⋈* Tele.ofList ρ ⋈ δ))
    (η : (j : C.Binder β) →
      Expr ((pre ⋈* τ ⋈ α) ⋈* Tele.ofList υ ⋈ j.arity))
    (e : Expr ((pre ⋈ β) ⋈* Tele.ofList χ)) :
    Subst.act_inst.PreLift.sequential ρ υ χ ι η e =
    Subst.act_inst.PreLift.fused ρ υ χ ι η e := by
  let κ : Subst C (pre ⋈* τ) (⌊α⌋) (Tele.ofList ρ) :=
    Subst.inst (⌊α⌋) (fun q => match q with
    | .here i => ι (.here i))
  let lam : Subst C pre (⌊β⌋) ((τ ⋈ α) ⋈* Tele.ofList υ) :=
    Subst.inst (⌊β⌋) (fun q => match q with
    | .here j => η j)
  let lam' : Subst C pre (⌊β⌋)
      ((τ ⋈* Tele.ofList ρ) ⋈* Tele.ofList υ) :=
    Subst.inst (⌊β⌋) (fun q => match q with
    | .here j => κ.act (Tele.ofList υ ⋈ j.arity) (η j))
  change κ.act ((Tele.ofList υ : Shape C) ⋈* Tele.ofList χ)
      (lam.act (Tele.ofList χ) e)
    =
    lam'.act (Tele.ofList χ) e
  match e with
  | .ap (α := γ) head args =>
    have ih_args : ∀ (j : C.Binder γ),
        κ.act ((Tele.ofList υ : Shape C) ⋈*
              Tele.ofList (j.arity :: χ))
            (lam.act (Tele.ofList (j.arity :: χ)) (args j))
          =
          lam'.act (Tele.ofList (j.arity :: χ)) (args j) := by
      intro j
      change κ.act ((Tele.ofList υ : Shape C) ⋈*
            Tele.ofList (j.arity :: χ))
          (lam.act (Tele.ofList (j.arity :: χ)) (args j))
        =
        lam'.act (Tele.ofList (j.arity :: χ)) (args j)
      exact Subst.act_inst.preNaturalityLiftAt ρ υ (j.arity :: χ) ι η
        (args j)
    rcases @ProperTele.cover C (Tele.ofList χ)
        (by exact ProperTele.ofList χ)
        (pre ⋈ β) γ head with
      ⟨xχ, h_xχ⟩ | ⟨below, h_below⟩
    · subst h_xχ
      refine (congrArg
        (κ.act ((Tele.ofList υ : Shape C) ⋈* Tele.ofList χ))
        (Subst.act_ap_inr lam (Tele.ofList χ) xχ args)).trans ?_
      change κ.act ((Tele.ofList υ : Shape C) ⋈* Tele.ofList χ)
          (.ap
            ((ProperTele.inr ((pre ⋈* (τ ⋈ α)) ⋈* Tele.ofList υ)) xχ)
            (fun j => lam.act (Tele.ofList χ ⋈ j.arity) (args j)))
        =
        lam'.act (Tele.ofList χ)
          (.ap ((ProperTele.inr (pre ⋈ β)) xχ) args)
      rw [← ProperTele.extendList_inr_inr
        (Tele.ofList υ : Shape C) χ (pre ⋈* (τ ⋈ α)) xχ]
      refine (Subst.act_ap_inr κ
        ((Tele.ofList υ : Shape C) ⋈* Tele.ofList χ)
        ((ProperTele.inr (Tele.ofList υ : Shape C)) xχ)
        (fun j => lam.act (Tele.ofList χ ⋈ j.arity) (args j))).trans ?_
      change .ap
          ((ProperTele.inr (pre ⋈* (τ ⋈* Tele.ofList ρ)))
            ((ProperTele.inr (Tele.ofList υ : Shape C)) xχ))
          (fun j =>
            κ.act (((Tele.ofList υ : Shape C) ⋈* Tele.ofList χ) ⋈ j.arity)
              (lam.act (Tele.ofList χ ⋈ j.arity) (args j)))
        =
        lam'.act (Tele.ofList χ)
          (.ap ((ProperTele.inr (pre ⋈ β)) xχ) args)
      rw [ProperTele.extendList_inr_inr
        (Tele.ofList υ : Shape C) χ (pre ⋈* (τ ⋈* Tele.ofList ρ)) xχ]
      refine Eq.trans ?_
        (Subst.act_ap_inr lam' (Tele.ofList χ) xχ args).symm
      congr 1
      funext j
      change κ.act ((Tele.ofList υ : Shape C) ⋈*
            Tele.ofList (j.arity :: χ))
          (lam.act (Tele.ofList (j.arity :: χ)) (args j))
        =
        lam'.act (Tele.ofList (j.arity :: χ)) (args j)
      exact ih_args j
    · subst h_below
      rcases ProperTele.cover pre below with ⟨xβ, h_xβ⟩ | ⟨z, h_z⟩
      · subst h_xβ
        cases xβ with
        | here j =>
            refine (congrArg
              (κ.act ((Tele.ofList υ : Shape C) ⋈* Tele.ofList χ))
              (Subst.act_ap_inl_dom lam (Tele.ofList χ)
                (.here j) args)).trans ?_
            let θ : ∀ {δ : C.Arity}, (⌊j.arity⌋) ∋ δ →
                Expr ((pre ⋈* τ) ⋈* (⌊α⌋) ⋈*
                  (Tele.ofList υ : Shape C) ⋈* Tele.ofList χ ⋈ δ) :=
              fun q => match q with
              | .here k => lam.act (Tele.ofList χ ⋈ k.arity) (args k)
            let θ' : ∀ {δ : C.Arity}, (⌊j.arity⌋) ∋ δ →
                Expr ((pre ⋈* τ ⋈* Tele.ofList ρ) ⋈*
                  (Tele.ofList υ : Shape C) ⋈* Tele.ofList χ ⋈ δ) :=
              fun q => match q with
              | .here k => lam'.act (Tele.ofList χ ⋈ k.arity) (args k)
            have hfill : ∀ (k : C.Binder j.arity),
                κ.act (((Tele.ofList υ : Shape C) ⋈* Tele.ofList χ) ⋈ k.arity)
                    (θ (.here k))
                  =
                θ' (.here k) := by
              intro k
              change κ.act ((Tele.ofList υ : Shape C) ⋈*
                    Tele.ofList (k.arity :: χ))
                  (lam.act (Tele.ofList (k.arity :: χ)) (args k))
                =
                lam'.act (Tele.ofList (k.arity :: χ)) (args k)
              exact ih_args k
            have hunder := Subst.act_inst.underListAt
              (pre := pre ⋈* τ) (dom := ⌊α⌋)
              (cod := Tele.ofList ρ) (τ := (Tele.ofList υ : Shape C))
              κ χ [] (ι := θ) (e := η j)
            unfold Subst.act_inst.UnderList.actThenInst
              Subst.act_inst.UnderList.instThenAct
              Subst.act_inst.instOne at hunder
            dsimp only at hunder
            refine Eq.trans hunder.symm ?_
            simp only [hfill, θ, θ']
            exact (Subst.act_ap_inl_dom lam' (Tele.ofList χ)
              (.here j) args).symm
        | there z => nomatch z
      · subst h_z
        refine (congrArg
          (κ.act ((Tele.ofList υ : Shape C) ⋈* Tele.ofList χ))
          (Subst.act_ap_inl_pre lam (Tele.ofList χ) z args)).trans ?_
        unfold Subst.weakenCod
        rw [ProperTele.extendList_inl (τ ⋈ α) υ pre z]
        change κ.act ((Tele.ofList υ : Shape C) ⋈* Tele.ofList χ)
            (.ap
              ((ProperTele.inl ((pre ⋈* (τ ⋈ α)) ⋈* Tele.ofList υ))
                ((ProperTele.inl (pre ⋈* (τ ⋈ α)))
                  ((ProperTele.inl pre) z)))
              (fun i => lam.act (Tele.ofList χ ⋈ i.arity) (args i)))
          =
          lam'.act (Tele.ofList χ)
            (.ap
              ((ProperTele.inl (pre ⋈ β)) ((ProperTele.inl pre) z))
              args)
        rw [← ProperTele.extendList_inl
          (Tele.ofList υ : Shape C) χ (pre ⋈* (τ ⋈ α))
          ((ProperTele.inl pre) z)]
        change κ.act ((Tele.ofList υ : Shape C) ⋈* Tele.ofList χ)
            (.ap
              ((ProperTele.inl ((pre ⋈* τ) ⋈* (⌊α⌋)))
                ((ProperTele.inl (pre ⋈* τ))
                  ((ProperTele.inl pre) z)))
              (fun i => lam.act (Tele.ofList χ ⋈ i.arity) (args i)))
          =
          lam'.act (Tele.ofList χ)
            (.ap
              ((ProperTele.inl (pre ⋈ β)) ((ProperTele.inl pre) z))
              args)
        rw [Subst.act_ap_inl_pre κ
          ((Tele.ofList υ : Shape C) ⋈* Tele.ofList χ)
          ((ProperTele.inl pre) z)]
        refine Eq.trans ?_
          (Subst.act_ap_inl_pre lam' (Tele.ofList χ) z args).symm
        congr 1
        · unfold Subst.weakenCod
          rw [← ProperTele.extendList_inl τ ρ pre z]
          rw [ProperTele.extendList_inl
            (τ ⋈* Tele.ofList ρ) υ pre z]
          change
            ((ProperTele.inl (pre ⋈* (τ ⋈* Tele.ofList ρ))) :
                (pre ⋈* (τ ⋈* Tele.ofList ρ)) →ʳ
                  (pre ⋈* (τ ⋈* Tele.ofList ρ)) ⋈*
                    ((Tele.ofList υ : Shape C) ⋈* Tele.ofList χ))
              ((ProperTele.inl pre) z)
            =
            ((ProperTele.inl ((pre ⋈* (τ ⋈* Tele.ofList ρ)) ⋈*
                Tele.ofList υ)) :
                ((pre ⋈* (τ ⋈* Tele.ofList ρ)) ⋈* Tele.ofList υ) →ʳ
                  ((pre ⋈* (τ ⋈* Tele.ofList ρ)) ⋈* Tele.ofList υ) ⋈*
                    Tele.ofList χ)
              (((ProperTele.inl (pre ⋈* (τ ⋈* Tele.ofList ρ))) :
                  (pre ⋈* (τ ⋈* Tele.ofList ρ)) →ʳ
                    (pre ⋈* (τ ⋈* Tele.ofList ρ)) ⋈*
                      Tele.ofList υ)
                ((ProperTele.inl pre) z))
          rw [← ProperTele.extendList_inl
            (Tele.ofList υ : Shape C) χ
            (pre ⋈* (τ ⋈* Tele.ofList ρ))
            ((ProperTele.inl pre) z)]
        funext k
        change κ.act ((Tele.ofList υ : Shape C) ⋈*
              Tele.ofList (k.arity :: χ))
            (lam.act (Tele.ofList (k.arity :: χ)) (args k))
          =
          lam'.act (Tele.ofList (k.arity :: χ)) (args k)
        exact ih_args k
termination_by
  ((⟨⟨[β]⟩, ⟨[α]⟩⟩ : InterchangeFuel C),
    (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ))
decreasing_by
  all_goals
    subst_vars
    first
      | refine Prod.Lex.left _ _ (InterchangeFuel.Lt.left_swap ?_)
        exact DomLt.step β (List.Mem.head _) j.arity ⟨j, rfl⟩
      | refine Prod.Lex.right _ ?_
        exact Expr.Subterm.of_arg_ofList_cons χ head args _

end

private theorem Subst.act_inst.preNaturalityLift {C : Carrier}
    {pre τ : Shape C} [ProperTele τ]
    {α β : C.Arity}
    (ρ υ : List C.Arity)
    (ι : ∀ {δ : C.Arity}, (⌊α⌋) ∋ δ →
      Expr (pre ⋈* τ ⋈* Tele.ofList ρ ⋈ δ))
    (η : (j : C.Binder β) →
      Expr ((pre ⋈* τ ⋈ α) ⋈* Tele.ofList υ ⋈ j.arity))
    (e : Expr (pre ⋈ β)) :
    Subst.act_inst.PreLift.sequential ρ υ [] ι η e =
    Subst.act_inst.PreLift.fused ρ υ [] ι η e := by
  exact Subst.act_inst.preNaturalityLiftAt
    (pre := pre) (τ := τ) (α := α) (β := β)
    ρ υ [] ι η e

private theorem Subst.act_inst.underList {C : Carrier}
    {pre dom cod τ : Shape C} [ProperTele dom] [ProperTele cod] [ProperTele τ]
    (σ : Subst C pre dom cod)
    {α : C.Arity}
    (ρ : List C.Arity)
    (ι : ∀ {β : C.Arity}, (⌊α⌋) ∋ β →
      Expr (pre ⋈* dom ⋈* τ ⋈* Tele.ofList ρ ⋈ β))
    (e : Expr (pre ⋈* dom ⋈* τ ⋈ α)) :
    Subst.act_inst.UnderList.actThenInst σ ρ [] ι e =
    Subst.act_inst.UnderList.instThenAct σ ρ [] ι e := by
  exact Subst.act_inst.underListAt σ ρ [] ι e

private theorem Subst.act_inst.preNaturalityAt {C : Carrier}
    {pre dom cod : Shape C} [ProperTele dom] [ProperTele cod]
    (σ : Subst C pre dom cod)
    {α : C.Arity}
    (ρ υ : List C.Arity)
    (ι : ∀ {β : C.Arity}, (⌊α⌋) ∋ β →
      Expr (pre ⋈* dom ⋈* Tele.ofList ρ ⋈ β))
    (e : Expr ((pre ⋈ α) ⋈* Tele.ofList υ)) :
    Subst.act_inst.PreNaturality.sequential σ ρ υ ι e =
    Subst.act_inst.PreNaturality.fused σ ρ υ ι e := by
  let κ : Subst C pre (⌊α⌋) (dom ⋈* Tele.ofList ρ) :=
    Subst.inst (⌊α⌋) (fun q => match q with
    | .here i => ι (.here i))
  let κ' : Subst C pre (⌊α⌋) (cod ⋈* Tele.ofList ρ) :=
    Subst.inst (⌊α⌋) (fun q => match q with
    | .here i =>
        σ.act (Tele.ofList ρ ⋈ i.arity) (ι (.here i)))
  change σ.act ((Tele.ofList ρ : Shape C) ⋈* Tele.ofList υ)
      (κ.act (Tele.ofList υ) e)
    =
    κ'.act (Tele.ofList υ) e
  match e with
  | .ap (α := β) head args =>
    rcases @ProperTele.cover C ((⌊α⌋) ⋈* Tele.ofList υ)
        (by exact ProperTele.extendList (⌊α⌋) υ)
        pre β head with
      ⟨top, h_top⟩ | ⟨below, h_below⟩
    · subst h_top
      rcases @ProperTele.cover C (Tele.ofList υ)
          (by exact ProperTele.ofList υ)
          (⌊α⌋) β top with
        ⟨xυ, h_xυ⟩ | ⟨xα, h_xα⟩
      · subst h_xυ
        rw [ProperTele.extendList_inr_inr (⌊α⌋) υ pre xυ]
        refine (congrArg (σ.act ((Tele.ofList ρ : Shape C) ⋈* Tele.ofList υ))
          (Subst.act_ap_inr κ (Tele.ofList υ) xυ args)).trans ?_
        refine Eq.trans ?_ (Subst.act_ap_inr κ' (Tele.ofList υ) xυ args).symm
        change σ.act ((Tele.ofList ρ : Shape C) ⋈* Tele.ofList υ)
            (.ap
              ((ProperTele.inr ((pre ⋈* dom) ⋈* Tele.ofList ρ)) xυ)
              (fun j => κ.act (Tele.ofList υ ⋈ j.arity) (args j)))
          =
          .ap
            ((ProperTele.inr ((pre ⋈* cod) ⋈* Tele.ofList ρ)) xυ)
            (fun j => κ'.act (Tele.ofList υ ⋈ j.arity) (args j))
        rw [← ProperTele.extendList_inr_inr
          (Tele.ofList ρ : Shape C) υ (pre ⋈* dom) xυ]
        rw [Subst.act_ap_inr σ
          ((Tele.ofList ρ : Shape C) ⋈* Tele.ofList υ)
          ((ProperTele.inr (Tele.ofList ρ : Shape C)) xυ)
          (fun j => κ.act (Tele.ofList υ ⋈ j.arity) (args j))]
        rw [ProperTele.extendList_inr_inr
          (Tele.ofList ρ : Shape C) υ (pre ⋈* cod) xυ]
        congr 1
        funext j
        change σ.act ((Tele.ofList ρ : Shape C) ⋈* Tele.ofList (j.arity :: υ))
            (κ.act (Tele.ofList (j.arity :: υ)) (args j))
          =
          κ'.act (Tele.ofList (j.arity :: υ)) (args j)
        exact Subst.act_inst.preNaturalityAt σ ρ (j.arity :: υ) ι (args j)
      · subst h_xα
        rw [ProperTele.extendList_inr_inl
          (⌊α⌋) υ pre xα]
        refine (congrArg
          (σ.act ((Tele.ofList ρ : Shape C) ⋈* Tele.ofList υ))
          (Subst.act_ap_inl_dom κ (Tele.ofList υ)
            xα args)).trans ?_
        refine Eq.trans ?_
          (Subst.act_ap_inl_dom κ' (Tele.ofList υ)
            xα args).symm
        have hsub :
            κ'.sub xα = σ.act (Tele.ofList ρ ⋈ β) (κ.sub xα) := by
          cases xα with
          | here i => rfl
          | there z => nomatch z
        rw [hsub]
        let ιβ : ∀ {δ : C.Arity}, (⌊β⌋) ∋ δ →
            Expr (pre ⋈* dom ⋈* Tele.ofList ρ ⋈* Tele.ofList υ ⋈ δ) :=
          fun q => match q with
          | .here j => κ.act (Tele.ofList υ ⋈ j.arity) (args j)
        have hfill : ∀ (j : C.Binder β),
            σ.act (((Tele.ofList ρ : Shape C) ⋈* Tele.ofList υ) ⋈ j.arity)
                (κ.act (Tele.ofList υ ⋈ j.arity) (args j))
              =
            κ'.act (Tele.ofList υ ⋈ j.arity) (args j) := by
          intro j
          change σ.act
              ((Tele.ofList ρ : Shape C) ⋈* Tele.ofList (j.arity :: υ))
              (κ.act (Tele.ofList (j.arity :: υ)) (args j))
            =
            κ'.act (Tele.ofList (j.arity :: υ)) (args j)
          exact Subst.act_inst.preNaturalityAt σ ρ (j.arity :: υ) ι
            (args j)
        simp only [← hfill]
        exact (Subst.act_inst.underList σ υ
          (τ := (Tele.ofList ρ : Shape C))
          (ι := ιβ)
          (e := κ.sub xα)).symm
    · subst h_below
      rw [ProperTele.extendList_inl (⌊α⌋) υ pre below]
      refine (congrArg
        (σ.act ((Tele.ofList ρ : Shape C) ⋈* Tele.ofList υ))
        (Subst.act_ap_inl_pre κ (Tele.ofList υ)
          below args)).trans ?_
      refine Eq.trans ?_
        (Subst.act_ap_inl_pre κ' (Tele.ofList υ)
          below args).symm
      unfold Subst.weakenCod
      rw [ProperTele.extendList_inl dom ρ pre below]
      change σ.act ((Tele.ofList ρ : Shape C) ⋈* Tele.ofList υ)
          (.ap
            ((ProperTele.inl ((pre ⋈* dom) ⋈* Tele.ofList ρ))
              ((ProperTele.inl (pre ⋈* dom))
                ((ProperTele.inl pre) below)))
            (fun j => κ.act (Tele.ofList υ ⋈ j.arity) (args j)))
        =
        .ap
          ((ProperTele.inl (pre ⋈* (cod ⋈* Tele.ofList ρ)))
            ((ProperTele.inl pre) below))
          (fun j => κ'.act (Tele.ofList υ ⋈ j.arity) (args j))
      rw [← ProperTele.extendList_inl (Tele.ofList ρ : Shape C) υ
        (pre ⋈* dom) ((ProperTele.inl pre) below)]
      refine (Subst.act_ap_inl_pre σ
        ((Tele.ofList ρ : Shape C) ⋈* Tele.ofList υ)
        below
        (fun j => κ.act (Tele.ofList υ ⋈ j.arity) (args j))).trans ?_
      unfold Subst.weakenCod
      rw [ProperTele.extendList_inl cod ρ pre below]
      have hHead :
          ((ProperTele.inl (pre ⋈* cod) :
              (pre ⋈* cod) →ʳ
                (pre ⋈* cod) ⋈* ((Tele.ofList ρ : Shape C) ⋈* Tele.ofList υ))
            ((ProperTele.inl pre) below))
            =
          ((ProperTele.inl (pre ⋈* (cod ⋈* Tele.ofList ρ)) :
              (pre ⋈* (cod ⋈* Tele.ofList ρ)) →ʳ
                (pre ⋈* (cod ⋈* Tele.ofList ρ)) ⋈* Tele.ofList υ)
            ((ProperTele.inl (pre ⋈* cod) :
              (pre ⋈* cod) →ʳ (pre ⋈* cod) ⋈* Tele.ofList ρ)
              ((ProperTele.inl pre) below))) := by
        exact ProperTele.extendList_inl (Tele.ofList ρ : Shape C) υ
          (pre ⋈* cod) ((ProperTele.inl pre) below)
      rw [← hHead]
      congr 1
      funext j
      change σ.act ((Tele.ofList ρ : Shape C) ⋈* Tele.ofList (j.arity :: υ))
          (κ.act (Tele.ofList (j.arity :: υ)) (args j))
        =
        κ'.act (Tele.ofList (j.arity :: υ)) (args j)
      exact Subst.act_inst.preNaturalityAt σ ρ (j.arity :: υ) ι
        (args j)
termination_by (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by
  all_goals
    subst_vars
    try subst β
    subst_vars
    first
      | exact Expr.Subterm.of_arg_ofList_cons υ _ «args✝» _
      | exact Expr.Subterm.of_arg_ofList_cons υ _ args _

private theorem Subst.act_inst.preNaturality {C : Carrier}
    {pre dom cod : Shape C} [ProperTele dom] [ProperTele cod]
    (σ : Subst C pre dom cod)
    {α : C.Arity}
    (ρ : List C.Arity)
    (ι : ∀ {β : C.Arity}, (⌊α⌋) ∋ β →
      Expr (pre ⋈* dom ⋈* Tele.ofList ρ ⋈ β))
    (e : Expr (pre ⋈ α)) :
    Subst.act_inst.PreNaturality.sequential σ ρ [] ι e =
    Subst.act_inst.PreNaturality.fused σ ρ [] ι e := by
  exact Subst.act_inst.preNaturalityAt σ ρ [] ι e

private theorem Subst.act_inst.interchange {C : Carrier}
    {pre dom cod τ : Shape C} [ProperTele dom] [ProperTele cod] [ProperTele τ]
    (σ : Subst C pre dom cod)
    {α : C.Arity}
    (ι : ∀ {β : C.Arity}, (⌊α⌋) ∋ β →
      Expr (pre ⋈* dom ⋈* τ ⋈ β))
    (ρ : List C.Arity)
    (e : Expr (pre ⋈* dom ⋈* (⌊α⌋) ⋈* Tele.ofList ρ)) :
    Subst.act_inst.Interchange.actThenInst σ ι ρ e =
    Subst.act_inst.Interchange.instThenAct σ ι ρ e := by
  unfold Subst.act_inst.Interchange.actThenInst
    Subst.act_inst.Interchange.instThenAct
    Subst.act_inst.instOne
  dsimp only
  let κ : Subst C (pre ⋈* dom) (⌊α⌋) τ :=
    Subst.inst (⌊α⌋) (fun q => match q with
      | .here i => ι (.here i))
  let κ' : Subst C (pre ⋈* cod) (⌊α⌋) τ :=
    Subst.inst (⌊α⌋) (fun q => match q with
      | .here i => σ.act (τ ⋈ i.arity) (ι (.here i)))
  change κ'.act (Tele.ofList ρ)
      (σ.act ((⌊α⌋) ⋈* Tele.ofList ρ) e)
    =
    σ.act (τ ⋈* Tele.ofList ρ)
      (κ.act (Tele.ofList ρ) e)
  match e with
  | .ap (α := β) head args =>
    rcases @ProperTele.cover C ((⌊α⌋) ⋈* Tele.ofList ρ)
        (by exact ProperTele.extendList (⌊α⌋) ρ)
        (pre ⋈* dom) β head with
      ⟨top, h_top⟩ | ⟨below, h_below⟩
    · subst h_top
      rcases @ProperTele.cover C (Tele.ofList ρ)
          (by exact ProperTele.ofList ρ)
          (⌊α⌋) β top with
        ⟨xρ, h_xρ⟩ | ⟨xα, h_xα⟩
      · subst h_xρ
        refine (congrArg (κ'.act (Tele.ofList ρ))
          (@Subst.act_ap_inr C pre dom cod inferInstance inferInstance
            σ ((⌊α⌋) ⋈* Tele.ofList ρ)
            (ProperTele.extendList (⌊α⌋) ρ)
            β ((ProperTele.inr (⌊α⌋)) xρ) args)).trans ?_
        rw [ProperTele.extendList_inr_inr (⌊α⌋) ρ (pre ⋈* dom) xρ]
        rw [ProperTele.extendList_inr_inr (⌊α⌋) ρ (pre ⋈* cod) xρ]
        refine (Subst.act_ap_inr κ' (Tele.ofList ρ) xρ
          (fun j => σ.act (((⌊α⌋) ⋈* Tele.ofList ρ) ⋈ j.arity) (args j))).trans ?_
        rw [Subst.act_ap_inr κ (Tele.ofList ρ) xρ args]
        rw [← ProperTele.extendList_inr_inr τ ρ (pre ⋈* dom) xρ]
        refine Eq.trans ?_ (Subst.act_ap_inr σ (τ ⋈* Tele.ofList ρ)
          ((ProperTele.inr τ) xρ)
          (fun j => κ.act (Tele.ofList ρ ⋈ j.arity) (args j))).symm
        rw [ProperTele.extendList_inr_inr τ ρ (pre ⋈* cod) xρ]
        congr 1
        funext j
        change κ'.act (Tele.ofList (j.arity :: ρ))
            (σ.act ((⌊α⌋) ⋈* Tele.ofList (j.arity :: ρ)) (args j))
          =
          σ.act (τ ⋈* Tele.ofList (j.arity :: ρ))
            (κ.act (Tele.ofList (j.arity :: ρ)) (args j))
        exact Subst.act_inst.interchange σ ι (j.arity :: ρ) (args j)
      · subst h_xα
        have hfillTop : ∀ (j : C.Binder β),
            κ'.act (Tele.ofList ρ ⋈ j.arity)
                (σ.act (((⌊α⌋) ⋈* Tele.ofList ρ) ⋈ j.arity)
                  (args j))
              =
            σ.act ((τ ⋈* Tele.ofList ρ) ⋈ j.arity)
                (κ.act (Tele.ofList ρ ⋈ j.arity) (args j)) := by
          intro j
          change κ'.act (Tele.ofList (j.arity :: ρ))
              (σ.act ((⌊α⌋) ⋈* Tele.ofList (j.arity :: ρ))
                (args j))
            =
            σ.act (τ ⋈* Tele.ofList (j.arity :: ρ))
              (κ.act (Tele.ofList (j.arity :: ρ)) (args j))
          exact Subst.act_inst.interchange σ ι (j.arity :: ρ) (args j)
        cases xα with
        | here i =>
            refine (congrArg (κ'.act (Tele.ofList ρ))
              (@Subst.act_ap_inr C pre dom cod inferInstance inferInstance
                σ ((⌊α⌋) ⋈* Tele.ofList ρ)
                (ProperTele.extendList (⌊α⌋) ρ)
                i.arity ((ProperTele.inl (⌊α⌋))
                  (.here i)) args)).trans ?_
            rw [ProperTele.extendList_inr_inl
              (⌊α⌋) ρ (pre ⋈* cod) (.here i)]
            refine (Subst.act_ap_inl_dom κ' (Tele.ofList ρ)
              (.here i)
              (fun j => σ.act (((⌊α⌋) ⋈* Tele.ofList ρ) ⋈ j.arity)
                (args j))).trans ?_
            rw [ProperTele.extendList_inr_inl
              (⌊α⌋) ρ (pre ⋈* dom) (.here i)]
            rw [Subst.act_ap_inl_dom κ (Tele.ofList ρ)
              (.here i) args]
            rw [show κ'.sub (.here i)
                  = σ.act (τ ⋈ i.arity) (ι (.here i)) from rfl]
            rw [show κ.sub (.here i)
                  = ι (.here i) from rfl]
            let ιβ : ∀ {δ : C.Arity}, (⌊i.arity⌋) ∋ δ →
                Expr (pre ⋈* dom ⋈* τ ⋈* Tele.ofList ρ ⋈ δ) :=
              fun q => match q with
              | .here j => κ.act (Tele.ofList ρ ⋈ j.arity) (args j)
            have hfill : ∀ (j : C.Binder i.arity),
                κ'.act (Tele.ofList ρ ⋈ j.arity)
                    (σ.act (((⌊α⌋) ⋈* Tele.ofList ρ) ⋈ j.arity)
                      (args j))
                  =
                σ.act ((τ ⋈* Tele.ofList ρ) ⋈ j.arity)
                    (ιβ (.here j)) := by
              intro j
              exact hfillTop j
            simp only [hfill]
            exact Subst.act_inst.underList σ ρ
              (ι := ιβ)
              (e := ι (.here i))
        | there z => nomatch z
    · subst h_below
      rcases ProperTele.cover pre below with ⟨z, h_z⟩ | ⟨z, h_z⟩
      · subst h_z
        refine (congrArg (κ'.act (Tele.ofList ρ))
          (Subst.act_ap_inl_dom σ
            ((⌊α⌋) ⋈* Tele.ofList ρ) z args)).trans ?_
        let ιβ : ∀ {δ : C.Arity}, (⌊β⌋) ∋ δ →
            Expr (pre ⋈* cod ⋈* (⌊α⌋) ⋈* Tele.ofList ρ ⋈ δ) :=
          fun q => match q with
          | .here j =>
              σ.act (((⌊α⌋) ⋈* Tele.ofList ρ) ⋈ j.arity) (args j)
        have hpre := Subst.act_inst.preNaturality κ' ρ
          (ι := ιβ) (e := σ z)
        unfold Subst.act_inst.PreNaturality.sequential
          Subst.act_inst.PreNaturality.fused
          Subst.act_inst.instOne at hpre
        dsimp only at hpre
        refine hpre.trans ?_
        have hfill : ∀ (j : C.Binder β),
            κ'.act (Tele.ofList ρ ⋈ j.arity)
                (ιβ (.here j))
              =
            σ.act ((τ ⋈* Tele.ofList ρ) ⋈ j.arity)
                (κ.act (Tele.ofList ρ ⋈ j.arity) (args j)) := by
          intro j
          change κ'.act (Tele.ofList (j.arity :: ρ))
              (σ.act ((⌊α⌋) ⋈* Tele.ofList (j.arity :: ρ))
                (args j))
            =
            σ.act (τ ⋈* Tele.ofList (j.arity :: ρ))
              (κ.act (Tele.ofList (j.arity :: ρ)) (args j))
          exact Subst.act_inst.interchange σ ι (j.arity :: ρ) (args j)
        simp only [hfill]
        rw [ProperTele.extendList_inl
          (⌊α⌋) ρ (pre ⋈* dom) ((ProperTele.inr pre) z)]
        rw [Subst.act_ap_inl_pre κ (Tele.ofList ρ)
          ((ProperTele.inr pre) z) args]
        unfold Subst.weakenCod
        rw [← ProperTele.extendList_inl τ ρ (pre ⋈* dom)
          ((ProperTele.inr pre) z)]
        exact (Subst.act_ap_inl_dom σ (τ ⋈* Tele.ofList ρ) z
          (fun j => κ.act (Tele.ofList ρ ⋈ j.arity) (args j))).symm
      · subst h_z
        refine (congrArg (κ'.act (Tele.ofList ρ))
          (Subst.act_ap_inl_pre σ
            ((⌊α⌋) ⋈* Tele.ofList ρ) z args)).trans ?_
        rw [ProperTele.extendList_inl
          (⌊α⌋) ρ (pre ⋈* cod) ((Subst.weakenCod σ) z)]
        refine (Subst.act_ap_inl_pre κ' (Tele.ofList ρ)
          ((Subst.weakenCod σ) z)
          (fun j => σ.act (((⌊α⌋) ⋈* Tele.ofList ρ) ⋈ j.arity)
            (args j))).trans ?_
        rw [ProperTele.extendList_inl
          (⌊α⌋) ρ (pre ⋈* dom) ((ProperTele.inl pre) z)]
        rw [Subst.act_ap_inl_pre κ (Tele.ofList ρ)
          ((ProperTele.inl pre) z) args]
        unfold Subst.weakenCod
        rw [← ProperTele.extendList_inl τ ρ (pre ⋈* dom)
          ((ProperTele.inl pre) z)]
        refine Eq.trans ?_ (Subst.act_ap_inl_pre σ (τ ⋈* Tele.ofList ρ) z
          (fun j => κ.act (Tele.ofList ρ ⋈ j.arity) (args j))).symm
        unfold Subst.weakenCod
        rw [← ProperTele.extendList_inl τ ρ (pre ⋈* cod)
          ((ProperTele.inl pre) z)]
        congr 1
        funext j
        change κ'.act (Tele.ofList (j.arity :: ρ))
            (σ.act ((⌊α⌋) ⋈* Tele.ofList (j.arity :: ρ)) (args j))
          =
          σ.act (τ ⋈* Tele.ofList (j.arity :: ρ))
            (κ.act (Tele.ofList (j.arity :: ρ)) (args j))
        exact Subst.act_inst.interchange σ ι (j.arity :: ρ) (args j)
termination_by (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by
  all_goals
    subst_vars
    first
      | exact (Expr.Subterm.of_arg_ofList_cons ρ head args _)
      | exact (Expr.Subterm.of_arg_ofList_cons ρ _ «args✝» _)
      | exact (Expr.Subterm.of_arg_ofList_cons ρ _ args _)

private theorem Subst.act_inst.fusion {C : Carrier} {Δ Ε τ : Shape C}
    [ProperTele Δ] [ProperTele Ε] [ProperTele τ]
    (g : ∀ {β : C.Arity}, Δ ∋ β → Expr (Ε ⋈ β))
    {α : C.Arity}
    (ι : ∀ {β : C.Arity}, (⌊α⌋) ∋ β →
      Expr (Δ ⋈* τ ⋈ β))
    (e : Expr (Δ ⋈ α)) :
    Subst.act_inst.Interchange.actThenInst (τ := τ) (toSubst g) ι [] e =
    Subst.act_inst.Interchange.instThenAct (τ := τ) (toSubst g) ι [] e := by
  exact Subst.act_inst.interchange (toSubst g) ι [] e


/-- **`act_kcomp`** — acting via a Kleisli composition factors.
Translates to `lift (g ∘ f) = lift g ∘ lift f` (comp_lift).  Generalised over
the depth `τ` so the recursive call on each arg fits the same statement. -/
theorem Subst.act_kcomp {C : Carrier} {Γ Δ Ξ : Shape C}
    [ProperTele Γ] [ProperTele Δ] [ProperTele Ξ]
    (f : ∀ {β : C.Arity}, Γ ∋ β → Expr (Δ ⋈ β))
    (g : ∀ {β : C.Arity}, Δ ∋ β → Expr (Ξ ⋈ β))
    (τ : Shape C) [ProperTele τ]
    (e : Expr (Γ ⋈* τ)) :
    (toSubst (Subst.kcomp f g)).act τ e
      = (toSubst g).act τ ((toSubst f).act τ e) := by
  match e with
  | .ap (α := β) head args =>
    rcases ProperTele.cover Γ head with
      ⟨x, h_x⟩ | ⟨y, h_y⟩
    · subst h_x
      refine (Subst.act_ap_inr (toSubst (Subst.kcomp f g)) τ x args).trans ?_
      change
        .ap ((ProperTele.inr (Shape.nil ⋈* Ξ)) x)
          (fun j => (toSubst (Subst.kcomp f g)).act (τ ⋈ j.arity) (args j))
        =
        (toSubst g).act τ
          ((toSubst f).act τ
            (.ap ((ProperTele.inr (Shape.nil ⋈* Γ)) x) args))
      rw [Subst.act_ap_inr (toSubst f) τ x args]
      rw [Subst.act_ap_inr (toSubst g) τ x
        (fun i => (toSubst f).act (τ ⋈ i.arity) (args i))]
      congr 1
      funext i
      exact Subst.act_kcomp f g (τ ⋈ i.arity) (args i)
    · subst h_y
      rw [← ProperTele.inr_nil_id y]
      refine (Subst.act_ap_inl_dom
        (toSubst (Subst.kcomp f g)) τ y args).trans ?_
      have ih_args : ∀ (i : C.Binder β),
          (toSubst (Subst.kcomp f g)).act (τ ⋈ i.arity) (args i)
            =
          (toSubst g).act (τ ⋈ i.arity)
            ((toSubst f).act (τ ⋈ i.arity) (args i)) :=
        fun i => Subst.act_kcomp f g (τ ⋈ i.arity) (args i)
      rw [show (toSubst (Subst.kcomp f g)).sub y
            = (toSubst g).act (⌊β⌋) (f y) from rfl]
      simp only [ih_args]
      change
        ⟦Subst.inst (⌊β⌋)
          (fun {δ} (q : (⌊β⌋) ∋ δ) => match q with
          | .here i =>
            (toSubst g).act (τ ⋈ i.arity)
              ((toSubst f).act (τ ⋈ i.arity) (args i)))⟧ˢ
          ((toSubst g).act (⌊β⌋) (f y))
        =
        (toSubst g).act τ
          ((toSubst f).act τ
            (.ap
              ((ProperTele.inl (Shape.nil ⋈* Γ))
                ((ProperTele.inr Shape.nil) y)) args))
      rw [Subst.act_ap_inl_dom (toSubst f) τ y args]
      exact Subst.act_inst.fusion g
        (τ := τ)
        (ι := fun {δ} (q : (⌊β⌋) ∋ δ) => match q with
          | .here i => (toSubst f).act (τ ⋈ i.arity) (args i))
        (e := f y)
termination_by (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg head args _
