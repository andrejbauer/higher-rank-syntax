import HigherRankSyntaxTele.Subst

/-!
# Equations of the substitution action

Auxiliary equations for the three relative-monad laws, built from
**computation lemmas**: each takes `Subst.act` on an `Expr.apply` with a
specific head (τ-side, dom-side, pre-side) and reduces the classify
dispatch to a clean right-hand side.  The reflection lemmas
`ProperTele.classify_inr` / `classify_inl` are the rewriting handles.

## The three monad laws

* `Subst.act_id` — `(Subst.id Γ).act τ e = e` (unit_right).
* `Subst.act_η` — `(toSubst f).act (Shape.nil ⋈ α) (Expr.η p) = f p` (unit_left).
* `Subst.act_kcomp` — Kleisli composition factors (comp_lift).
-/


/-! ## Computation lemmas — `Subst.act` on a specific apply head -/

/-- Computing `σ.act` on an apply whose head is right-injected into the
τ-side: collapses to the S-side reconstruction. -/
theorem Subst.act_apply_inr {C : Carrier} {pre dom cod : Shape C}
    [ProperTele dom] [ProperTele cod]
    (σ : Subst C pre dom cod) (τ : Shape C) [ProperTele τ]
    {α : C.Arity} (x : τ ∋ α)
    (args : (i : C.Binder α) →
      Expr (pre ⋈* dom ⋈* τ ⋈ i.arity)) :
    σ.act τ (Expr.apply ((ProperTele.inr (pre ⋈* dom)).apply x) args)
      = Expr.apply ((ProperTele.inr (pre ⋈* cod)).apply x)
          (fun j => σ.act (τ ⋈ j.arity) (args j)) := by
  have h := @Subst.act.eq_1 C pre dom cod inferInstance inferInstance σ τ inferInstance α
              ((ProperTele.inr (pre ⋈* dom)).apply x) args
  rw [ProperTele.classify_inr (pre ⋈* dom)] at h
  exact h

/-- Computing `σ.act` on an apply whose head is left-injected below τ and
classified to the dom side: fires the dom-branch instantiation. -/
theorem Subst.act_apply_inl_dom {C : Carrier} {pre dom cod : Shape C}
    [ProperTele dom] [ProperTele cod]
    (σ : Subst C pre dom cod) (τ : Shape C) [ProperTele τ]
    {α : C.Arity} (y : dom ∋ α)
    (args : (i : C.Binder α) →
      Expr (pre ⋈* dom ⋈* τ ⋈ i.arity)) :
    σ.act τ (Expr.apply
              ((ProperTele.inl (pre ⋈* dom)).apply
                ((ProperTele.inr pre).apply y)) args)
      = (Subst.inst (Shape.nil ⋈ α) (fun q => match q with
            | .here i => σ.act (τ ⋈ i.arity) (args i))).act Shape.nil (σ y) := by
  have h := @Subst.act.eq_1 C pre dom cod inferInstance inferInstance σ τ inferInstance α
              ((ProperTele.inl (pre ⋈* dom)).apply
                ((ProperTele.inr pre).apply y)) args
  rw [ProperTele.classify_inl (pre ⋈* dom)] at h
  unfold Subst.classifyDom at h
  rw [ProperTele.classify_inr pre] at h
  exact h

/-- Computing `σ.act` on an apply whose head is left-injected below τ and
classified to the pre side: rebuilds the head in the pre branch. -/
theorem Subst.act_apply_inl_pre {C : Carrier} {pre dom cod : Shape C}
    [ProperTele dom] [ProperTele cod]
    (σ : Subst C pre dom cod) (τ : Shape C) [ProperTele τ]
    {α : C.Arity} (z : pre ∋ α)
    (args : (i : C.Binder α) →
      Expr (pre ⋈* dom ⋈* τ ⋈ i.arity)) :
    σ.act τ (Expr.apply
              ((ProperTele.inl (pre ⋈* dom)).apply
                ((ProperTele.inl pre).apply z)) args)
      = Expr.apply
          ((ProperTele.inl (pre ⋈* cod)).apply
            ((Subst.weakenCod σ).apply z))
          (fun i => σ.act (τ ⋈ i.arity) (args i)) := by
  have h := @Subst.act.eq_1 C pre dom cod inferInstance inferInstance σ τ inferInstance α
              ((ProperTele.inl (pre ⋈* dom)).apply
                ((ProperTele.inl pre).apply z)) args
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
        (Expr.η ((ProperTele.inr (pre ⋈* dom)).apply x))
      = Expr.η ((ProperTele.inr (pre ⋈* cod)).apply x) := by
  rw [Expr.η.eq_1]
  -- `.there ((inr τ).apply x) = (inr (τ ⋈ α)).apply (.there x)` holds
  -- definitionally (instCons.inr); `change` accepts the defeq.
  change σ.act (τ ⋈ α)
      (Expr.apply ((ProperTele.inr (pre ⋈* dom)).apply
                     (ListSlotAt.there x))
                  (fun i => Expr.η (ListSlotAt.here i))) = _
  rw [Subst.act_apply_inr σ (τ ⋈ α) (ListSlotAt.there x)]
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
      (ι : ∀ {β : C.Arity}, (Shape.nil ⋈ i.arity) ∋ β → Expr (pre ⋈* cod ⋈ β))
      (p : pre ∋ i.arity),
      (Subst.inst (Shape.nil ⋈ i.arity) ι).act Shape.nil (Expr.η p)
        = Expr.apply ((ProperTele.inl pre).apply p) (fun j => ι (ListSlotAt.here j))) :
    ∀ (τ : Shape C) [ProperTele τ] (e : Expr ((Δ ⋈ α) ⋈* τ)),
      (Subst.instId Δ α).act τ e = e
  | τ, _, Expr.apply (α := β) head argFam => by
      have ih_all : ∀ (k : C.Binder β),
          (Subst.instId Δ α).act (τ ⋈ k.arity) (argFam k) = argFam k :=
        fun k => Subst.act_inst.idOf α Δ hη (τ ⋈ k.arity) (argFam k)
      rcases ProperTele.cover (Δ ⋈ α) head with ⟨y, h_y⟩ | ⟨y, h_y⟩
      · subst h_y
        refine (Subst.act_apply_inr (Subst.instId Δ α) τ y argFam).trans ?_
        congr
        funext k
        exact ih_all k
      · subst h_y
        rcases ProperTele.cover Δ y with ⟨z, h_z⟩ | ⟨z, h_z⟩
        · subst h_z
          cases z with
          | here i =>
              refine (Subst.act_apply_inl_dom
                (Subst.instId Δ α) τ (ListSlotAt.here i) argFam).trans ?_
              rw [show (Subst.instId Δ α).sub (ListSlotAt.here i)
                    = @Expr.η C (Δ ⋈ α) i.arity (ListSlotAt.here i) from rfl]
              refine (hη i (pre := Δ ⋈ α) (cod := τ)
                (ι := _) (p := ListSlotAt.here i)).trans ?_
              change
                Expr.apply ((ProperTele.inl (Δ ⋈ α)).apply
                    (ListSlotAt.here i))
                  (fun k => (Subst.instId Δ α).act (τ ⋈ k.arity) (argFam k))
                =
                Expr.apply ((ProperTele.inl (Δ ⋈ α)).apply
                    (ListSlotAt.here i)) argFam
              congr 1
              funext k
              exact ih_all k
          | there z' => nomatch z'
        · subst h_z
          refine (Subst.act_apply_inl_pre (Subst.instId Δ α) τ z argFam).trans ?_
          change
            Expr.apply ((ProperTele.inl (Δ ⋈ α)).apply
                ((ProperTele.inl Δ).apply z))
              (fun k => (Subst.instId Δ α).act (τ ⋈ k.arity) (argFam k))
            =
            Expr.apply ((ProperTele.inl (Δ ⋈ α)).apply
                ((ProperTele.inl Δ).apply z)) argFam
          congr 1
          funext k
          exact ih_all k
termination_by τ _ e => (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg head argFam _

/-- The β-for-η property and the identity-instantiation property, proved
together by well-founded recursion on arities; projected as `act_inst.η`
and `act_inst.id`. -/
private theorem Subst.act_inst {C : Carrier} (α : C.Arity) :
    (∀ {pre cod : Shape C} [ProperTele cod]
      (ι : ∀ {β : C.Arity}, (Shape.nil ⋈ α) ∋ β → Expr (pre ⋈* cod ⋈ β))
      (p : pre ∋ α),
      (Subst.inst (Shape.nil ⋈ α) ι).act Shape.nil (Expr.η p)
        = Expr.apply ((ProperTele.inl pre).apply p) (fun i => ι (ListSlotAt.here i)))
    ∧ (∀ (Δ τ : Shape C) [ProperTele τ] (e : Expr ((Δ ⋈ α) ⋈* τ)),
      (Subst.instId Δ α).act τ e = e) := by
  refine ⟨?eta_pre, ?inst_id⟩
  · intro pre cod _ ι p
    rw [Expr.η.eq_1]
    change (Subst.inst (Shape.nil ⋈ α) ι).act Shape.nil
        (Expr.apply ((ProperTele.inl (pre ⋈* (Shape.nil ⋈ α))).apply
          ((ProperTele.inl pre).apply p)) (fun i => Expr.η (ListSlotAt.here i))) = _
    rw [Subst.act_apply_inl_pre]
    change
      Expr.apply ((Subst.inst (Shape.nil ⋈ α) ι).weakenCod.apply p)
        (fun i => (Subst.inst (Shape.nil ⋈ α) ι).act
          (Shape.nil ⋈ i.arity) (Expr.η (ListSlotAt.here i)))
      =
      Expr.apply ((ProperTele.inl pre).apply p)
        (fun i => ι (ListSlotAt.here i))
    change
      Expr.apply ((ProperTele.inl pre).apply p)
        (fun i => (Subst.inst (Shape.nil ⋈ α) ι).act
          (Shape.nil ⋈ i.arity) (Expr.η (ListSlotAt.here i)))
      =
      Expr.apply ((ProperTele.inl pre).apply p)
        (fun i => ι (ListSlotAt.here i))
    congr
    funext i
    rw [Expr.η.eq_1]
    change (Subst.inst (Shape.nil ⋈ α) ι).act (Shape.nil ⋈ i.arity)
        (Expr.apply ((ProperTele.inl (pre ⋈* (Shape.nil ⋈ α))).apply
          ((ProperTele.inr pre).apply (ListSlotAt.here i)))
          (fun k =>
            @Expr.η C
              ((pre ⋈* (Shape.nil ⋈ α)) ⋈* (Shape.nil ⋈ i.arity))
              k.arity (ListSlotAt.here k))) = _
    rw [Subst.act_apply_inl_dom]
    rw [show (Subst.inst (Shape.nil ⋈ α) ι).sub (ListSlotAt.here i)
          = ι (ListSlotAt.here i) from rfl]
    have hfill : ∀ (k : C.Binder i.arity),
        (Subst.inst (Shape.nil ⋈ α) ι).act
          ((Shape.nil ⋈ i.arity) ⋈ k.arity)
            (@Expr.η C
              ((pre ⋈* (Shape.nil ⋈ α)) ⋈* (Shape.nil ⋈ i.arity))
              k.arity (ListSlotAt.here k))
        =
          @Expr.η C
            ((pre ⋈* cod) ⋈* (Shape.nil ⋈ i.arity))
            k.arity (ListSlotAt.here k) := by
      intro k
      exact Subst.act_η_inr (Subst.inst (Shape.nil ⋈ α) ι)
        (Shape.nil ⋈ i.arity) (x := ListSlotAt.here k)
    simp only [hfill]
    change (Subst.instId (pre ⋈* cod) i.arity).act Shape.nil
      (ι (ListSlotAt.here i)) = ι (ListSlotAt.here i)
    exact (Subst.act_inst i.arity).2 (pre ⋈* cod) Shape.nil
      (ι (ListSlotAt.here i))
  · intro Δ τ _ e
    exact Subst.act_inst.idOf α Δ
      (fun i => (Subst.act_inst i.arity).1) τ e
termination_by α
decreasing_by
  all_goals exact ⟨i, rfl⟩

/-- β-for-η for a one-binder instantiation: instantiating the η-expansion
of a pre-slot exposes the kit. -/
theorem Subst.act_inst.η {C : Carrier} {pre cod : Shape C} [ProperTele cod]
    {α : C.Arity}
    (ι : ∀ {β : C.Arity}, (Shape.nil ⋈ α) ∋ β →
      Expr (pre ⋈* cod ⋈ β))
    (p : pre ∋ α) :
    (Subst.inst (Shape.nil ⋈ α) ι).act Shape.nil (Expr.η p)
      =
    Expr.apply ((ProperTele.inl pre).apply p)
      (fun i => ι (ListSlotAt.here i)) :=
  (Subst.act_inst α).1 ι p

/-- Identity instantiation acts as the identity. -/
theorem Subst.act_inst.id {C : Carrier} (α : C.Arity) (Δ : Shape C) :
    ∀ (τ : Shape C) [ProperTele τ] (e : Expr ((Δ ⋈ α) ⋈* τ)),
      (Subst.instId Δ α).act τ e = e :=
  (Subst.act_inst α).2 Δ

/-! ## Monad laws -/

/-- **`act_id`** — the identity substitution acts as the identity.
Translates to `lift η = 𝟙` (unit_right).  Generalised over τ so the
recursive call on each arg fits the same statement. -/
theorem Subst.act_id {C : Carrier} (Γ : Shape C) [ProperTele Γ]
    (τ : Shape C) [ProperTele τ]
    (e : Expr (Γ ⋈* τ)) :
    (Subst.id Γ).act τ e = e := by
  match e with
  | Expr.apply (α := β) x args =>
    rcases ProperTele.cover Γ x with
      ⟨y, h_y⟩ | ⟨y, h_y⟩
    · -- head = embed x; the τ-embed branch fires
      subst h_y
      refine (Subst.act_apply_inr (Subst.id Γ) τ y args).trans ?_
      congr ; funext k ; apply Subst.act_id
    · -- head = weaken y; y : Γ ∋ β.  Cover y at base Shape.nil:
      -- weaken-from-nil is empty, so y is necessarily embed-image.
      subst h_y
      rcases ProperTele.cover Shape.nil y with ⟨y, h_q⟩ | ⟨z, _⟩
      · subst h_q
        refine (Subst.act_apply_inl_dom (Subst.id Γ) τ y args).trans ?_
        -- Simplify (Subst.id Γ) y = Expr.η y (rfl via toSubst_sub).
        show (Subst.inst (Shape.nil ⋈ β) (fun q => match q with
              | .here k => (Subst.id Γ).act (τ ⋈ k.arity) (args k))).act Shape.nil
              (Expr.η y) = _
        -- IH on each argument:
        have h_args : ∀ (k : C.Binder β),
            (Subst.id Γ).act (τ ⋈ k.arity) (args k) = args k :=
          fun k => Subst.act_id Γ (τ ⋈ k.arity) (args k)
        -- Simplify (embed Shape.nil).apply y = y on the RHS.
        rw [ProperTele.inr_nil_id y]
        refine (Subst.act_inst.η
          (pre := Γ) (cod := τ) (α := β) (ι := _) (p := y)).trans ?_
        change
          Expr.apply ((ProperTele.inl Γ).apply y)
            (fun k => (Subst.id Γ).act (τ ⋈ k.arity) (args k))
          =
          Expr.apply ((ProperTele.inl Γ).apply y) args
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
    (toSubst f).act (Shape.nil ⋈ α) (Expr.η p) = f p := by
  rw [Expr.η.eq_1]
  -- `.there p = (weaken_{Shape.nil ⋈ α} _).apply p` by instCons.weaken (rfl).
  -- Cover p at base Shape.nil: p must be embed-image (weaken-from-nil empty).
  rcases ProperTele.cover Shape.nil p with ⟨y, h_q⟩ | ⟨z, _⟩
  · subst h_q
    show (toSubst f).act (Shape.nil ⋈ α)
        (Expr.apply ((ProperTele.inl (Shape.nil ⋈* Γ)).apply
                      ((ProperTele.inr Shape.nil).apply y))
                    (fun i => Expr.η (ListSlotAt.here i))) = _
    rw [Subst.act_apply_inl_dom (toSubst f) (Shape.nil ⋈ α) y]
    have hfill : ∀ (i : C.Binder α),
        (toSubst f).act ((Shape.nil ⋈ α) ⋈ i.arity)
          (@Expr.η C
            ((Shape.nil ⋈* Γ) ⋈* (Shape.nil ⋈ α))
            i.arity (ListSlotAt.here i))
        =
        @Expr.η C
          ((Shape.nil ⋈* Δ) ⋈* (Shape.nil ⋈ α))
          i.arity (ListSlotAt.here i) := by
      intro i
      exact Subst.act_η_inr (toSubst f) (Shape.nil ⋈ α)
        (x := ListSlotAt.here i)
    simp only [hfill]
    rw [toSubst_sub]
    rw [ProperTele.inr_nil_id y]
    change (Subst.instId Δ α).act Shape.nil (f y) = f y
    exact Subst.act_inst.id α Δ Shape.nil (f y)
  · exact nomatch z

/-- **`act_kcomp`** — acting via a Kleisli composition factors.
Translates to `lift (g ∘ f) = lift g ∘ lift f` (comp_lift). -/
theorem Subst.act_kcomp {C : Carrier} {Γ Δ Ξ : Shape C}
    [ProperTele Γ] [ProperTele Δ] [ProperTele Ξ]
    (f : ∀ {β : C.Arity}, Γ ∋ β → Expr (Δ ⋈ β))
    (g : ∀ {β : C.Arity}, Δ ∋ β → Expr (Ξ ⋈ β))
    (α : C.Arity) (e : Expr (Γ ⋈ α)) :
    (toSubst (Subst.kcomp f g)).act (Shape.nil ⋈ α) e
      = (toSubst g).act (Shape.nil ⋈ α)
          ((toSubst f).act (Shape.nil ⋈ α) e) := by
  match e with
  | Expr.apply (α := β) head args =>
    sorry
