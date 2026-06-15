import HigherRankSyntax.Subst

/-!
# Equations of the substitution action

Auxiliary equations for the three relative-monad laws, built from
**computation lemmas**: each takes `Subst.act` on an `Expr.ap` with a
specific head (τ-side, dom-side, pre-side) and reduces the classify
dispatch to a clean right-hand side.  The reflection lemmas
`Proper.classify_inr` / `classify_inl` are the rewriting handles.

## The three monad laws

* `Subst.act_id` — `(Subst.id Γ).act τ e = e` (unit_right).
* `Subst.act_η` — `(toSubst f).act ⌊α⌋ (Expr.η p) = f p` (unit_left).
* `Subst.act_kcomp` — Kleisli composition factors (comp_lift).
-/


/-! ## Computation lemmas — `Subst.act` on a specific apply head -/

/-- Computing `σ.act` on an apply whose head is right-injected into the
τ-side: collapses to the S-side reconstruction. -/
theorem Subst.act_ap_inr
    {C : Carrier} {pre dom cod : Shape C}
    [Proper dom] [Proper cod]
    (σ : Subst C pre dom cod) (τ : Shape C) [Proper τ]
    {α} (x : τ ∋ α)
    (args : (i : C.Binder α) → Expr (pre ⧺ dom ⧺ τ ∷ i.arity)) :
  σ.act τ (.ap (ι₂ x) args)
    = .ap (ι₂ x) (fun j => σ.act (τ ∷ j.arity) (args j))
  := by
  conv => lhs; unfold Subst.act
  rw [Subst.classifySite_inr]

/-- Computing `σ.act` on an apply whose head is left-injected below τ and
classified to the dom side: fires the dom-branch instantiation. -/
theorem Subst.act_ap_inl_dom
    {C : Carrier} {pre dom cod : Shape C}
    [Proper dom] [Proper cod]
    (σ : Subst C pre dom cod) (τ : Shape C) [Proper τ]
    {α} (y : dom ∋ α)
    (args : (i : C.Binder α) → Expr (pre ⧺ dom ⧺ τ ∷ i.arity)) :
  σ.act τ (.ap ((Proper.inl (pre ⧺ dom)) ((Proper.inr pre) y)) args)
    = ⟦ Subst.inst ⌊α⌋ (fun q => match q with | .here i => σ.act (τ ∷ i.arity) (args i)) ⟧ˢ (σ y)
  := by
  conv => lhs; unfold Subst.act
  rw [Subst.classifySite_inl_dom]
  rfl

/-- Computing `σ.act` on an apply whose head is left-injected below τ and
classified to the pre side: rebuilds the head in the pre branch. -/
theorem Subst.act_ap_inl_pre
    {C : Carrier} {pre dom cod : Shape C}
    [Proper dom] [Proper cod]
    (σ : Subst C pre dom cod) (τ : Shape C) [Proper τ]
    {α} (z : pre ∋ α)
    (args : (i : C.Binder α) → Expr (pre ⧺ dom ⧺ τ ∷ i.arity)) :
  σ.act τ (.ap ((Proper.inl (pre ⧺ dom)) ((Proper.inl pre) z)) args)
    = .ap ((Proper.inl (pre ⧺ cod)) ((Subst.weakenCod σ) z)) (fun i => σ.act (τ ∷ i.arity) (args i))
  := by
  conv => lhs; unfold Subst.act
  rw [Subst.classifySite_inl_pre]

/-! ## Auxiliary: η-action on a right-injected slot -/

/-- Acting on the η-expansion of a right-injected (S-side) slot reproduces
the η in the target shape.  By WF recursion on the slot's arity `α`; uses
`act_apply_inr` as a black-box computation lemma. -/
theorem Subst.act_η_inr
    {C : Carrier} {pre dom cod : Shape C}
    [Proper dom] [Proper cod]
    (σ : Subst C pre dom cod) (τ : Shape C) [Proper τ]
    {α} (x : τ ∋ α) :
  σ.act (τ ∷ α) (.η ((Proper.inr (pre ⧺ dom)) x))
    = .η ((Proper.inr (pre ⧺ cod)) x)
  := by
  rw [Expr.η.eq_1]
  -- `.there ((inr τ) x) = (inr (τ ∷ α)) (.there x)` holds
  -- definitionally (instCons.inr); `change` accepts the defeq.
  change σ.act (τ ∷ α)
      (.ap ((Proper.inr (pre ⧺ dom))
                     (.there x))
                  (fun i => .η (.here i))) = _
  rw [Subst.act_ap_inr σ (τ ∷ α) (.there x)]
  rw [Expr.η.eq_1]
  congr 1
  funext i
  exact Subst.act_η_inr σ (τ ∷ α)
          (x := @ListSlotAt.here C α τ.toList i)
termination_by α
decreasing_by exact ⟨i, rfl⟩

/-! ## Instantiation laws: identity action and β-for-η -/

/-- Identity instantiation acts as the identity, given the β-for-η
property at the immediate sub-arities of the head arity.  The proof
recurses over the expression. -/
private theorem idOf
    {C : Carrier} (α : C.Arity) (Δ : Shape C)
    (hη : ∀ (i : C.Binder α), ∀ {pre cod : Shape C} [Proper cod]
      (ι : ∀ {β : C.Arity}, (⌊i.arity⌋) ∋ β → Expr (pre ⧺ cod ∷ β))
      (p : pre ∋ i.arity),
      ⟦Subst.inst (⌊i.arity⌋) ι⟧ˢ (.η p)
        = .ap ((Proper.inl pre) p) (fun j => ι (.here j))) :
  ∀ (τ : Shape C) [Proper τ] (e : Expr ((Δ ∷ α) ⧺ τ)),
    (Subst.instId Δ α).act τ e = e
  | τ, _, .ap (α := β) head argFam => by
      have ih_all : ∀ (k : C.Binder β),
          (Subst.instId Δ α).act (τ ∷ k.arity) (argFam k) = argFam k :=
        fun k => idOf α Δ hη (τ ∷ k.arity) (argFam k)
      rcases Proper.cover (Δ ∷ α) head with ⟨y, h_y⟩ | ⟨y, h_y⟩
      · subst h_y
        refine (Subst.act_ap_inr (Subst.instId Δ α) τ y argFam).trans ?_
        congr
        funext k
        exact ih_all k
      · subst h_y
        rcases Proper.cover Δ y with ⟨z, h_z⟩ | ⟨z, h_z⟩
        · subst h_z
          cases z with
          | here i =>
              refine (Subst.act_ap_inl_dom
                (Subst.instId Δ α) τ (.here i) argFam).trans ?_
              rw [show (Subst.instId Δ α).sub (.here i)
                    = @Expr.η C (Δ ∷ α) i.arity (.here i) from rfl]
              refine (hη i (pre := Δ ∷ α) (cod := τ)
                (ι := _) (p := .here i)).trans ?_
              change
                Expr.ap ((Proper.inl (Δ ∷ α))
                    (.here i))
                  (fun k => (Subst.instId Δ α).act (τ ∷ k.arity) (argFam k))
                =
                Expr.ap ((Proper.inl (Δ ∷ α))
                    (.here i)) argFam
              congr 1
              funext k
              exact ih_all k
          | there z' => nomatch z'
        · subst h_z
          refine (Subst.act_ap_inl_pre (Subst.instId Δ α) τ z argFam).trans ?_
          change
            Expr.ap ((Proper.inl (Δ ∷ α))
                ((Proper.inl Δ) z))
              (fun k => (Subst.instId Δ α).act (τ ∷ k.arity) (argFam k))
            =
            Expr.ap ((Proper.inl (Δ ∷ α))
                ((Proper.inl Δ) z)) argFam
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
theorem Subst.act_inst.η
    {C : Carrier} {pre cod : Shape C} [Proper cod]
    {α} (ι : ∀ {β : C.Arity}, ⌊α⌋ ∋ β → Expr (pre ⧺ cod ∷ β))
    (p : pre ∋ α) :
  ⟦Subst.inst ⌊α⌋ ι⟧ˢ (.η p)
    = .ap ((Proper.inl pre) p) (fun i => ι (.here i))
  := by
  rw [Expr.η.eq_1]
  change ⟦Subst.inst ⌊α⌋ ι⟧ˢ
      (.ap ((Proper.inl (pre ⧺ ⌊α⌋))
        ((Proper.inl pre) p)) (fun i => .η (.here i))) = _
  rw [Subst.act_ap_inl_pre]
  change
    Expr.ap ((Subst.inst ⌊α⌋ ι).weakenCod p)
      (fun i => (Subst.inst ⌊α⌋ ι).act
        (⌊i.arity⌋) (.η (.here i)))
    =
    Expr.ap ((Proper.inl pre) p)
      (fun i => ι (.here i))
  change
    Expr.ap ((Proper.inl pre) p)
      (fun i => (Subst.inst ⌊α⌋ ι).act
        (⌊i.arity⌋) (.η (.here i)))
    =
    Expr.ap ((Proper.inl pre) p)
      (fun i => ι (.here i))
  congr
  funext i
  rw [Expr.η.eq_1]
  change (Subst.inst ⌊α⌋ ι).act (⌊i.arity⌋)
      (.ap ((Proper.inl (pre ⧺ ⌊α⌋))
        ((Proper.inr pre) (.here i)))
        (fun k =>
          @Expr.η C
            ((pre ⧺ ⌊α⌋) ⧺ (⌊i.arity⌋))
            k.arity (.here k))) = _
  rw [Subst.act_ap_inl_dom]
  rw [show (Subst.inst ⌊α⌋ ι).sub (.here i)
        = ι (.here i) from rfl]
  have hfill : ∀ (k : C.Binder i.arity),
      (Subst.inst ⌊α⌋ ι).act
        ((⌊i.arity⌋) ∷ k.arity)
          (@Expr.η C
            ((pre ⧺ ⌊α⌋) ⧺ (⌊i.arity⌋))
            k.arity (.here k))
      =
        @Expr.η C
          ((pre ⧺ cod) ⧺ (⌊i.arity⌋))
          k.arity (.here k)
          := by
    intro k
    exact Subst.act_η_inr (Subst.inst ⌊α⌋ ι)
      (⌊i.arity⌋) (x := .here k)
  simp only [hfill]
  exact Subst.act_inst.id i.arity (pre ⧺ cod) Shape.nil
    (ι (.here i))
termination_by α
decreasing_by exact ⟨i, rfl⟩

/-- Identity instantiation acts as the identity. -/
theorem Subst.act_inst.id
    {C : Carrier} (α : C.Arity) (Δ : Shape C) :
  ∀ (τ : Shape C) [Proper τ] (e : Expr ((Δ ∷ α) ⧺ τ)),
    (Subst.instId Δ α).act τ e = e
  :=
  fun τ _ e =>
    idOf α Δ (fun i => Subst.act_inst.η) τ e
termination_by α
decreasing_by exact ⟨i, rfl⟩

end

/-! ## Monad laws -/

/-- **`act_id`** — the identity substitution acts as the identity.
Translates to `lift η = 𝟙` (unit_right).  Generalised over τ so the
recursive call on each arg fits the same statement. -/
theorem Subst.act_id
    {C : Carrier} (Γ : Shape C) [Proper Γ]
    (τ : Shape C) [Proper τ]
    (e : Expr (Γ ⧺ τ)) :
  (Subst.id Γ).act τ e = e
  := by
  match e with
  | .ap (α := β) x args =>
    rcases Proper.cover Γ x with
      ⟨y, h_y⟩ | ⟨y, h_y⟩
    · -- head = inr x; the τ-side branch fires.
      subst h_y
      refine (Subst.act_ap_inr (Subst.id Γ) τ y args).trans ?_
      congr ; funext k ; apply Subst.act_id
    · -- head = inl y; y : Γ ∋ β.  Cover y at base Shape.nil:
      -- inl-from-nil is empty, so y is necessarily in the right image.
      subst h_y
      rcases Proper.cover Shape.nil y with ⟨y, h_q⟩ | ⟨z, _⟩
      · subst h_q
        refine (Subst.act_ap_inl_dom (Subst.id Γ) τ y args).trans ?_
        -- Simplify (Subst.id Γ) y = Expr.η y (rfl via toSubst_sub).
        show ⟦Subst.inst ⌊β⌋ (fun q => match q with
              | .here k => (Subst.id Γ).act (τ ∷ k.arity) (args k))⟧ˢ
              (.η y) = _
        -- IH on each argument:
        have h_args : ∀ (k : C.Binder β),
            (Subst.id Γ).act (τ ∷ k.arity) (args k) = args k :=
          fun k => Subst.act_id Γ (τ ∷ k.arity) (args k)
        -- Simplify (inr Shape.nil) y = y on the RHS.
        rw [Proper.inr_nil_id y]
        refine (Subst.act_inst.η
          (pre := Γ) (cod := τ) (α := β) (ι := _) (p := y)).trans ?_
        change
          Expr.ap ((Proper.inl Γ) y)
            (fun k => (Subst.id Γ).act (τ ∷ k.arity) (args k))
          =
          Expr.ap ((Proper.inl Γ) y) args
        congr 1
        funext k
        exact h_args k
      · exact nomatch z
termination_by (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args _

/-- **`act_η`** — acting on an η-expansion reduces to applying `f`.
Translates to `lift f ∘ η = f` (unit_left). -/
theorem Subst.act_η
    {C : Carrier} {Γ Δ : Shape C} [Proper Γ] [Proper Δ]
    (f : ∀ {β : C.Arity}, Γ ∋ β → Expr (Δ ∷ β))
    (α : C.Arity) (p : Γ ∋ α) :
  (toSubst f).act ⌊α⌋ (.η p) = f p
  := by
  rw [Expr.η.eq_1]
  -- `.there p = (weaken_{⌊α⌋} _) p` by instCons.weaken (rfl).
  -- Cover p at base Shape.nil: p must be in the right image (inl-from-nil empty).
  rcases Proper.cover Shape.nil p with ⟨y, h_q⟩ | ⟨z, _⟩
  · subst h_q
    show (toSubst f).act ⌊α⌋
        (.ap ((Proper.inl (Shape.nil ⧺ Γ))
                      ((Proper.inr Shape.nil) y))
                    (fun i => .η (.here i))) = _
    rw [Subst.act_ap_inl_dom (toSubst f) ⌊α⌋ y]
    have hfill : ∀ (i : C.Binder α),
        (toSubst f).act (⌊α⌋ ∷ i.arity)
          (@Expr.η C
            ((Shape.nil ⧺ Γ) ⧺ ⌊α⌋)
            i.arity (.here i))
        =
        @Expr.η C
          ((Shape.nil ⧺ Δ) ⧺ ⌊α⌋)
          i.arity (.here i)
          := by
      intro i
      exact Subst.act_η_inr (toSubst f) ⌊α⌋
        (x := .here i)
    simp only [hfill]
    rw [toSubst_sub]
    rw [Proper.inr_nil_id y]
    exact Subst.act_inst.id α Δ Shape.nil (f y)
  · exact nomatch z

/-- `Expr.Subterm.of_arg` repackaged for the descent shape
`Γ ⧺ Tele.ofList (j.arity :: ρ)`. -/
private theorem Expr.Subterm.of_arg_ofList_cons
    {C : Carrier} {Γ : Shape C}
    (ρ : List C.Arity) {α}
    (head : Γ ⧺ Tele.ofList ρ ∋ α)
    (args : (i : C.Binder α) → Expr (Γ ⧺ Tele.ofList ρ ∷ i.arity))
    (j : C.Binder α) :
  Expr.Subterm
    ⟨Γ ⧺ Tele.ofList (j.arity :: ρ), args j⟩
    ⟨Γ ⧺ Tele.ofList ρ, .ap head args⟩
  := by
  simpa [Shape.extList, Shape.ext, Tele.comp, Tele.ofList] using
    (Expr.Subterm.of_arg head args j)

/-- A slot of the singleton list `[α]` has sub-arity α. -/
private theorem ListSlotAt.sub_single
    {C : Carrier} {α β : C.Arity} (x : (⌊α⌋ : Shape C) ∋ β) :
  Carrier.Sub β α
  := by
  cases x with
  | here i => exact ⟨i, rfl⟩
  | there z => nomatch z

/-! ## General substitution diamond for composition -/

private abbrev instOne
    {C : Carrier} {pre : Shape C} (α : C.Arity) (cod : Shape C)
    (f : (i : C.Binder α) → Expr (pre ⧺ cod ∷ i.arity)) :
    Subst C pre ⌊α⌋ cod :=
  Subst.inst ⌊α⌋ (fun q => match q with | .here i => f i)

private structure TargetProper {C : Carrier}
    (τ src dst : Shape C) (υ : List C.Arity) where
  hτ : Proper τ
  hSrcShape : Proper src
  hDstShape : Proper dst
  hSrc : Proper (τ ⧺ src)
  hDst : Proper (τ ⧺ dst)
  hSrc_inr_src : ∀ (Γ : Shape C) {α : C.Arity} (x : src ∋ α),
    letI : Proper τ := hτ
    letI : Proper src := hSrcShape
    letI : Proper (τ ⧺ src) := hSrc
    (Proper.inr Γ : (τ ⧺ src) →ʳ Γ ⧺ (τ ⧺ src))
      ((Proper.inr τ : src →ʳ τ ⧺ src) x)
    =
    (Proper.inr (Γ ⧺ τ) : src →ʳ Γ ⧺ τ ⧺ src) x
  hSrc_inr_tau : ∀ (Γ : Shape C) {α : C.Arity} (x : τ ∋ α),
    letI : Proper τ := hτ
    letI : Proper src := hSrcShape
    letI : Proper (τ ⧺ src) := hSrc
    (Proper.inr Γ : (τ ⧺ src) →ʳ Γ ⧺ (τ ⧺ src))
      ((Proper.inl τ : τ →ʳ τ ⧺ src) x)
    =
    (Proper.inl (Γ ⧺ τ) : Γ ⧺ τ →ʳ Γ ⧺ τ ⧺ src)
      ((Proper.inr Γ : τ →ʳ Γ ⧺ τ) x)
  hSrc_inl : ∀ (Γ : Shape C) {α : C.Arity} (x : Γ ∋ α),
    letI : Proper τ := hτ
    letI : Proper src := hSrcShape
    letI : Proper (τ ⧺ src) := hSrc
    (Proper.inl Γ : Γ →ʳ Γ ⧺ (τ ⧺ src)) x
    =
    (Proper.inl (Γ ⧺ τ) : Γ ⧺ τ →ʳ Γ ⧺ τ ⧺ src)
      ((Proper.inl Γ : Γ →ʳ Γ ⧺ τ) x)
  hDst_inr_dst : ∀ (Γ : Shape C) {α : C.Arity} (x : dst ∋ α),
    letI : Proper τ := hτ
    letI : Proper dst := hDstShape
    letI : Proper (τ ⧺ dst) := hDst
    (Proper.inr Γ : (τ ⧺ dst) →ʳ Γ ⧺ (τ ⧺ dst))
      ((Proper.inr τ : dst →ʳ τ ⧺ dst) x)
    =
    (Proper.inr (Γ ⧺ τ) : dst →ʳ Γ ⧺ τ ⧺ dst) x
  hDst_inr_tau : ∀ (Γ : Shape C) {α : C.Arity} (x : τ ∋ α),
    letI : Proper τ := hτ
    letI : Proper dst := hDstShape
    letI : Proper (τ ⧺ dst) := hDst
    (Proper.inr Γ : (τ ⧺ dst) →ʳ Γ ⧺ (τ ⧺ dst))
      ((Proper.inl τ : τ →ʳ τ ⧺ dst) x)
    =
    (Proper.inl (Γ ⧺ τ) : Γ ⧺ τ →ʳ Γ ⧺ τ ⧺ dst)
      ((Proper.inr Γ : τ →ʳ Γ ⧺ τ) x)
  hDst_inl : ∀ (Γ : Shape C) {α : C.Arity} (x : Γ ∋ α),
    letI : Proper τ := hτ
    letI : Proper dst := hDstShape
    letI : Proper (τ ⧺ dst) := hDst
    (Proper.inl Γ : Γ →ʳ Γ ⧺ (τ ⧺ dst)) x
    =
    (Proper.inl (Γ ⧺ τ) : Γ ⧺ τ →ʳ Γ ⧺ τ ⧺ dst)
      ((Proper.inl Γ : Γ →ʳ Γ ⧺ τ) x)

private abbrev TargetProper.hSrcUnder {C : Carrier}
    {τ src dst : Shape C} {υ : List C.Arity}
    (target : TargetProper τ src dst υ) :
    Proper ((τ ⧺ src) ⧺ Tele.ofList υ) := by
  letI : Proper (τ ⧺ src) := target.hSrc
  exact Proper.extendList (τ ⧺ src) υ

private abbrev TargetProper.hDstUnder {C : Carrier}
    {τ src dst : Shape C} {υ : List C.Arity}
    (target : TargetProper τ src dst υ) :
    Proper ((τ ⧺ dst) ⧺ Tele.ofList υ) := by
  letI : Proper (τ ⧺ dst) := target.hDst
  exact Proper.extendList (τ ⧺ dst) υ

private abbrev TargetProper.base {C : Carrier}
    (τ src dst : Shape C) [Proper τ] [Proper src] [Proper dst]
    (υ : List C.Arity) :
    TargetProper τ src dst υ where
  hτ := inferInstance
  hSrcShape := inferInstance
  hDstShape := inferInstance
  hSrc := Proper.compose τ src
  hDst := Proper.compose τ dst
  hSrc_inr_src := by
    intro Γ α x
    exact Proper.compose_inr_inr τ src Γ x
  hSrc_inr_tau := by
    intro Γ α x
    exact Proper.compose_inr_inl τ src Γ x
  hSrc_inl := by
    intro Γ α x
    exact Proper.compose_inl τ src Γ x
  hDst_inr_dst := by
    intro Γ α x
    exact Proper.compose_inr_inr τ dst Γ x
  hDst_inr_tau := by
    intro Γ α x
    exact Proper.compose_inr_inl τ dst Γ x
  hDst_inl := by
    intro Γ α x
    exact Proper.compose_inl τ dst Γ x

private abbrev TargetProper.nil {C : Carrier}
    (src dst : Shape C) [Proper src] [Proper dst]
    (υ : List C.Arity) :
    TargetProper Shape.nil src dst υ where
  hτ := inferInstance
  hSrcShape := inferInstance
  hDstShape := inferInstance
  hSrc := inferInstanceAs (Proper src)
  hDst := inferInstanceAs (Proper dst)
  hSrc_inr_src := by
    intro Γ α x
    rw [Proper.inr_nil_id x]
    change (Proper.inr Γ) x = (Proper.inr Γ) x
    rfl
  hSrc_inr_tau := by
    intro Γ α x
    nomatch x
  hSrc_inl := by
    intro Γ α x
    rfl
  hDst_inr_dst := by
    intro Γ α x
    rw [Proper.inr_nil_id x]
    change (Proper.inr Γ) x = (Proper.inr Γ) x
    rfl
  hDst_inr_tau := by
    intro Γ α x
    nomatch x
  hDst_inl := by
    intro Γ α x
    rfl

private abbrev TargetProper.hSrcExt {C : Carrier}
    {τ src dst : Shape C} {υ : List C.Arity}
    (target : TargetProper τ src dst υ) (β : C.Arity) :
    Proper ((τ ⧺ src) ∷ β) :=
  letI : Proper τ := target.hτ
  letI : Proper src := target.hSrcShape
  letI : Proper (τ ⧺ src) := target.hSrc
  inferInstance

private abbrev TargetProper.hDstExt {C : Carrier}
    {τ src dst : Shape C} {υ : List C.Arity}
    (target : TargetProper τ src dst υ) (β : C.Arity) :
    Proper ((τ ⧺ dst) ∷ β) :=
  letI : Proper τ := target.hτ
  letI : Proper dst := target.hDstShape
  letI : Proper (τ ⧺ dst) := target.hDst
  inferInstance

private abbrev TargetProper.arg {C : Carrier}
    {τ src dst : Shape C} {υ : List C.Arity}
    (target : TargetProper τ src dst υ) (β : C.Arity) :
    TargetProper τ src dst (β :: υ) where
  hτ := target.hτ
  hSrcShape := target.hSrcShape
  hDstShape := target.hDstShape
  hSrc := target.hSrc
  hDst := target.hDst
  hSrc_inr_src := target.hSrc_inr_src
  hSrc_inr_tau := target.hSrc_inr_tau
  hSrc_inl := target.hSrc_inl
  hDst_inr_dst := target.hDst_inr_dst
  hDst_inr_tau := target.hDst_inr_tau
  hDst_inl := target.hDst_inl

private abbrev TargetProper.srcStep {C : Carrier}
    {τ src dst : Shape C} {υ : List C.Arity}
    (target : TargetProper τ src dst υ) (β : C.Arity) :
    TargetProper (τ ⧺ dst) ⌊β⌋ (Tele.ofList υ) [] where
  hτ := target.hDst
  hSrcShape := inferInstance
  hDstShape := inferInstance
  hSrc := target.hDstExt β
  hDst := target.hDstUnder
  hSrc_inr_src := by
    intro Γ α x
    cases x with
    | here i => rfl
    | there z => nomatch z
  hSrc_inr_tau := by
    intro Γ α x
    rfl
  hSrc_inl := by
    intro Γ α x
    rfl
  hDst_inr_dst := by
    intro Γ α x
    letI : Proper (τ ⧺ dst) := target.hDst
    exact Proper.extendList_inr_inr (τ ⧺ dst) υ Γ x
  hDst_inr_tau := by
    intro Γ α x
    letI : Proper (τ ⧺ dst) := target.hDst
    exact Proper.extendList_inr_inl (τ ⧺ dst) υ Γ x
  hDst_inl := by
    intro Γ α x
    letI : Proper (τ ⧺ dst) := target.hDst
    exact Proper.extendList_inl (τ ⧺ dst) υ Γ x

private abbrev TargetProper.liftBeta {C : Carrier}
    (υ χ : List C.Arity) {β : C.Arity} (j : C.Binder β) :
    TargetProper (Tele.ofList υ) ⌊j.arity⌋ (Tele.ofList χ) [] where
  hτ := inferInstance
  hSrcShape := inferInstance
  hDstShape := inferInstance
  hSrc := by
    letI : Proper (Tele.ofList υ : Shape C) := inferInstance
    exact Proper.extendList (Tele.ofList υ : Shape C) [j.arity]
  hDst := by
    letI : Proper (Tele.ofList υ : Shape C) := inferInstance
    exact Proper.extendList (Tele.ofList υ : Shape C) χ
  hSrc_inr_src := by
    intro Γ α x
    letI : Proper (Tele.ofList υ : Shape C) := inferInstance
    exact Proper.extendList_inr_inr (Tele.ofList υ : Shape C) [j.arity] Γ x
  hSrc_inr_tau := by
    intro Γ α x
    letI : Proper (Tele.ofList υ : Shape C) := inferInstance
    exact Proper.extendList_inr_inl (Tele.ofList υ : Shape C) [j.arity] Γ x
  hSrc_inl := by
    intro Γ α x
    letI : Proper (Tele.ofList υ : Shape C) := inferInstance
    exact Proper.extendList_inl (Tele.ofList υ : Shape C) [j.arity] Γ x
  hDst_inr_dst := by
    intro Γ α x
    letI : Proper (Tele.ofList υ : Shape C) := inferInstance
    exact Proper.extendList_inr_inr (Tele.ofList υ : Shape C) χ Γ x
  hDst_inr_tau := by
    intro Γ α x
    letI : Proper (Tele.ofList υ : Shape C) := inferInstance
    exact Proper.extendList_inr_inl (Tele.ofList υ : Shape C) χ Γ x
  hDst_inl := by
    intro Γ α x
    letI : Proper (Tele.ofList υ : Shape C) := inferInstance
    exact Proper.extendList_inl (Tele.ofList υ : Shape C) χ Γ x

private abbrev actAt
    {C : Carrier} {pre dom cod τ : Shape C}
    [Proper dom] [Proper cod]
    (σ : Subst C pre dom cod)
    (hτ : Proper τ)
    (e : Expr (pre ⧺ dom ⧺ τ)) :
    Expr (pre ⧺ cod ⧺ τ) :=
  @Subst.act C pre dom cod inferInstance inferInstance σ τ hτ e

namespace Diamond

private abbrev acted
    {C : Carrier} {pre dom cod τ src dst : Shape C}
    [Proper dom] [Proper cod] [Proper τ] [Proper src] [Proper dst]
    (σ : Subst C pre dom cod)
    {υ : List C.Arity}
    (target : TargetProper τ src dst υ)
    (κ : Subst C (pre ⧺ dom ⧺ τ) src dst) :
    Subst C (pre ⧺ cod ⧺ τ) src dst :=
  letI : Proper τ := target.hτ
  letI : Proper src := target.hSrcShape
  letI : Proper dst := target.hDstShape
  Subst.inst src (fun {β} x =>
    actAt (pre := pre) (dom := dom) (cod := cod)
      σ (target.hDstExt β) (κ.sub x))

private abbrev actThenInst
    {C : Carrier} {pre dom cod τ src dst : Shape C}
    [Proper dom] [Proper cod] [Proper τ] [Proper src] [Proper dst]
    (σ : Subst C pre dom cod)
    {υ : List C.Arity}
    (target : TargetProper τ src dst υ)
    (κ : Subst C (pre ⧺ dom ⧺ τ) src dst)
    (e : Expr (((pre ⧺ dom ⧺ τ) ⧺ src) ⧺ Tele.ofList υ)) :=
  letI : Proper τ := target.hτ
  letI : Proper src := target.hSrcShape
  letI : Proper dst := target.hDstShape
  (acted σ target κ).act (Tele.ofList υ)
    (actAt (pre := pre) (dom := dom) (cod := cod)
      σ target.hSrcUnder e)

private abbrev instThenAct
    {C : Carrier} {pre dom cod τ src dst : Shape C}
    [Proper dom] [Proper cod] [Proper τ] [Proper src] [Proper dst]
    (σ : Subst C pre dom cod)
    {υ : List C.Arity}
    (target : TargetProper τ src dst υ)
    (κ : Subst C (pre ⧺ dom ⧺ τ) src dst)
    (e : Expr (((pre ⧺ dom ⧺ τ) ⧺ src) ⧺ Tele.ofList υ)) :=
  letI : Proper τ := target.hτ
  letI : Proper src := target.hSrcShape
  letI : Proper dst := target.hDstShape
  actAt (pre := pre) (dom := dom) (cod := cod)
    σ target.hDstUnder
    (κ.act (Tele.ofList υ) e)

end Diamond

namespace Lift

private abbrev sequential
    {C : Carrier} {pre τ src dst : Shape C}
    [Proper τ] [Proper src] [Proper dst]
    {υ : List C.Arity}
    (target : TargetProper τ src dst υ)
    (κ : Subst C (pre ⧺ τ) src dst)
    {β : C.Arity} (χ : List C.Arity)
    (η : (j : C.Binder β) →
      Expr (((pre ⧺ τ) ⧺ src) ⧺ Tele.ofList υ ∷ j.arity))
    (e : Expr ((pre ∷ β) ⧺ Tele.ofList χ)) :=
  letI : Proper τ := target.hτ
  letI : Proper src := target.hSrcShape
  letI : Proper dst := target.hDstShape
  let lam : Subst C pre ⌊β⌋ ((τ ⧺ src) ⧺ Tele.ofList υ) :=
    instOne β ((τ ⧺ src) ⧺ Tele.ofList υ) η
  letI : Proper ((τ ⧺ src) ⧺ Tele.ofList υ) := target.hSrcUnder
  κ.act ((Tele.ofList υ) ⧺ Tele.ofList χ)
    (lam.act (Tele.ofList χ) e)

private abbrev fused
    {C : Carrier} {pre τ src dst : Shape C}
    [Proper τ] [Proper src] [Proper dst]
    {υ : List C.Arity}
    (target : TargetProper τ src dst υ)
    (κ : Subst C (pre ⧺ τ) src dst)
    {β : C.Arity} (χ : List C.Arity)
    (η : (j : C.Binder β) →
      Expr (((pre ⧺ τ) ⧺ src) ⧺ Tele.ofList υ ∷ j.arity))
    (e : Expr ((pre ∷ β) ⧺ Tele.ofList χ)) :=
  letI : Proper τ := target.hτ
  letI : Proper src := target.hSrcShape
  letI : Proper dst := target.hDstShape
  let lam' : Subst C pre ⌊β⌋ ((τ ⧺ dst) ⧺ Tele.ofList υ) :=
    instOne β ((τ ⧺ dst) ⧺ Tele.ofList υ)
      (fun j => κ.act (Tele.ofList υ ∷ j.arity) (η j))
  letI : Proper ((τ ⧺ dst) ⧺ Tele.ofList υ) := target.hDstUnder
  lam'.act (Tele.ofList χ) e

end Lift

private inductive DiamondSite {C : Carrier}
    (pre dom τ src : Shape C) (υ : List C.Arity) : C.Arity → Type where
  | under {β} (xυ : Tele.ofList υ ∋ β) : DiamondSite pre dom τ src υ β
  | src {β} (xsrc : src ∋ β) : DiamondSite pre dom τ src υ β
  | tau {β} (xτ : τ ∋ β) : DiamondSite pre dom τ src υ β
  | dom {β} (z : dom ∋ β) : DiamondSite pre dom τ src υ β
  | pre {β} (z : pre ∋ β) : DiamondSite pre dom τ src υ β

private def DiamondSite.embed {C : Carrier}
    {pre dom τ src dst : Shape C} [Proper dom] [Proper τ] [Proper src]
    {β : C.Arity} {υ : List C.Arity}
    (target : TargetProper τ src dst υ) :
    DiamondSite pre dom τ src υ β →
      (((pre ⧺ dom ⧺ τ) ⧺ src) ⧺ Tele.ofList υ) ∋ β :=
  letI : Proper (τ ⧺ src) := target.hSrc
  letI : Proper ((τ ⧺ src) ⧺ Tele.ofList υ) := target.hSrcUnder
  fun
  | .under xυ =>
      ((Proper.inr (pre ⧺ dom)) :
        ((τ ⧺ src) ⧺ Tele.ofList υ) →ʳ
          (pre ⧺ dom) ⧺ ((τ ⧺ src) ⧺ Tele.ofList υ))
        ((Proper.inr (τ ⧺ src)) xυ)
  | .src xsrc =>
      ((Proper.inr (pre ⧺ dom)) :
        ((τ ⧺ src) ⧺ Tele.ofList υ) →ʳ
          (pre ⧺ dom) ⧺ ((τ ⧺ src) ⧺ Tele.ofList υ))
        ((Proper.inl (τ ⧺ src)) ((Proper.inr τ) xsrc))
  | .tau xτ =>
      ((Proper.inr (pre ⧺ dom)) :
        ((τ ⧺ src) ⧺ Tele.ofList υ) →ʳ
          (pre ⧺ dom) ⧺ ((τ ⧺ src) ⧺ Tele.ofList υ))
        ((Proper.inl (τ ⧺ src)) ((Proper.inl τ) xτ))
  | .dom z =>
      ((Proper.inl (pre ⧺ dom)) :
        (pre ⧺ dom) →ʳ
          (pre ⧺ dom) ⧺ ((τ ⧺ src) ⧺ Tele.ofList υ))
        ((Proper.inr pre) z)
  | .pre z =>
      ((Proper.inl (pre ⧺ dom)) :
        (pre ⧺ dom) →ʳ
          (pre ⧺ dom) ⧺ ((τ ⧺ src) ⧺ Tele.ofList υ))
        ((Proper.inl pre) z)

private theorem DiamondSite.cover {C : Carrier}
    {pre dom τ src dst : Shape C} [Proper dom] [Proper τ] [Proper src]
    {β : C.Arity} {υ : List C.Arity}
    (target : TargetProper τ src dst υ)
    (head : (((pre ⧺ dom ⧺ τ) ⧺ src) ⧺ Tele.ofList υ) ∋ β) :
    ∃ site : DiamondSite pre dom τ src υ β,
      head = DiamondSite.embed target site := by
  letI : Proper (τ ⧺ src) := target.hSrc
  letI : Proper ((τ ⧺ src) ⧺ Tele.ofList υ) := target.hSrcUnder
  obtain ⟨site, h_site⟩ :=
    Subst.coverSite (pre := pre) (dom := dom)
      (τ := (τ ⧺ src) ⧺ Tele.ofList υ) head
  subst h_site
  cases site with
  | tau top =>
      rcases Proper.cover (Γ := Tele.ofList υ) (τ ⧺ src) top with
        ⟨xυ, h_xυ⟩ | ⟨base, h_base⟩
      · subst h_xυ
        refine ⟨.under xυ, ?_⟩
        unfold DiamondSite.embed Subst.embedSource
        rfl
      · subst h_base
        rcases Proper.cover (Γ := src) τ base with
          ⟨xsrc, h_xsrc⟩ | ⟨xτ, h_xτ⟩
        · subst h_xsrc
          refine ⟨.src xsrc, ?_⟩
          unfold DiamondSite.embed Subst.embedSource
          rfl
        · subst h_xτ
          refine ⟨.tau xτ, ?_⟩
          unfold DiamondSite.embed Subst.embedSource
          rfl
  | dom z =>
      refine ⟨.dom z, ?_⟩
      unfold DiamondSite.embed Subst.embedSource
      rfl
  | pre z =>
      refine ⟨.pre z, ?_⟩
      unfold DiamondSite.embed Subst.embedSource
      rfl

private inductive LiftSite {C : Carrier}
    (pre : Shape C) (β : C.Arity) (χ : List C.Arity) : C.Arity → Type where
  | under {γ} (xχ : Tele.ofList χ ∋ γ) : LiftSite pre β χ γ
  | beta (j : C.Binder β) : LiftSite pre β χ j.arity
  | pre {γ} (z : pre ∋ γ) : LiftSite pre β χ γ

private def LiftSite.embed {C : Carrier}
    {pre : Shape C} {β γ : C.Arity} {χ : List C.Arity} :
    LiftSite pre β χ γ → ((pre ∷ β) ⧺ Tele.ofList χ) ∋ γ
  | .under xχ => (Proper.inr (pre ∷ β)) xχ
  | .beta j => (Proper.inl (pre ∷ β)) ((Proper.inr pre) (.here j))
  | .pre z => (Proper.inl (pre ∷ β)) ((Proper.inl pre) z)

private theorem LiftSite.cover {C : Carrier}
    {pre : Shape C} {β γ : C.Arity} {χ : List C.Arity}
    (head : ((pre ∷ β) ⧺ Tele.ofList χ) ∋ γ) :
    ∃ site : LiftSite pre β χ γ, head = LiftSite.embed site := by
  rcases Proper.cover (Γ := Tele.ofList χ) (pre ∷ β) head with
    ⟨xχ, h_xχ⟩ | ⟨below, h_below⟩
  · subst h_xχ
    exact ⟨.under xχ, rfl⟩
  · subst h_below
    rcases Proper.cover pre below with ⟨xβ, h_xβ⟩ | ⟨z, h_z⟩
    · subst h_xβ
      cases xβ with
      | here j => exact ⟨.beta j, rfl⟩
      | there z => nomatch z
    · subst h_z
      exact ⟨.pre z, rfl⟩

/-- Two active substitution-domain fuels, considered up to swapping.  The mutual
diamond/lift proof either descends in one fuel component or keeps the fuel fixed
and descends into an expression argument. -/
private structure InterchangeFuel (C : Carrier) where
  fst : DomMeasure C
  snd : DomMeasure C

/-- Strict-decrease relation on `InterchangeFuel`, allowing component swap. -/
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

/-- Both components of an `InterchangeFuel` pair are simultaneously accessible. -/
private theorem InterchangeFuel.Lt.accPair
    {C : Carrier} (a b : DomMeasure C) :
  Acc (InterchangeFuel.Lt (C := C)) ⟨a, b⟩ ∧ Acc (InterchangeFuel.Lt (C := C)) ⟨b, a⟩
  := by
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

/-- `InterchangeFuel.Lt` is well-founded. -/
private theorem InterchangeFuel.Lt.wf
    {C : Carrier} :
  WellFounded (InterchangeFuel.Lt (C := C))
  := by
  refine ⟨fun f => ?_⟩
  cases f with
  | mk a b =>
      exact (InterchangeFuel.Lt.accPair a b).1

private instance {C : Carrier} : WellFoundedRelation (InterchangeFuel C) where
  rel := InterchangeFuel.Lt
  wf := InterchangeFuel.Lt.wf

/-! ### Source-head classifiers for the one-binder interaction -/

mutual

private theorem diamondAt
    {C : Carrier} {pre dom cod τ src dst : Shape C}
    [Proper dom] [Proper cod] [Proper τ] [Proper src] [Proper dst]
    (σ : Subst C pre dom cod)
    {υ : List C.Arity}
    (target : TargetProper τ src dst υ)
    (κ : Subst C (pre ⧺ dom ⧺ τ) src dst)
    (e : Expr (((pre ⧺ dom ⧺ τ) ⧺ src) ⧺ Tele.ofList υ)) :
    Diamond.actThenInst σ target κ e = Diamond.instThenAct σ target κ e := by
  unfold Diamond.actThenInst Diamond.instThenAct
  letI : Proper τ := target.hτ
  letI : Proper src := target.hSrcShape
  letI : Proper dst := target.hDstShape
  letI : Proper (τ ⧺ src) := target.hSrc
  letI : Proper (τ ⧺ dst) := target.hDst
  letI : Proper ((τ ⧺ src) ⧺ Tele.ofList υ) := target.hSrcUnder
  letI : Proper ((τ ⧺ dst) ⧺ Tele.ofList υ) := target.hDstUnder
  match e with
  | .ap (α := β) head args =>
      have hargs : ∀ (j : C.Binder β),
          Diamond.actThenInst σ (target.arg j.arity) κ (args j)
            =
          Diamond.instThenAct σ (target.arg j.arity) κ (args j) :=
        fun j => diamondAt σ (target.arg j.arity) κ (args j)
      obtain ⟨site, h_site⟩ :=
        DiamondSite.cover (pre := pre) (dom := dom) (τ := τ)
          (src := src) (dst := dst) target head
      subst h_site
      cases site with
      | under xυ =>
          change (Diamond.acted σ target κ).act (Tele.ofList υ)
              (σ.act (τ ⧺ src ⧺ Tele.ofList υ)
                (.ap ((Proper.inr (pre ⧺ dom)) ((Proper.inr (τ ⧺ src)) xυ)) args))
            =
            σ.act (τ ⧺ dst ⧺ Tele.ofList υ)
              (κ.act (Tele.ofList υ)
                (.ap ((Proper.inr (pre ⧺ dom)) ((Proper.inr (τ ⧺ src)) xυ)) args))
          rw [Subst.act_ap_inr σ ((τ ⧺ src) ⧺ Tele.ofList υ)
            ((Proper.inr (τ ⧺ src)) xυ) args]
          rw [Proper.extendList_inr_inr (τ ⧺ src) υ (pre ⧺ cod) xυ]
          change (Diamond.acted σ target κ).act (Tele.ofList υ)
              (.ap ((Proper.inr ((pre ⧺ cod ⧺ τ) ⧺ src)) xυ)
                (fun j => σ.act (τ ⧺ src ⧺ Tele.ofList υ ∷ j.arity) (args j)))
            =
            σ.act (τ ⧺ dst ⧺ Tele.ofList υ)
              (κ.act (Tele.ofList υ)
                (.ap ((Proper.inr (pre ⧺ dom)) ((Proper.inr (τ ⧺ src)) xυ)) args))
          rw [Subst.act_ap_inr (Diamond.acted σ target κ) (Tele.ofList υ) xυ
            (fun j => σ.act (τ ⧺ src ⧺ Tele.ofList υ ∷ j.arity) (args j))]
          rw [Proper.extendList_inr_inr (τ ⧺ src) υ (pre ⧺ dom) xυ]
          change .ap ((Proper.inr ((pre ⧺ cod ⧺ τ) ⧺ dst)) xυ)
                (fun j => (Diamond.acted σ target κ).act (Tele.ofList υ ∷ j.arity)
                  (σ.act (τ ⧺ src ⧺ Tele.ofList υ ∷ j.arity) (args j)))
            =
            σ.act (τ ⧺ dst ⧺ Tele.ofList υ)
              (κ.act (Tele.ofList υ)
                (.ap ((Proper.inr ((pre ⧺ dom ⧺ τ) ⧺ src)) xυ) args))
          rw [Subst.act_ap_inr κ (Tele.ofList υ) xυ args]
          change .ap ((Proper.inr ((pre ⧺ cod ⧺ τ) ⧺ dst)) xυ)
                (fun j => (Diamond.acted σ target κ).act (Tele.ofList υ ∷ j.arity)
                  (σ.act (τ ⧺ src ⧺ Tele.ofList υ ∷ j.arity) (args j)))
            =
            σ.act (τ ⧺ dst ⧺ Tele.ofList υ)
              (.ap ((Proper.inr (pre ⧺ dom ⧺ (τ ⧺ dst))) xυ)
                (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j)))
          rw [← Proper.extendList_inr_inr (τ ⧺ dst) υ (pre ⧺ dom) xυ]
          rw [Subst.act_ap_inr σ ((τ ⧺ dst) ⧺ Tele.ofList υ)
            ((Proper.inr (τ ⧺ dst)) xυ)
            (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))]
          rw [Proper.extendList_inr_inr (τ ⧺ dst) υ (pre ⧺ cod) xυ]
          congr 1
          funext j
          exact hargs j
      | src xsrc =>
          change (Diamond.acted σ target κ).act (Tele.ofList υ)
              (σ.act (τ ⧺ src ⧺ Tele.ofList υ)
                (.ap
                  ((Proper.inr (pre ⧺ dom))
                    ((Proper.inl (τ ⧺ src)) ((Proper.inr τ) xsrc)))
                  args))
            =
            σ.act (τ ⧺ dst ⧺ Tele.ofList υ)
              (κ.act (Tele.ofList υ)
                (.ap
                  ((Proper.inr (pre ⧺ dom))
                    ((Proper.inl (τ ⧺ src)) ((Proper.inr τ) xsrc)))
                  args))
          rw [Subst.act_ap_inr σ ((τ ⧺ src) ⧺ Tele.ofList υ)
            ((Proper.inl (τ ⧺ src)) ((Proper.inr τ) xsrc)) args]
          rw [Proper.extendList_inr_inl (τ ⧺ src) υ (pre ⧺ cod)
            ((Proper.inr τ) xsrc)]
          rw [target.hSrc_inr_src (pre ⧺ cod) xsrc]
          change (Diamond.acted σ target κ).act (Tele.ofList υ)
              (.ap
                ((Proper.inl ((pre ⧺ cod ⧺ τ) ⧺ src))
                  ((Proper.inr (pre ⧺ cod ⧺ τ)) xsrc))
                (fun j => σ.act (τ ⧺ src ⧺ Tele.ofList υ ∷ j.arity) (args j)))
            =
            σ.act (τ ⧺ dst ⧺ Tele.ofList υ)
              (κ.act (Tele.ofList υ)
                (.ap
                  ((Proper.inr (pre ⧺ dom))
                    ((Proper.inl (τ ⧺ src)) ((Proper.inr τ) xsrc)))
                  args))
          rw [Subst.act_ap_inl_dom (Diamond.acted σ target κ) (Tele.ofList υ) xsrc
            (fun j => σ.act (τ ⧺ src ⧺ Tele.ofList υ ∷ j.arity) (args j))]
          rw [show (Diamond.acted σ target κ).sub xsrc =
              σ.act ((τ ⧺ dst) ∷ β) (κ.sub xsrc) from rfl]
          rw [Proper.extendList_inr_inl (τ ⧺ src) υ (pre ⧺ dom)
            ((Proper.inr τ) xsrc)]
          rw [target.hSrc_inr_src (pre ⧺ dom) xsrc]
          change ⟦Subst.inst ⌊β⌋
                (fun {δ} q => match q with
                | .here j =>
                    (Diamond.acted σ target κ).act (Tele.ofList υ ∷ j.arity)
                      (σ.act (τ ⧺ src ⧺ Tele.ofList υ ∷ j.arity) (args j)))⟧ˢ
              (σ.act ((τ ⧺ dst) ∷ β) (κ.sub xsrc))
            =
            σ.act (τ ⧺ dst ⧺ Tele.ofList υ)
              (κ.act (Tele.ofList υ)
                (.ap
                  ((Proper.inl ((pre ⧺ dom ⧺ τ) ⧺ src))
                    ((Proper.inr (pre ⧺ dom ⧺ τ)) xsrc))
                  args))
          rw [Subst.act_ap_inl_dom κ (Tele.ofList υ) xsrc args]
          rw [show κ.sub xsrc = κ.sub xsrc from rfl]
          let κβ : Subst C (pre ⧺ dom ⧺ (τ ⧺ dst)) ⌊β⌋ (Tele.ofList υ) :=
            instOne β (Tele.ofList υ)
              (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))
          letI : Proper (τ ⧺ dst) := target.hDst
          have hrec := diamondAt (τ := τ ⧺ dst) (src := ⌊β⌋)
            (dst := Tele.ofList υ) σ (target.srcStep β) κβ (e := κ.sub xsrc)
          unfold Diamond.actThenInst Diamond.instThenAct Diamond.acted at hrec
          have hf :
              (fun {δ : C.Arity} (q : ⌊β⌋ ∋ δ) =>
                match q with
                | .here j =>
                    (Diamond.acted σ target κ).act (Tele.ofList υ ∷ j.arity)
                      (σ.act (τ ⧺ src ⧺ Tele.ofList υ ∷ j.arity) (args j)))
              =
              (fun {δ : C.Arity} (q : ⌊β⌋ ∋ δ) =>
                σ.act (τ ⧺ dst ⧺ Tele.ofList υ ∷ δ) (κβ.sub q)) := by
            funext δ q
            cases q with
            | here j =>
                exact hargs j
            | there q => nomatch q
          have hSubst :
              Subst.inst (C := C) (pre := pre ⧺ cod ⧺ τ ⧺ dst)
                (dom := ⌊β⌋) (cod := Tele.ofList υ)
                (fun {δ : C.Arity} (q : ⌊β⌋ ∋ δ) =>
                  match q with
                  | .here j =>
                      (Diamond.acted σ target κ).act (Tele.ofList υ ∷ j.arity)
                        (σ.act (τ ⧺ src ⧺ Tele.ofList υ ∷ j.arity) (args j)))
              =
              Subst.inst (C := C) (pre := pre ⧺ cod ⧺ τ ⧺ dst)
                (dom := ⌊β⌋) (cod := Tele.ofList υ)
                (fun {δ : C.Arity} (q : ⌊β⌋ ∋ δ) =>
                  σ.act (τ ⧺ dst ⧺ Tele.ofList υ ∷ δ) (κβ.sub q)) := by
            exact congrArg
              (fun filler =>
                Subst.inst (C := C) (pre := pre ⧺ cod ⧺ τ ⧺ dst)
                  (dom := ⌊β⌋) (cod := Tele.ofList υ) filler)
              hf
          rw [hSubst]
          simpa only [κβ, instOne] using hrec
      | tau xτ =>
          change (Diamond.acted σ target κ).act (Tele.ofList υ)
              (σ.act (τ ⧺ src ⧺ Tele.ofList υ)
                (.ap
                  ((Proper.inr (pre ⧺ dom))
                    ((Proper.inl (τ ⧺ src)) ((Proper.inl τ) xτ)))
                  args))
            =
            σ.act (τ ⧺ dst ⧺ Tele.ofList υ)
              (κ.act (Tele.ofList υ)
                (.ap
                  ((Proper.inr (pre ⧺ dom))
                    ((Proper.inl (τ ⧺ src)) ((Proper.inl τ) xτ)))
                  args))
          rw [Subst.act_ap_inr σ ((τ ⧺ src) ⧺ Tele.ofList υ)
            ((Proper.inl (τ ⧺ src)) ((Proper.inl τ) xτ)) args]
          rw [Proper.extendList_inr_inl (τ ⧺ src) υ (pre ⧺ cod)
            ((Proper.inl τ) xτ)]
          rw [target.hSrc_inr_tau (pre ⧺ cod) xτ]
          change (Diamond.acted σ target κ).act (Tele.ofList υ)
              (.ap
                ((Proper.inl ((pre ⧺ cod ⧺ τ) ⧺ src))
                  ((Proper.inl (pre ⧺ cod ⧺ τ))
                    ((Proper.inr (pre ⧺ cod)) xτ)))
                (fun j => σ.act (τ ⧺ src ⧺ Tele.ofList υ ∷ j.arity) (args j)))
            =
            σ.act (τ ⧺ dst ⧺ Tele.ofList υ)
              (κ.act (Tele.ofList υ)
                (.ap
                  ((Proper.inr (pre ⧺ dom))
                    ((Proper.inl (τ ⧺ src)) ((Proper.inl τ) xτ)))
                  args))
          rw [Subst.act_ap_inl_pre (Diamond.acted σ target κ) (Tele.ofList υ)
            ((Proper.inr (pre ⧺ cod)) xτ)
            (fun j => σ.act (τ ⧺ src ⧺ Tele.ofList υ ∷ j.arity) (args j))]
          rw [Proper.extendList_inr_inl (τ ⧺ src) υ (pre ⧺ dom)
            ((Proper.inl τ) xτ)]
          rw [target.hSrc_inr_tau (pre ⧺ dom) xτ]
          change .ap
              ((Proper.inl (pre ⧺ cod ⧺ τ ⧺ dst))
                ((Proper.inl (pre ⧺ cod ⧺ τ))
                  ((Proper.inr (pre ⧺ cod)) xτ)))
              (fun i => (Diamond.acted σ target κ).act (Tele.ofList υ ∷ i.arity)
                (σ.act (τ ⧺ src ⧺ Tele.ofList υ ∷ i.arity) (args i)))
            =
            σ.act (τ ⧺ dst ⧺ Tele.ofList υ)
              (κ.act (Tele.ofList υ)
                (.ap
                  ((Proper.inl ((pre ⧺ dom ⧺ τ) ⧺ src))
                    ((Proper.inl (pre ⧺ dom ⧺ τ))
                      ((Proper.inr (pre ⧺ dom)) xτ)))
                  args))
          rw [Subst.act_ap_inl_pre κ (Tele.ofList υ)
            ((Proper.inr (pre ⧺ dom)) xτ) args]
          unfold Subst.weakenCod
          have hτdom :
              ((Proper.inl (pre ⧺ dom ⧺ τ)) ((Proper.inr (pre ⧺ dom)) xτ)) =
              ((Proper.inr (pre ⧺ dom)) ((Proper.inl τ) xτ))
              := (target.hDst_inr_tau (pre ⧺ dom) xτ).symm
          rw [hτdom]
          change .ap
              ((Proper.inl (pre ⧺ cod ⧺ τ ⧺ dst))
                ((Proper.inl (pre ⧺ cod ⧺ τ))
                  ((Proper.inr (pre ⧺ cod)) xτ)))
              (fun i => (Diamond.acted σ target κ).act (Tele.ofList υ ∷ i.arity)
                (σ.act (τ ⧺ src ⧺ Tele.ofList υ ∷ i.arity) (args i)))
            =
            σ.act (τ ⧺ dst ⧺ Tele.ofList υ)
              (.ap
                ((Proper.inl (pre ⧺ dom ⧺ (τ ⧺ dst)))
                  ((Proper.inr (pre ⧺ dom)) ((Proper.inl τ) xτ)))
                (fun i => κ.act (Tele.ofList υ ∷ i.arity) (args i)))
          rw [← Proper.extendList_inr_inl (τ ⧺ dst) υ (pre ⧺ dom)
            ((Proper.inl τ) xτ)]
          rw [Subst.act_ap_inr σ ((τ ⧺ dst) ⧺ Tele.ofList υ)
            ((Proper.inl (τ ⧺ dst)) ((Proper.inl τ) xτ))
            (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))]
          rw [Proper.extendList_inr_inl (τ ⧺ dst) υ (pre ⧺ cod)
            ((Proper.inl τ) xτ)]
          rw [target.hDst_inr_tau (pre ⧺ cod) xτ]
          congr 1
          funext j
          exact hargs j
      | dom z =>
          refine (congrArg ((Diamond.acted σ target κ).act (Tele.ofList υ))
            (Subst.act_ap_inl_dom σ
              ((τ ⧺ src) ⧺ Tele.ofList υ) z args)).trans ?_
          let η : (j : C.Binder β) →
              Expr (((pre ⧺ cod ⧺ τ) ⧺ src) ⧺ Tele.ofList υ ∷ j.arity) :=
            fun j => σ.act (τ ⧺ src ⧺ Tele.ofList υ ∷ j.arity) (args j)
          refine (liftAt target (Diamond.acted σ target κ) [] η (σ z)).trans ?_
          let ζ₀ : ∀ {δ : C.Arity}, ⌊β⌋ ∋ δ →
              Expr ((pre ⧺ cod) ⧺
                ((τ ⧺ dst) ⧺ Tele.ofList υ) ∷ δ) :=
            fun q => match q with
            | .here j =>
                (Diamond.acted σ target κ).act (Tele.ofList υ ∷ j.arity)
                  (σ.act (τ ⧺ src ⧺ Tele.ofList υ ∷ j.arity)
                    (args j))
          let ζ₁ : ∀ {δ : C.Arity}, ⌊β⌋ ∋ δ →
              Expr ((pre ⧺ cod) ⧺
                ((τ ⧺ dst) ⧺ Tele.ofList υ) ∷ δ) :=
            fun q => match q with
            | .here j =>
                σ.act (τ ⧺ dst ⧺ Tele.ofList υ ∷ j.arity)
                  (κ.act (Tele.ofList υ ∷ j.arity) (args j))
          have hζ :
              (fun {δ : C.Arity} (q : ⌊β⌋ ∋ δ) => ζ₀ q)
                =
              (fun {δ : C.Arity} (q : ⌊β⌋ ∋ δ) => ζ₁ q) := by
            funext δ q
            cases q with
            | here j => exact hargs j
            | there q => nomatch q
          change ⟦Subst.inst (C := C) (pre := pre ⧺ cod)
                (dom := ⌊β⌋)
                (cod := (τ ⧺ dst) ⧺ Tele.ofList υ)
                ζ₀⟧ˢ (σ z)
              =
              σ.act (τ ⧺ dst ⧺ Tele.ofList υ)
                (κ.act (Tele.ofList υ)
                  (.ap
                    (((Proper.inl (pre ⧺ dom)) :
                        (pre ⧺ dom) →ʳ
                          (pre ⧺ dom) ⧺ ((τ ⧺ src) ⧺ Tele.ofList υ))
                      ((Proper.inr pre) z))
                    args))
          rw [hζ]
          have hκ :
              κ.act (Tele.ofList υ)
                (.ap
                  (((Proper.inl (pre ⧺ dom)) :
                      (pre ⧺ dom) →ʳ
                        (pre ⧺ dom) ⧺ ((τ ⧺ src) ⧺ Tele.ofList υ))
                    ((Proper.inr pre) z))
                  args)
              =
              .ap
                ((Proper.inl ((pre ⧺ dom ⧺ τ) ⧺ dst))
                  ((Proper.inl (pre ⧺ dom ⧺ τ))
                    ((Proper.inl (pre ⧺ dom))
                      ((Proper.inr pre) z))))
                (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j)) := by
            rw [Proper.extendList_inl
              (τ ⧺ src) υ (pre ⧺ dom) ((Proper.inr pre) z)]
            rw [target.hSrc_inl (pre ⧺ dom) ((Proper.inr pre) z)]
            exact Subst.act_ap_inl_pre κ (Tele.ofList υ)
              ((Proper.inl (pre ⧺ dom))
                ((Proper.inr pre) z)) args
          refine Eq.trans ?_
            (congrArg (σ.act ((τ ⧺ dst) ⧺ Tele.ofList υ)) hκ).symm
          rw [← target.hDst_inl (pre ⧺ dom) ((Proper.inr pre) z)]
          change ⟦Subst.inst (C := C) (pre := pre ⧺ cod)
                (dom := ⌊β⌋)
                (cod := (τ ⧺ dst) ⧺ Tele.ofList υ)
                ζ₁⟧ˢ (σ z)
              =
              σ.act (τ ⧺ dst ⧺ Tele.ofList υ)
                (.ap
                  ((Proper.inl
                      (pre ⧺ dom ⧺ (τ ⧺ dst)))
                    (((Proper.inl (pre ⧺ dom)) :
                        (pre ⧺ dom) →ʳ
                          pre ⧺ dom ⧺ (τ ⧺ dst))
                      ((Proper.inr pre) z)))
                  (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j)))
          rw [← Proper.extendList_inl
            (τ ⧺ dst) υ (pre ⧺ dom)
            ((Proper.inr pre) z)]
          exact (Subst.act_ap_inl_dom σ
            ((τ ⧺ dst) ⧺ Tele.ofList υ) z
            (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))).symm
      | pre z =>
          change (Diamond.acted σ target κ).act (Tele.ofList υ)
              (σ.act (τ ⧺ src ⧺ Tele.ofList υ)
                (.ap
                  (((Proper.inl (pre ⧺ dom)) :
                    (pre ⧺ dom) →ʳ
                      (pre ⧺ dom) ⧺ ((τ ⧺ src) ⧺ Tele.ofList υ))
                    ((Proper.inl pre) z))
                  args))
            =
            σ.act (τ ⧺ dst ⧺ Tele.ofList υ)
              (κ.act (Tele.ofList υ)
                (.ap
                  (((Proper.inl (pre ⧺ dom)) :
                    (pre ⧺ dom) →ʳ
                      (pre ⧺ dom) ⧺ ((τ ⧺ src) ⧺ Tele.ofList υ))
                    ((Proper.inl pre) z))
                  args))
          rw [Subst.act_ap_inl_pre σ ((τ ⧺ src) ⧺ Tele.ofList υ) z args]
          unfold Subst.weakenCod
          rw [Proper.extendList_inl (τ ⧺ src) υ (pre ⧺ cod)
            ((Proper.inl pre) z)]
          rw [target.hSrc_inl (pre ⧺ cod) ((Proper.inl pre) z)]
          change (Diamond.acted σ target κ).act (Tele.ofList υ)
              (.ap
                ((Proper.inl ((pre ⧺ cod ⧺ τ) ⧺ src))
                  ((Proper.inl (pre ⧺ cod ⧺ τ))
                    ((Proper.inl (pre ⧺ cod)) ((Proper.inl pre) z))))
                (fun j => σ.act (τ ⧺ src ⧺ Tele.ofList υ ∷ j.arity) (args j)))
            =
            σ.act (τ ⧺ dst ⧺ Tele.ofList υ)
              (κ.act (Tele.ofList υ)
                (.ap
                  (((Proper.inl (pre ⧺ dom)) :
                    (pre ⧺ dom) →ʳ
                      (pre ⧺ dom) ⧺ ((τ ⧺ src) ⧺ Tele.ofList υ))
                    ((Proper.inl pre) z))
                  args))
          rw [Subst.act_ap_inl_pre (Diamond.acted σ target κ) (Tele.ofList υ)
            ((Proper.inl (pre ⧺ cod)) ((Proper.inl pre) z))
            (fun j => σ.act (τ ⧺ src ⧺ Tele.ofList υ ∷ j.arity) (args j))]
          rw [Proper.extendList_inl (τ ⧺ src) υ (pre ⧺ dom)
            ((Proper.inl pre) z)]
          rw [target.hSrc_inl (pre ⧺ dom) ((Proper.inl pre) z)]
          change .ap
              ((Proper.inl (pre ⧺ cod ⧺ τ ⧺ dst))
                ((Proper.inl (pre ⧺ cod ⧺ τ))
                  ((Proper.inl (pre ⧺ cod)) ((Proper.inl pre) z))))
              (fun i => (Diamond.acted σ target κ).act (Tele.ofList υ ∷ i.arity)
                (σ.act (τ ⧺ src ⧺ Tele.ofList υ ∷ i.arity) (args i)))
            =
            σ.act (τ ⧺ dst ⧺ Tele.ofList υ)
              (κ.act (Tele.ofList υ)
                (.ap
                  ((Proper.inl ((pre ⧺ dom ⧺ τ) ⧺ src))
                    ((Proper.inl (pre ⧺ dom ⧺ τ))
                      ((Proper.inl (pre ⧺ dom)) ((Proper.inl pre) z))))
                  args))
          rw [Subst.act_ap_inl_pre κ (Tele.ofList υ)
            ((Proper.inl (pre ⧺ dom)) ((Proper.inl pre) z)) args]
          unfold Subst.weakenCod
          rw [← target.hDst_inl (pre ⧺ dom) ((Proper.inl pre) z)]
          change .ap
              ((Proper.inl (pre ⧺ cod ⧺ τ ⧺ dst))
                ((Proper.inl (pre ⧺ cod ⧺ τ))
                  ((Proper.inl (pre ⧺ cod)) ((Proper.inl pre) z))))
              (fun i => (Diamond.acted σ target κ).act (Tele.ofList υ ∷ i.arity)
                (σ.act (τ ⧺ src ⧺ Tele.ofList υ ∷ i.arity) (args i)))
            =
            σ.act (τ ⧺ dst ⧺ Tele.ofList υ)
              (.ap
                ((Proper.inl (pre ⧺ dom ⧺ (τ ⧺ dst)))
                  ((Proper.inl (pre ⧺ dom)) ((Proper.inl pre) z)))
                (fun i => κ.act (Tele.ofList υ ∷ i.arity) (args i)))
          rw [← Proper.extendList_inl (τ ⧺ dst) υ (pre ⧺ dom)
            ((Proper.inl pre) z)]
          rw [Subst.act_ap_inl_pre σ ((τ ⧺ dst) ⧺ Tele.ofList υ) z
            (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))]
          unfold Subst.weakenCod
          rw [Proper.extendList_inl (τ ⧺ dst) υ (pre ⧺ cod)
            ((Proper.inl pre) z)]
          rw [target.hDst_inl (pre ⧺ cod) ((Proper.inl pre) z)]
          congr 1
          funext j
          exact hargs j
termination_by
  ((⟨⟨dom.toList⟩, ⟨src.toList⟩⟩ : InterchangeFuel C),
    (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ))
decreasing_by
  all_goals
    subst_vars
    first
      | refine Prod.Lex.left _ _ (InterchangeFuel.Lt.right ?_)
        obtain ⟨γ, hmem, hsub⟩ := SlotAt.subWitness xsrc
        exact DomLt.step γ hmem _ hsub
      | refine Prod.Lex.left _ _ (InterchangeFuel.Lt.left ?_)
        obtain ⟨γ, hmem, hsub⟩ := SlotAt.subWitness z
        exact DomLt.step γ hmem _ hsub
      | refine Prod.Lex.right _ ?_
        exact Expr.Subterm.of_arg_ofList_cons υ _ _ _

private theorem liftAt
    {C : Carrier} {pre τ src dst : Shape C}
    [Proper τ] [Proper src] [Proper dst]
    {υ : List C.Arity}
    (target : TargetProper τ src dst υ)
    (κ : Subst C (pre ⧺ τ) src dst)
    {β : C.Arity} (χ : List C.Arity)
    (η : (j : C.Binder β) →
      Expr (((pre ⧺ τ) ⧺ src) ⧺ Tele.ofList υ ∷ j.arity))
    (e : Expr ((pre ∷ β) ⧺ Tele.ofList χ)) :
    Lift.sequential target κ χ η e = Lift.fused target κ χ η e := by
  letI : Proper τ := target.hτ
  letI : Proper src := target.hSrcShape
  letI : Proper dst := target.hDstShape
  letI : Proper (τ ⧺ src) := target.hSrc
  letI : Proper (τ ⧺ dst) := target.hDst
  letI : Proper ((τ ⧺ src) ⧺ Tele.ofList υ) := target.hSrcUnder
  letI : Proper ((τ ⧺ dst) ⧺ Tele.ofList υ) := target.hDstUnder
  let lam : Subst C pre ⌊β⌋ ((τ ⧺ src) ⧺ Tele.ofList υ) :=
    instOne β ((τ ⧺ src) ⧺ Tele.ofList υ) η
  let lam' : Subst C pre ⌊β⌋ ((τ ⧺ dst) ⧺ Tele.ofList υ) :=
    instOne β ((τ ⧺ dst) ⧺ Tele.ofList υ)
      (fun j => κ.act (Tele.ofList υ ∷ j.arity) (η j))
  change κ.act ((Tele.ofList υ) ⧺ Tele.ofList χ)
      (lam.act (Tele.ofList χ) e)
    =
    lam'.act (Tele.ofList χ) e
  match e with
  | .ap (α := γ) head args =>
      have ih_args : ∀ (j : C.Binder γ),
          Lift.sequential target κ (j.arity :: χ) η (args j)
            =
          Lift.fused target κ (j.arity :: χ) η (args j) :=
        fun j => liftAt target κ (j.arity :: χ) η (args j)
      obtain ⟨site, h_site⟩ :=
        LiftSite.cover (pre := pre) (β := β) (χ := χ) head
      subst h_site
      cases site with
      | under xχ =>
          refine (congrArg
            (κ.act ((Tele.ofList υ) ⧺ Tele.ofList χ))
            (Subst.act_ap_inr lam (Tele.ofList χ) xχ args)).trans ?_
          change κ.act ((Tele.ofList υ) ⧺ Tele.ofList χ)
              (.ap
                ((Proper.inr (((pre ⧺ τ) ⧺ src) ⧺ Tele.ofList υ)) xχ)
                (fun j => lam.act (Tele.ofList χ ∷ j.arity) (args j)))
            =
            lam'.act (Tele.ofList χ)
              (.ap ((Proper.inr (pre ∷ β)) xχ) args)
          rw [← Proper.extendList_inr_inr
            (Tele.ofList υ) χ ((pre ⧺ τ) ⧺ src) xχ]
          refine (Subst.act_ap_inr κ
            ((Tele.ofList υ) ⧺ Tele.ofList χ)
            ((Proper.inr (Tele.ofList υ)) xχ)
            (fun j => lam.act (Tele.ofList χ ∷ j.arity) (args j))).trans ?_
          change .ap
              ((Proper.inr ((pre ⧺ τ) ⧺ dst))
                ((Proper.inr (Tele.ofList υ)) xχ))
              (fun j =>
                κ.act (((Tele.ofList υ) ⧺ Tele.ofList χ) ∷ j.arity)
                  (lam.act (Tele.ofList χ ∷ j.arity) (args j)))
            =
            lam'.act (Tele.ofList χ)
              (.ap ((Proper.inr (pre ∷ β)) xχ) args)
          rw [Proper.extendList_inr_inr
            (Tele.ofList υ) χ ((pre ⧺ τ) ⧺ dst) xχ]
          refine Eq.trans ?_
            (Subst.act_ap_inr lam' (Tele.ofList χ) xχ args).symm
          congr 1
          funext j
          exact ih_args j
      | beta j =>
          refine (congrArg
            (κ.act ((Tele.ofList υ) ⧺ Tele.ofList χ))
            (Subst.act_ap_inl_dom lam (Tele.ofList χ)
              (.here j) args)).trans ?_
          let θ : ∀ {δ : C.Arity}, (⌊j.arity⌋) ∋ δ →
              Expr ((pre ⧺ τ) ⧺ src ⧺
                (Tele.ofList υ) ⧺ Tele.ofList χ ∷ δ) :=
            fun q => match q with
            | .here k => lam.act (Tele.ofList χ ∷ k.arity) (args k)
          let θ' : ∀ {δ : C.Arity}, (⌊j.arity⌋) ∋ δ →
              Expr ((pre ⧺ τ ⧺ dst) ⧺
                (Tele.ofList υ) ⧺ Tele.ofList χ ∷ δ) :=
            fun q => match q with
            | .here k => lam'.act (Tele.ofList χ ∷ k.arity) (args k)
          have hfill : ∀ (k : C.Binder j.arity),
              κ.act (((Tele.ofList υ) ⧺ Tele.ofList χ) ∷ k.arity)
                  (θ (.here k))
                =
              θ' (.here k) := by
            intro k
            exact ih_args k
          let θSubst : Subst C ((pre ⧺ τ) ⧺ src ⧺ Tele.ofList υ)
              ⌊j.arity⌋ (Tele.ofList χ) :=
            instOne j.arity (Tele.ofList χ)
              (fun k => lam.act (Tele.ofList χ ∷ k.arity) (args k))
          have hrec := diamondAt (pre := pre ⧺ τ) (dom := src)
            (cod := dst) (τ := Tele.ofList υ) (src := ⌊j.arity⌋)
            (dst := Tele.ofList χ) κ (TargetProper.liftBeta υ χ j)
            θSubst (e := η j)
          unfold Diamond.actThenInst Diamond.instThenAct Diamond.acted at hrec
          refine Eq.trans hrec.symm ?_
          have hSubst :
              Subst.inst (C := C) (pre := pre ⧺ τ ⧺ dst ⧺ Tele.ofList υ)
                (dom := ⌊j.arity⌋) (cod := Tele.ofList χ)
                (fun {δ : C.Arity} (q : ⌊j.arity⌋ ∋ δ) =>
                  κ.act (((Tele.ofList υ) ⧺ Tele.ofList χ) ∷ δ)
                    (θSubst.sub q))
              =
              Subst.inst (C := C) (pre := pre ⧺ τ ⧺ dst ⧺ Tele.ofList υ)
                (dom := ⌊j.arity⌋) (cod := Tele.ofList χ)
                (fun {δ : C.Arity} (q : ⌊j.arity⌋ ∋ δ) =>
                  θ' q) := by
            apply congrArg
            funext δ q
            cases q with
            | here k => exact hfill k
            | there q => nomatch q
          rw [hSubst]
          change ⟦Subst.inst ⌊j.arity⌋
                (fun {α : C.Arity} (q : ⌊j.arity⌋ ∋ α) =>
                  match q with
                  | .here i => lam'.act (Tele.ofList χ ∷ i.arity) (args i))⟧ˢ
                (lam'.sub (.here j))
              =
              lam'.act (Tele.ofList χ)
                (.ap
                  ((Proper.inl (pre ⧺ ⌊β⌋))
                    ((Proper.inr pre) (.here j)))
                  args)
          symm
          conv => lhs; unfold Subst.act
          rw [Subst.classifySite_inl_dom]
          simp only
          congr
          funext α q
          cases q with
          | here i => rfl
          | there q => nomatch q
      | pre z =>
          refine (congrArg
            (κ.act ((Tele.ofList υ) ⧺ Tele.ofList χ))
            (Subst.act_ap_inl_pre lam (Tele.ofList χ) z args)).trans ?_
          unfold Subst.weakenCod
          rw [Proper.extendList_inl (τ ⧺ src) υ pre z]
          rw [target.hSrc_inl pre z]
          change κ.act ((Tele.ofList υ) ⧺ Tele.ofList χ)
              (.ap
                ((Proper.inl (((pre ⧺ τ) ⧺ src) ⧺ Tele.ofList υ))
                  ((Proper.inl ((pre ⧺ τ) ⧺ src))
                    ((Proper.inl (pre ⧺ τ))
                      ((Proper.inl pre) z))))
                (fun i => lam.act (Tele.ofList χ ∷ i.arity) (args i)))
            =
            lam'.act (Tele.ofList χ)
              (.ap
                ((Proper.inl (pre ∷ β)) ((Proper.inl pre) z))
                args)
          rw [← Proper.extendList_inl
            (Tele.ofList υ) χ ((pre ⧺ τ) ⧺ src)
            ((Proper.inl (pre ⧺ τ)) ((Proper.inl pre) z))]
          change κ.act ((Tele.ofList υ) ⧺ Tele.ofList χ)
              (.ap
                ((Proper.inl ((pre ⧺ τ) ⧺ src))
                  ((Proper.inl (pre ⧺ τ))
                    ((Proper.inl pre) z)))
                (fun i => lam.act (Tele.ofList χ ∷ i.arity) (args i)))
            =
            lam'.act (Tele.ofList χ)
              (.ap
                ((Proper.inl (pre ∷ β)) ((Proper.inl pre) z))
                args)
          rw [Subst.act_ap_inl_pre κ
            ((Tele.ofList υ) ⧺ Tele.ofList χ)
            ((Proper.inl pre) z)]
          refine Eq.trans ?_
            (Subst.act_ap_inl_pre lam' (Tele.ofList χ) z args).symm
          congr 1
          · unfold Subst.weakenCod
            rw [← target.hDst_inl pre z]
            rw [Proper.extendList_inl
              (τ ⧺ dst) υ pre z]
            change
              ((Proper.inl (pre ⧺ (τ ⧺ dst))) :
                  (pre ⧺ (τ ⧺ dst)) →ʳ
                    (pre ⧺ (τ ⧺ dst)) ⧺
                      ((Tele.ofList υ) ⧺ Tele.ofList χ))
                ((Proper.inl pre) z)
              =
              ((Proper.inl ((pre ⧺ (τ ⧺ dst)) ⧺
                  Tele.ofList υ)) :
                  ((pre ⧺ (τ ⧺ dst)) ⧺ Tele.ofList υ) →ʳ
                    ((pre ⧺ (τ ⧺ dst)) ⧺ Tele.ofList υ) ⧺
                      Tele.ofList χ)
                (((Proper.inl (pre ⧺ (τ ⧺ dst))) :
                    (pre ⧺ (τ ⧺ dst)) →ʳ
                      (pre ⧺ (τ ⧺ dst)) ⧺
                        Tele.ofList υ)
                  ((Proper.inl pre) z))
            rw [← Proper.extendList_inl
              (Tele.ofList υ) χ
              (pre ⧺ (τ ⧺ dst))
              ((Proper.inl pre) z)]
          funext k
          exact ih_args k
termination_by
  ((⟨⟨[β]⟩, ⟨src.toList⟩⟩ : InterchangeFuel C),
    (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ))
decreasing_by
  all_goals
    subst_vars
    first
      | refine Prod.Lex.left _ _ (InterchangeFuel.Lt.left_swap ?_)
        exact DomLt.step β (List.Mem.head _) j.arity ⟨j, rfl⟩
      | refine Prod.Lex.right _ ?_
        exact Expr.Subterm.of_arg_ofList_cons χ _ _ _

end

/-- **`act_comp`** — action by a composite substitution factors into two actions. -/
theorem Subst.act_comp
    {C : Carrier} {pre dom mid cod : Shape C}
    [Proper dom] [Proper mid] [Proper cod]
    (σ : Subst C pre dom mid) (θ : Subst C pre mid cod)
    (τ : Shape C) [Proper τ] (e : Expr (pre ⧺ dom ⧺ τ)) :
  (Subst.comp σ θ).act τ e = θ.act τ (σ.act τ e)
  := by
  match e with
  | .ap (α := β) head args =>
    obtain ⟨site, h_site⟩ := Subst.coverSite (pre := pre) (dom := dom) (τ := τ) head
    subst h_site
    cases site with
    | tau x =>
      refine (Subst.act_ap_inr (Subst.comp σ θ) τ x args).trans ?_
      change
        .ap ((Proper.inr (pre ⧺ cod)) x)
          (fun j => (Subst.comp σ θ).act (τ ∷ j.arity) (args j))
        =
        θ.act τ
          (σ.act τ
            (.ap ((Proper.inr (pre ⧺ dom)) x) args))
      rw [Subst.act_ap_inr σ τ x args]
      rw [Subst.act_ap_inr θ τ x (fun i => σ.act (τ ∷ i.arity) (args i))]
      congr 1
      funext i
      exact Subst.act_comp σ θ (τ ∷ i.arity) (args i)
    | dom y =>
      refine (Subst.act_ap_inl_dom (Subst.comp σ θ) τ y args).trans ?_
      have ih_args : ∀ (i : C.Binder β),
          (Subst.comp σ θ).act (τ ∷ i.arity) (args i)
            =
          θ.act (τ ∷ i.arity)
            (σ.act (τ ∷ i.arity) (args i)) :=
        fun i => Subst.act_comp σ θ (τ ∷ i.arity) (args i)
      rw [show (Subst.comp σ θ).sub y = θ.act ⌊β⌋ (σ y) from rfl]
      simp only [ih_args]
      change
        ⟦Subst.inst ⌊β⌋
          (fun {δ} (q : ⌊β⌋ ∋ δ) => match q with
          | .here i =>
              θ.act (τ ∷ i.arity)
                (σ.act (τ ∷ i.arity) (args i)))⟧ˢ
          (θ.act ⌊β⌋ (σ y))
        =
        θ.act τ
          (σ.act τ
            (.ap
              ((Proper.inl (pre ⧺ dom)) ((Proper.inr pre) y))
              args))
      rw [Subst.act_ap_inl_dom σ τ y args]
      let κβ : Subst C (pre ⧺ mid ⧺ Shape.nil) ⌊β⌋ τ :=
        instOne β τ (fun i => σ.act (τ ∷ i.arity) (args i))
      have h := diamondAt (pre := pre) (dom := mid) (cod := cod)
        (τ := Shape.nil) (src := ⌊β⌋) (dst := τ)
        θ (TargetProper.nil ⌊β⌋ τ []) κβ (e := σ y)
      unfold Diamond.actThenInst Diamond.instThenAct Diamond.acted at h
      unfold actAt at h
      unfold TargetProper.nil TargetProper.hDstExt
        TargetProper.hSrcUnder TargetProper.hDstUnder at h
      unfold κβ at h
      unfold instOne at h
      dsimp only at h
      change
        (Subst.inst (C := C) (pre := pre ⧺ cod)
          (dom := ⌊β⌋) (cod := τ)
          (fun {δ : C.Arity} (q : ⌊β⌋ ∋ δ) =>
            θ.act (τ ∷ δ)
              (match q with
              | .here i => σ.act (τ ∷ i.arity) (args i)))).act
          (Tele.ofList []) (θ.act ⌊β⌋ (σ y))
        =
        θ.act τ
          ((Subst.inst (C := C) (pre := pre ⧺ mid)
            (dom := ⌊β⌋) (cod := τ)
            (fun {δ : C.Arity} (q : ⌊β⌋ ∋ δ) =>
              match q with
              | .here i => σ.act (τ ∷ i.arity) (args i))).act
            (Tele.ofList []) (σ y)) at h
      have hFiller :
          Subst.inst (C := C) (pre := pre ⧺ cod)
            (dom := ⌊β⌋) (cod := τ)
            (fun {δ : C.Arity} (q : ⌊β⌋ ∋ δ) =>
              θ.act (τ ∷ δ)
                (match q with
                | .here i => σ.act (τ ∷ i.arity) (args i)))
          =
          Subst.inst (C := C) (pre := pre ⧺ cod)
            (dom := ⌊β⌋) (cod := τ)
            (fun {δ : C.Arity} (q : ⌊β⌋ ∋ δ) =>
              match q with
              | .here i =>
                  θ.act (τ ∷ i.arity)
                    (σ.act (τ ∷ i.arity) (args i))) := by
        apply congrArg
        funext δ q
        cases q with
        | here i => rfl
        | there q => nomatch q
      rw [hFiller] at h
      change
        ⟦Subst.inst ⌊β⌋
          (fun {δ} (q : ⌊β⌋ ∋ δ) => match q with
          | .here i =>
              θ.act (τ ∷ i.arity)
                (σ.act (τ ∷ i.arity) (args i)))⟧ˢ
          (θ.act ⌊β⌋ (σ y))
        =
        θ.act τ
          (⟦Subst.inst ⌊β⌋
            (fun {δ} (q : ⌊β⌋ ∋ δ) => match q with
            | .here i => σ.act (τ ∷ i.arity) (args i))⟧ˢ
            (σ y)) at h
      exact h
    | pre z =>
      refine (Subst.act_ap_inl_pre (Subst.comp σ θ) τ z args).trans ?_
      change
        .ap ((Proper.inl (pre ⧺ cod)) ((Subst.comp σ θ).weakenCod z))
          (fun i => (Subst.comp σ θ).act (τ ∷ i.arity) (args i))
        =
        θ.act τ
          (σ.act τ
            (.ap
              ((Proper.inl (pre ⧺ dom)) ((Proper.inl pre) z))
              args))
      rw [Subst.act_ap_inl_pre σ τ z args]
      unfold Subst.weakenCod
      rw [Subst.act_ap_inl_pre θ τ z (fun i => σ.act (τ ∷ i.arity) (args i))]
      congr 1
      funext i
      exact Subst.act_comp σ θ (τ ∷ i.arity) (args i)
termination_by (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg head args _

/-- **`act_kcomp`** — Kleisli composition factors through `Subst.act_comp`. -/
theorem Subst.act_kcomp
    {C : Carrier} {Γ Δ Ξ : Shape C} [Proper Γ] [Proper Δ] [Proper Ξ]
    (f : ∀ {β}, Γ ∋ β → Expr (Δ ∷ β))
    (g : ∀ {β}, Δ ∋ β → Expr (Ξ ∷ β))
    (τ : Shape C) [Proper τ] (e : Expr (Γ ⧺ τ)) :
  (toSubst (Subst.kcomp f g)).act τ e = (toSubst g).act τ ((toSubst f).act τ e)
  := by
  change (Subst.comp (toSubst f) (toSubst g)).act τ e =
    (toSubst g).act τ ((toSubst f).act τ e)
  exact Subst.act_comp (toSubst f) (toSubst g) τ e
