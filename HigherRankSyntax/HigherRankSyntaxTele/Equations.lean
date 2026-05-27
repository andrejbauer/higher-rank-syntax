import HigherRankSyntaxTele.Subst

/-!
# Equations of the substitution walker

This file holds the auxiliary equations needed to prove the three
relative-monad laws.

## Strategy

`Subst.act`'s body is a long expression with an inline let-bound aux
struct in the dom branch.  Don't `unfold Subst.act` and try to manipulate
the raw body — that exposes the let-aux and rewrites become impossible.

Instead, prove small **computation lemmas** that take `Subst.act` on an
apply with a specific head shape (τ-embedded, τ-weakened) and collapse
the τ-classify dispatch to a clean RHS.  The reflection methods
`ProperTele.classify_embed` / `classify_weaken` are the rewriting handles.

## Three monad laws (clean statements)

* `Subst.act_id` — `(Subst.id Γ).act τ e = e` (unit_right).
* `Subst.act_η` — `(toSubst f).act (Shape.nil ⋈ α) (Expr.η p) = f p` (unit_left).
* `Subst.act_kcomp` — Kleisli composition factors (comp_lift).
-/


/-! ## Computation lemmas — `Subst.act` on a specific apply head -/

/-- Computing `σ.act` on an apply whose head is a τ-embedded shape-slot:
collapses to the τ-slot branch reconstruction. -/
theorem Subst.act_apply_embed {C : Carrier} {pre dom cod : Shape C}
    [ProperTele dom] [ProperTele cod]
    (σ : Subst C pre dom cod) (τ : Shape C) [ProperTele τ]
    {α : C.Arity} (x : τ ∋ α)
    (args : (i : C.Binder α) →
      Expr (pre ⋈* dom ⋈* τ ⋈ i.arity)) :
    σ.act τ (Expr.apply ((ProperTele.embed (pre ⋈* dom)).apply x) args)
      = Expr.apply ((ProperTele.embed (pre ⋈* cod)).apply x)
          (fun j => σ.act (τ ⋈ j.arity) (args j)) := by
  have h := @Subst.act.eq_1 C pre dom cod inferInstance inferInstance σ τ inferInstance α
              ((ProperTele.embed (pre ⋈* dom)).apply x) args
  rw [ProperTele.classify_embed (pre ⋈* dom)] at h
  exact h

/-- Computing `σ.act` on an apply whose head is τ-weakened from a dom-side
slot: collapses to the aux-step in the dom branch. -/
theorem Subst.act_apply_weaken_dom {C : Carrier} {pre dom cod : Shape C}
    [ProperTele dom] [ProperTele cod]
    (σ : Subst C pre dom cod) (τ : Shape C) [ProperTele τ]
    {α : C.Arity} (y : dom ∋ α)
    (args : (i : C.Binder α) →
      Expr (pre ⋈* dom ⋈* τ ⋈ i.arity)) :
    σ.act τ (Expr.apply
              ((ProperTele.weaken (pre ⋈* dom)).apply
                ((ProperTele.embed pre).apply y)) args)
      = (Subst.inst (Shape.nil ⋈ α) (fun q => match q with
            | .here i => σ.act (τ ⋈ i.arity) (args i))).act Shape.nil (σ y) := by
  have h := @Subst.act.eq_1 C pre dom cod inferInstance inferInstance σ τ inferInstance α
              ((ProperTele.weaken (pre ⋈* dom)).apply
                ((ProperTele.embed pre).apply y)) args
  rw [ProperTele.classify_weaken (pre ⋈* dom)] at h
  unfold Subst.classifyDom at h
  rw [ProperTele.classify_embed pre] at h
  exact h

/-- Computing `σ.act` on an apply whose head is τ-weakened from a pre-side
slot: collapses to the rebuild in the pre branch. -/
theorem Subst.act_apply_weaken_pre {C : Carrier} {pre dom cod : Shape C}
    [ProperTele dom] [ProperTele cod]
    (σ : Subst C pre dom cod) (τ : Shape C) [ProperTele τ]
    {α : C.Arity} (z : pre ∋ α)
    (args : (i : C.Binder α) →
      Expr (pre ⋈* dom ⋈* τ ⋈ i.arity)) :
    σ.act τ (Expr.apply
              ((ProperTele.weaken (pre ⋈* dom)).apply
                ((ProperTele.weaken pre).apply z)) args)
      = Expr.apply
          ((ProperTele.weaken (pre ⋈* cod)).apply
            ((Subst.weakenCod σ).apply z))
          (fun i => σ.act (τ ⋈ i.arity) (args i)) := by
  have h := @Subst.act.eq_1 C pre dom cod inferInstance inferInstance σ τ inferInstance α
              ((ProperTele.weaken (pre ⋈* dom)).apply
                ((ProperTele.weaken pre).apply z)) args
  rw [ProperTele.classify_weaken (pre ⋈* dom)] at h
  unfold Subst.classifyDom at h
  rw [ProperTele.classify_weaken pre] at h
  exact h

/-! ## Auxiliary: η-walk on a τ-side slot -/

/-- Walking an η-expansion of a τ-side slot reproduces the η in the target
shape.  By WF recursion on the slot's arity `α`.  Uses `act_apply_embed`
as a black-box computation lemma — no `unfold Subst.act` needed. -/
theorem Subst.act_η_τ {C : Carrier} {pre dom cod : Shape C}
    [ProperTele dom] [ProperTele cod]
    (σ : Subst C pre dom cod) (t : Shape C) [ProperTele t]
    {α : C.Arity} (x : t ∋ α) :
    σ.act (t ⋈ α)
        (Expr.η ((ProperTele.embed (pre ⋈* dom)).apply x))
      = Expr.η ((ProperTele.embed (pre ⋈* cod)).apply x) := by
  rw [Expr.η.eq_1]
  -- `.there ((embed_t Γ).apply x) = ((embed_{t ⋈ α} Γ).apply (.there x))`
  -- by instCons.embed (rfl).  `change` accepts the defeq.
  change σ.act (t ⋈ α)
      (Expr.apply ((ProperTele.embed (pre ⋈* dom)).apply
                     (ListSlotAt.there x))
                  (fun i => Expr.η (ListSlotAt.here i))) = _
  rw [Subst.act_apply_embed σ (t ⋈ α) (ListSlotAt.there x)]
  rw [Expr.η.eq_1]
  congr 1
  funext i
  exact Subst.act_η_τ σ (t ⋈ α)
          (x := @ListSlotAt.here C α t.toList i)
termination_by α
decreasing_by exact ⟨i, rfl⟩

/-! ## Auxiliary: identity instantiation under one binder -/

/-- The identity instantiation for the one-binder telescope `Shape.nil ⋈ α`,
with an arbitrary fixed prefix `Δ`. -/
def Subst.instId {C : Carrier} (Δ : Shape C) (α : C.Arity) :
    Subst C Δ (Shape.nil ⋈ α) (Shape.nil ⋈ α) :=
  Subst.inst (Shape.nil ⋈ α) (fun q => match q with
    | .here i => Expr.η (.here i))

private def Subst.InstEtaPreProp {C : Carrier} (α : C.Arity) : Prop :=
  ∀ {pre cod : Shape C} [ProperTele cod]
    (ι : ∀ {β : C.Arity}, (Shape.nil ⋈ α) ∋ β →
      Expr (pre ⋈* cod ⋈ β))
    (p : pre ∋ α),
    (Subst.inst (Shape.nil ⋈ α) ι).act Shape.nil (Expr.η p)
      =
    Expr.apply ((ProperTele.weaken pre).apply p)
      (fun i => ι (ListSlotAt.here i))

private def Subst.InstIdProp {C : Carrier} (α : C.Arity) : Prop :=
  ∀ (Δ : Shape C) (τ : Shape C) [ProperTele τ]
    (e : Expr ((Δ ⋈ α) ⋈* τ)),
    (Subst.instId Δ α).act τ e = e

/-- Identity instantiation, assuming the β-for-η lemma for the immediate
sub-arities of the head arity.  The proof itself recurses only over the
expression being walked. -/
private theorem Subst.act_inst_id_of {C : Carrier} (α : C.Arity) (Δ : Shape C)
    (hη : ∀ (i : C.Binder α), Subst.InstEtaPreProp i.arity) :
    ∀ (τ : Shape C) [ProperTele τ] (e : Expr ((Δ ⋈ α) ⋈* τ)),
      (Subst.instId Δ α).act τ e = e
  | τ, _, Expr.apply (α := β) head argFam => by
      have ih_all : ∀ (k : C.Binder β),
          (Subst.instId Δ α).act (τ ⋈ k.arity) (argFam k) = argFam k :=
        fun k => Subst.act_inst_id_of α Δ hη (τ ⋈ k.arity) (argFam k)
      rcases ProperTele.cover (Δ ⋈ α) head with ⟨y, h_y⟩ | ⟨y, h_y⟩
      · subst h_y
        refine (Subst.act_apply_embed (Subst.instId Δ α) τ y argFam).trans ?_
        congr
        funext k
        exact ih_all k
      · subst h_y
        rcases ProperTele.cover Δ y with ⟨z, h_z⟩ | ⟨z, h_z⟩
        · subst h_z
          cases z with
          | here i =>
              refine (Subst.act_apply_weaken_dom
                (Subst.instId Δ α) τ (ListSlotAt.here i) argFam).trans ?_
              rw [show (Subst.instId Δ α).sub (ListSlotAt.here i)
                    = @Expr.η C (Δ ⋈ α) i.arity (ListSlotAt.here i) from rfl]
              refine (hη i (pre := Δ ⋈ α) (cod := τ)
                (ι := _) (p := ListSlotAt.here i)).trans ?_
              change
                Expr.apply ((ProperTele.weaken (Δ ⋈ α)).apply
                    (ListSlotAt.here i))
                  (fun k => (Subst.instId Δ α).act (τ ⋈ k.arity) (argFam k))
                =
                Expr.apply ((ProperTele.weaken (Δ ⋈ α)).apply
                    (ListSlotAt.here i)) argFam
              congr 1
              funext k
              exact ih_all k
          | there z' => nomatch z'
        · subst h_z
          refine (Subst.act_apply_weaken_pre (Subst.instId Δ α) τ z argFam).trans ?_
          change
            Expr.apply ((ProperTele.weaken (Δ ⋈ α)).apply
                ((ProperTele.weaken Δ).apply z))
              (fun k => (Subst.instId Δ α).act (τ ⋈ k.arity) (argFam k))
            =
            Expr.apply ((ProperTele.weaken (Δ ⋈ α)).apply
                ((ProperTele.weaken Δ).apply z)) argFam
          congr 1
          funext k
          exact ih_all k
termination_by τ _ e => (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg head argFam _

/-- The identity-instantiation and β-for-η instantiation lemmas are proved
together by well-founded recursion on arities. -/
private theorem Subst.act_inst_bundle {C : Carrier} (α : C.Arity) :
    Subst.InstEtaPreProp α ∧ Subst.InstIdProp α := by
  refine ⟨?eta_pre, ?inst_id⟩
  · intro pre cod _ ι p
    rw [Expr.η.eq_1]
    change (Subst.inst (Shape.nil ⋈ α) ι).act Shape.nil
        (Expr.apply ((ProperTele.weaken (pre ⋈* (Shape.nil ⋈ α))).apply
          ((ProperTele.weaken pre).apply p)) (fun i => Expr.η (ListSlotAt.here i))) = _
    rw [Subst.act_apply_weaken_pre]
    change
      Expr.apply ((Subst.inst (Shape.nil ⋈ α) ι).weakenCod.apply p)
        (fun i => (Subst.inst (Shape.nil ⋈ α) ι).act
          (Shape.nil ⋈ i.arity) (Expr.η (ListSlotAt.here i)))
      =
      Expr.apply ((ProperTele.weaken pre).apply p)
        (fun i => ι (ListSlotAt.here i))
    change
      Expr.apply ((ProperTele.weaken pre).apply p)
        (fun i => (Subst.inst (Shape.nil ⋈ α) ι).act
          (Shape.nil ⋈ i.arity) (Expr.η (ListSlotAt.here i)))
      =
      Expr.apply ((ProperTele.weaken pre).apply p)
        (fun i => ι (ListSlotAt.here i))
    congr
    funext i
    rw [Expr.η.eq_1]
    change (Subst.inst (Shape.nil ⋈ α) ι).act (Shape.nil ⋈ i.arity)
        (Expr.apply ((ProperTele.weaken (pre ⋈* (Shape.nil ⋈ α))).apply
          ((ProperTele.embed pre).apply (ListSlotAt.here i)))
          (fun k =>
            @Expr.η C
              ((pre ⋈* (Shape.nil ⋈ α)) ⋈* (Shape.nil ⋈ i.arity))
              k.arity (ListSlotAt.here k))) = _
    rw [Subst.act_apply_weaken_dom]
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
      exact Subst.act_η_τ (Subst.inst (Shape.nil ⋈ α) ι)
        (Shape.nil ⋈ i.arity) (x := ListSlotAt.here k)
    simp only [hfill]
    change (Subst.instId (pre ⋈* cod) i.arity).act Shape.nil
      (ι (ListSlotAt.here i)) = ι (ListSlotAt.here i)
    exact (Subst.act_inst_bundle i.arity).2 (pre ⋈* cod) Shape.nil
      (ι (ListSlotAt.here i))
  · intro Δ τ _ e
    exact Subst.act_inst_id_of α Δ
      (fun i => (Subst.act_inst_bundle i.arity).1) τ e
termination_by α
decreasing_by
  all_goals exact ⟨i, rfl⟩

/-- β-for-η for a one-binder instantiation. -/
theorem Subst.act_inst_η_pre {C : Carrier} {pre cod : Shape C} [ProperTele cod]
    {α : C.Arity}
    (ι : ∀ {β : C.Arity}, (Shape.nil ⋈ α) ∋ β →
      Expr (pre ⋈* cod ⋈ β))
    (p : pre ∋ α) :
    (Subst.inst (Shape.nil ⋈ α) ι).act Shape.nil (Expr.η p)
      =
    Expr.apply ((ProperTele.weaken pre).apply p)
      (fun i => ι (ListSlotAt.here i)) :=
  (Subst.act_inst_bundle α).1 ι p

/-- Identity instantiation acts as the identity walker. -/
theorem Subst.act_inst_id {C : Carrier} (α : C.Arity) (Δ : Shape C) :
    ∀ (τ : Shape C) [ProperTele τ] (e : Expr ((Δ ⋈ α) ⋈* τ)),
      (Subst.instId Δ α).act τ e = e :=
  (Subst.act_inst_bundle α).2 Δ

/-! ## Monad laws -/

/-- **`act_id`** — the identity substitution acts as the identity walker.
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
      refine (Subst.act_apply_embed (Subst.id Γ) τ y args).trans ?_
      congr ; funext k ; apply Subst.act_id
    · -- head = weaken y; y : Γ ∋ β.  Cover y at base Shape.nil:
      -- weaken-from-nil is empty, so y is necessarily embed-image.
      subst h_y
      rcases ProperTele.cover Shape.nil y with ⟨y, h_q⟩ | ⟨z, _⟩
      · subst h_q
        refine (Subst.act_apply_weaken_dom (Subst.id Γ) τ y args).trans ?_
        -- Simplify (Subst.id Γ) y = Expr.η y (rfl via toSubst_sub).
        show (Subst.inst (Shape.nil ⋈ β) (fun q => match q with
              | .here k => (Subst.id Γ).act (τ ⋈ k.arity) (args k))).act Shape.nil
              (Expr.η y) = _
        -- IH on each inner walk:
        have h_args : ∀ (k : C.Binder β),
            (Subst.id Γ).act (τ ⋈ k.arity) (args k) = args k :=
          fun k => Subst.act_id Γ (τ ⋈ k.arity) (args k)
        -- Simplify (embed Shape.nil).apply y = y on the RHS.
        rw [ProperTele.embed_nil_id y]
        refine (Subst.act_inst_η_pre
          (pre := Γ) (cod := τ) (α := β) (ι := _) (p := y)).trans ?_
        change
          Expr.apply ((ProperTele.weaken Γ).apply y)
            (fun k => (Subst.id Γ).act (τ ⋈ k.arity) (args k))
          =
          Expr.apply ((ProperTele.weaken Γ).apply y) args
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
        (Expr.apply ((ProperTele.weaken (Shape.nil ⋈* Γ)).apply
                      ((ProperTele.embed Shape.nil).apply y))
                    (fun i => Expr.η (ListSlotAt.here i))) = _
    rw [Subst.act_apply_weaken_dom (toSubst f) (Shape.nil ⋈ α) y]
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
      exact Subst.act_η_τ (toSubst f) (Shape.nil ⋈ α)
        (x := ListSlotAt.here i)
    simp only [hfill]
    rw [toSubst_sub]
    rw [ProperTele.embed_nil_id y]
    change (Subst.instId Δ α).act Shape.nil (f y) = f y
    exact Subst.act_inst_id α Δ Shape.nil (f y)
  · exact nomatch z

private theorem Subst.act_inst_interchange {C : Carrier}
    {pre dom cod τ : Shape C} [ProperTele dom] [ProperTele cod] [ProperTele τ]
    (σ : Subst C pre dom cod)
    {α : C.Arity}
    (ι : ∀ {β : C.Arity}, (Shape.nil ⋈ α) ∋ β →
      Expr (pre ⋈* dom ⋈* τ ⋈ β))
    (υ : Shape C) [ProperTele υ]
    (e : Expr (pre ⋈* dom ⋈* (Shape.nil ⋈ α) ⋈* υ)) :
    letI : ProperTele ((Shape.nil ⋈ α) ⋈* υ) :=
      ProperTele.compose (Shape.nil ⋈ α) υ
    letI : ProperTele (τ ⋈* υ) :=
      ProperTele.compose τ υ
    (Subst.inst (Shape.nil ⋈ α) (fun q => match q with
      | .here i => σ.act (τ ⋈ i.arity) (ι (ListSlotAt.here i)))).act
        υ (σ.act ((Shape.nil ⋈ α) ⋈* υ) e)
      =
    σ.act (τ ⋈* υ)
      ((Subst.inst (Shape.nil ⋈ α) ι).act υ e) := by
  sorry

private theorem Subst.act_inst_fusion {C : Carrier} {Δ Ε τ : Shape C}
    [ProperTele Δ] [ProperTele Ε] [ProperTele τ]
    (g : ∀ {β : C.Arity}, Δ ∋ β → Expr (Ε ⋈ β))
    {α : C.Arity}
    (ι : ∀ {β : C.Arity}, (Shape.nil ⋈ α) ∋ β →
      Expr (Δ ⋈* τ ⋈ β))
    (e : Expr (Δ ⋈ α)) :
    (Subst.inst (Shape.nil ⋈ α) (fun q => match q with
      | .here i => (toSubst g).act (τ ⋈ i.arity) (ι (ListSlotAt.here i)))).act
        Shape.nil ((toSubst g).act (Shape.nil ⋈ α) e)
      =
    (toSubst g).act τ
      ((Subst.inst (Shape.nil ⋈ α) ι).act Shape.nil e) := by
  exact Subst.act_inst_interchange (toSubst g) ι Shape.nil e

/-- Tau-generalized Kleisli composition equation for the substitution walker. -/
private theorem Subst.act_kcomp_τ {C : Carrier} {Γ Δ Ε : Shape C}
    [ProperTele Γ] [ProperTele Δ] [ProperTele Ε]
    (f : ∀ {β : C.Arity}, Γ ∋ β → Expr (Δ ⋈ β))
    (g : ∀ {β : C.Arity}, Δ ∋ β → Expr (Ε ⋈ β))
    (τ : Shape C) [ProperTele τ]
    (e : Expr (Γ ⋈* τ)) :
    (toSubst (Subst.kcomp f g)).act τ e
      = (toSubst g).act τ ((toSubst f).act τ e) := by
  match e with
  | Expr.apply (α := β) head args =>
    rcases ProperTele.cover Γ head with
      ⟨x, h_x⟩ | ⟨y, h_y⟩
    · subst h_x
      refine (Subst.act_apply_embed (toSubst (Subst.kcomp f g)) τ x args).trans ?_
      change
        Expr.apply ((ProperTele.embed (Shape.nil ⋈* Ε)).apply x)
          (fun j => (toSubst (Subst.kcomp f g)).act (τ ⋈ j.arity) (args j))
        =
        (toSubst g).act τ
          ((toSubst f).act τ
            (Expr.apply ((ProperTele.embed (Shape.nil ⋈* Γ)).apply x) args))
      rw [Subst.act_apply_embed (toSubst f) τ x args]
      rw [Subst.act_apply_embed (toSubst g) τ x
        (fun i => (toSubst f).act (τ ⋈ i.arity) (args i))]
      congr 1
      funext i
      exact Subst.act_kcomp_τ f g (τ ⋈ i.arity) (args i)
    · subst h_y
      rw [← ProperTele.embed_nil_id y]
      refine (Subst.act_apply_weaken_dom
        (toSubst (Subst.kcomp f g)) τ y args).trans ?_
      have ih_args : ∀ (i : C.Binder β),
          (toSubst (Subst.kcomp f g)).act (τ ⋈ i.arity) (args i)
            =
          (toSubst g).act (τ ⋈ i.arity)
            ((toSubst f).act (τ ⋈ i.arity) (args i)) :=
        fun i => Subst.act_kcomp_τ f g (τ ⋈ i.arity) (args i)
      rw [show (toSubst (Subst.kcomp f g)).sub y
            = (toSubst g).act (Shape.nil ⋈ β) (f y) from rfl]
      simp only [ih_args]
      change
        (Subst.inst (Shape.nil ⋈ β)
          (fun {δ} (q : (Shape.nil ⋈ β) ∋ δ) => match q with
          | .here i =>
            (toSubst g).act (τ ⋈ i.arity)
              ((toSubst f).act (τ ⋈ i.arity) (args i)))).act Shape.nil
          ((toSubst g).act (Shape.nil ⋈ β) (f y))
        =
        (toSubst g).act τ
          ((toSubst f).act τ
            (Expr.apply
              ((ProperTele.weaken (Shape.nil ⋈* Γ)).apply
                ((ProperTele.embed Shape.nil).apply y)) args))
      rw [Subst.act_apply_weaken_dom (toSubst f) τ y args]
      exact Subst.act_inst_fusion g
        (τ := τ)
        (ι := fun {δ} (q : (Shape.nil ⋈ β) ∋ δ) => match q with
          | .here i => (toSubst f).act (τ ⋈ i.arity) (args i))
        (e := f y)
termination_by (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg head args _

/-- **`act_kcomp`** — acting via a Kleisli composition factors.
Translates to `lift (g ∘ f) = lift g ∘ lift f` (comp_lift). -/
theorem Subst.act_kcomp {C : Carrier} {Γ Δ Ε : Shape C}
    [ProperTele Γ] [ProperTele Δ] [ProperTele Ε]
    (f : ∀ {β : C.Arity}, Γ ∋ β → Expr (Δ ⋈ β))
    (g : ∀ {β : C.Arity}, Δ ∋ β → Expr (Ε ⋈ β))
    (α : C.Arity) (e : Expr (Γ ⋈ α)) :
    (toSubst (Subst.kcomp f g)).act (Shape.nil ⋈ α) e
      = (toSubst g).act (Shape.nil ⋈ α)
          ((toSubst f).act (Shape.nil ⋈ α) e) := by
  exact Subst.act_kcomp_τ f g (Shape.nil ⋈ α) e
