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
        simp only [h_args]
        -- Simplify (embed Shape.nil).apply y = y on the RHS.
        rw [ProperTele.embed_nil_id y]
        sorry
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
    sorry
  · exact nomatch z

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
  match e with
  | Expr.apply (α := β) head args =>
    sorry
