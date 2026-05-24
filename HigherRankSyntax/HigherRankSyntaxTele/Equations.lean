import HigherRankSyntaxTele.Subst

/-!
# Equations of the substitution walker

This file holds the auxiliary equations needed to prove the three
relative-monad laws.

## The relative-monad laws, cleanly stated

* **`Subst.act_id`** — `(Subst.id Γ).act τ e = e`.  The identity substitution
  acts as the identity walker.  Translates to `lift η = 𝟙` in the relative
  monad (unit_right).

* **`Subst.act_η`** — `(toSubst f).act (cons α id) (Expr.η p) = f p`.  Acting
  on an η-expansion of a slot reduces to applying `f` to that slot.  This is
  the β-rule of the Kleisli extension: `lift f ∘ η = f` (unit_left).

* **`Subst.act_kcomp`** — `(toSubst (kcomp f g)).act τ e = (toSubst g).act τ
  ((toSubst f).act τ e)`.  Acting via a Kleisli composition factors through
  the two `.act`s.  This is `lift (g ∘ f) = lift g ∘ lift f` (comp_lift).

## Auxiliary equations

The proofs need helper lemmas about how `Subst.act` behaves on
`Expr.η`-shaped inputs at specific slot positions.  The cornerstone:

* **`Subst.act_η_τ`** — walking `Expr.η` of a τ-side slot reproduces the η
  in the target shape.  Used inside `act_η` to characterize the aux Subst's
  `sub` as η-fills, and inside `act_id` (via `identity_walker`) for the
  τ-slot branch of the walker.

`act_η_τ` is proved.  The three monad laws (`act_id`, `act_η`, `act_kcomp`)
are still `sorry`d.
-/


/-! ## Auxiliary: η-walk on a τ-side slot -/

/-- Walking an η-expansion of a τ-side slot reproduces the η in the target
shape.  By WF recursion on the slot's arity `α`, using the same insight as
`act_η`: rewrite the inner slot's `.there` as `(cons α t).embed Γ (.there q_τ)`
so that the propositional reflection `classify_embed` collapses τ.classify
directly to the shape continuation. -/
theorem Subst.act_η_τ {C : Carrier} (σ : Subst C) (t : CTele C)
    {α : C.Arity} (q_τ : t.shape ∋ α) :
    σ.act (CTele.cons α t)
        (Expr.η (t.embed (σ.pre ⋈* σ.dom) q_τ))
      = Expr.η (t.embed (σ.pre ⋈* σ.cod) q_τ) := by
  -- Step 1: unfold the LHS's outer Expr.η.
  rw [Expr.η.eq_1]
  -- Step 2: unfold Subst.act on the resulting .apply.
  unfold Subst.act
  -- Step 3: `change` the slot's form to use the cons.embed instead of `.there`
  -- (these are def-eq via cons_embed_there).  Then classify_embed applies.
  change ((CTele.cons α t).classify (σ.pre ⋈* σ.dom)
            (Expr ((σ.pre ⋈* σ.cod) ⋈* (CTele.cons α t).shape))
            (((CTele.cons α t).embed (σ.pre ⋈* σ.dom)).apply (ListSlotAt.there q_τ))
            _ _) = _
  rw [(CTele.cons α t).classify_embed (σ.pre ⋈* σ.dom)]
  -- Step 4: unfold the RHS's Expr.η.
  rw [Expr.η.eq_1]
  -- Step 5: both sides are Expr.apply.  Heads agree by cons_embed_there
  -- (rfl), so congr 1 collapses to the args.  Args agree by IH on i.arity.
  congr 1
  funext i
  -- IH: act_η_τ at (cons α t, .here i) with α' = i.arity.
  -- (cons α t).embed Γ (.here i) = .here i (cons_embed_here, rfl).
  exact Subst.act_η_τ σ (CTele.cons α t)
          (q_τ := @ListSlotAt.here C α t.shape.toList i)
termination_by α
decreasing_by
  -- i : C.Binder α gives Carrier.Sub i.arity α
  exact ⟨i, rfl⟩

/-! ## Monad laws -/

/-- **`act_id`** — the identity substitution acts as the identity walker.
Translates to `lift η = 𝟙` (unit_right). -/
theorem Subst.act_id {C : Carrier} (Γ : Shape C) (α : C.Arity)
    (e : Expr (Γ ⋈ α)) :
    (Subst.id Γ).act (CTele.cons α CTele.id) e = e := by
  sorry

/-- **`act_η`** — acting on an η-expansion reduces to applying `f`.
Translates to `lift f ∘ η = f` (unit_left).

The proof structure decomposes into three steps:
1. Unfold `Expr.η p = .apply (.there p) (fun i => Expr.η (.here i))` (via
   `Expr.η.eq_1`).
2. Walk the apply through `Subst.act`'s body: `τ.classify_weaken` (since
   `.there p = (cons α id).weaken Γ p`) reduces τ.classify to the
   below-τ continuation with `p_below = p`.  `toSubst`'s `classifyDom`
   then gives `PreOrDom.dom p`.  The dom-branch builds aux and calls
   `aux.act CTele.id (f p)`.
3. Show `aux.act CTele.id (f p) = f p`.  Aux is "canonical identity at
   `Δ ⋈ α`" because `aux.sub (.here i) = Expr.η (.here i)` — discharged
   by `act_η_τ` applied with `t := cons α id`, `q_τ := .here i`.  Then
   an identity-walker lemma closes.

Mechanical Lean encoding deferred — `act_η_τ`'s use site is established. -/
theorem Subst.act_η {C : Carrier} {Γ Δ : Shape C}
    (f : ∀ {β : C.Arity}, (Γ ∋ β) → Expr (Δ ⋈ β))
    (α : C.Arity) (p : Γ ∋ α) :
    (toSubst f).act (CTele.cons α CTele.id) (Expr.η p) = f p := by
  -- Step 1: unfold the outer Expr.η.
  rw [Expr.η.eq_1]
  -- Step 2: unfold Subst.act on the resulting .apply pattern.
  unfold Subst.act
  -- Step 3: reduce the toSubst projections and Tele's left unit.
  simp only [toSubst_pre, toSubst_dom, toSubst_cod, toSubst_classifyDom, toSubst_sub,
             Shape.nil_extList]
  -- Step 4: the slot `.there p` IS `(cons α id).weaken Γ |>.apply p`
  -- (cons_weaken + id_weaken are both `rfl`).  Convert and apply the
  -- propositional reflection `classify_weaken` to collapse the cons-classify
  -- dispatch directly to the below-τ continuation `k_below p`.
  rw [show (ListSlotAt.there p : (Γ ⋈ α) ∋ α) =
        ((CTele.cons α CTele.id).weaken Γ).apply p from rfl]
  rw [(CTele.cons α CTele.id).classify_weaken Γ]
  -- Goal now: `aux.act CTele.id (f p) = f p` for the canonical-identity
  -- aux at shape `Δ ⋈ α`.  Validate `act_η_τ` by exhibiting that
  -- `aux.sub (.here i) = Expr.η (.here i)` — the equation that makes
  -- aux identity-acting.
  have h_aux_sub_eq_η : ∀ (i : C.Binder α),
      (toSubst f).act (CTele.cons i.arity (CTele.cons α CTele.id))
          (@Expr.η C (Γ ⋈ α) i.arity (ListSlotAt.here i))
        = @Expr.η C (Δ ⋈ α) i.arity (ListSlotAt.here i) := by
    intro i
    exact Subst.act_η_τ (toSubst f) (CTele.cons α CTele.id)
            (q_τ := @ListSlotAt.here C α [] i)
  -- Lean accepts `h_aux_sub_eq_η`: `act_η_τ`'s statement is validated.
  -- Remaining: the identity-walker step on aux.  Deferred.
  sorry

/-- **`act_kcomp`** — acting via a Kleisli composition factors.
Translates to `lift (g ∘ f) = lift g ∘ lift f` (comp_lift). -/
theorem Subst.act_kcomp {C : Carrier} {Γ Δ Ε : Shape C}
    (f : ∀ {β : C.Arity}, (Γ ∋ β) → Expr (Δ ⋈ β))
    (g : ∀ {β : C.Arity}, (Δ ∋ β) → Expr (Ε ⋈ β))
    (α : C.Arity) (e : Expr (Γ ⋈ α)) :
    (toSubst (Subst.kcomp f g)).act (CTele.cons α CTele.id) e
      = (toSubst g).act (CTele.cons α CTele.id)
          ((toSubst f).act (CTele.cons α CTele.id) e) := by
  sorry
