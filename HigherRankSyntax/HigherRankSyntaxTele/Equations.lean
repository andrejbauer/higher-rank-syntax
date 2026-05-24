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

Currently all proofs are `sorry`d; we'll test the helper statements by
proving `act_η` first.
-/


/-! ## Auxiliary: η-walk on a τ-side slot -/

/-- Walking an η-expansion of a τ-side slot reproduces the η in the target
shape.

Proof outline:
* Unfold `Expr.η q = .apply (.there q) (fun j => Expr.η (.here j))`.
* Unfold `Subst.act` on the resulting `.apply`.  The τ-classify call is
  `(cons α t).classify Γ X (.there (t.embed Γ q_τ)) k_shape k_below`.
  By cons.classify's `.there` branch it recurses with
  `t.classify Γ X (t.embed Γ q_τ) (λ q_t => k_shape (.there q_t)) k_below`,
  which by `t.classify_embed` reduces to `k_shape (.there q_τ)`.
* The τ-slot branch builds `.apply ((cons α t).embed Δ (.there q_τ))
  (fun j => σ.act (cons j.arity (cons α t)) (Expr.η (.here j)))`.
  `(cons α t).embed Δ (.there q_τ) = .there (t.embed Δ q_τ)` by
  cons.embed's `.there` branch.
* Each recursive call invokes the IH at the smaller arity `j.arity ≺ α`
  via `C.subWf`, with `t' := cons α t` and `q_τ' := .here j`.  Since
  `(cons α t).embed Γ (.here j) = .here j` (cons.embed's `.here` branch),
  the IH gives `σ.act (cons j.arity (cons α t)) (Expr.η (.here j))
  = Expr.η (.here j)` in the target shape.
* Folding back: `.apply (.there (t.embed Δ q_τ)) (fun j => Expr.η (.here j))
  = Expr.η (t.embed Δ q_τ)`. -/
theorem Subst.act_η_τ {C : Carrier} (σ : Subst C) (t : CTele C)
    {α : C.Arity} (q_τ : t.shape ∋ α) :
    σ.act (CTele.cons α t)
        (Expr.η (t.embed (σ.pre ⋈* σ.dom) q_τ))
      = Expr.η (t.embed (σ.pre ⋈* σ.cod) q_τ) := by
  sorry

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
