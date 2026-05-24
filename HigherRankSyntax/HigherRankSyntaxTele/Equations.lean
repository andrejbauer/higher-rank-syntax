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
shape.  By induction on the input expression via `Expr.Subterm` (equivalent
to subWf on the slot's arity, since `Expr.η` terminates by arity). -/
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
Translates to `lift f ∘ η = f` (unit_left). -/
theorem Subst.act_η {C : Carrier} {Γ Δ : Shape C}
    (f : ∀ {β : C.Arity}, (Γ ∋ β) → Expr (Δ ⋈ β))
    (α : C.Arity) (p : Γ ∋ α) :
    (toSubst f).act (CTele.cons α CTele.id) (Expr.η p) = f p := by
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
