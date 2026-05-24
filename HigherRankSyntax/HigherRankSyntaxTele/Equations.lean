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
    {α : C.Arity} (q_τ : τ ∋ α)
    (args : (i : C.Binder α) →
      Expr (((pre ⋈* dom) ⋈* τ) ⋈ i.arity)) :
    σ.act τ (Expr.apply ((ProperTele.embed (t := τ) (pre ⋈* dom)).apply q_τ) args)
      = Expr.apply ((ProperTele.embed (t := τ) (pre ⋈* cod)).apply q_τ)
          (fun j => σ.act (τ ⋈ j.arity) (args j)) := by
  have h := @Subst.act.eq_1 C pre dom cod inferInstance inferInstance σ τ inferInstance α
              ((ProperTele.embed (t := τ) (pre ⋈* dom)).apply q_τ) args
  rw [ProperTele.classify_embed (t := τ) (pre ⋈* dom)] at h
  exact h

/-- Computing `σ.act` on an apply whose head is a τ-weakened below-slot:
collapses to the below-τ branch, which dispatches via `σ.classifyDom`. -/
theorem Subst.act_apply_weaken {C : Carrier} {pre dom cod : Shape C}
    [ProperTele dom] [ProperTele cod]
    (σ : Subst C pre dom cod) (τ : Shape C) [ProperTele τ]
    {α : C.Arity} (q : (pre ⋈* dom) ∋ α)
    (args : (i : C.Binder α) →
      Expr (((pre ⋈* dom) ⋈* τ) ⋈ i.arity)) :
    σ.act τ (Expr.apply ((ProperTele.weaken (t := τ) (pre ⋈* dom)).apply q) args)
      = (match σ.classifyDom q with
          | PreOrDom.dom q_dom =>
              let aux : Subst C (pre ⋈* cod) (Shape.nil ⋈ α) τ := {
                sub := fun {_} q' => match q' with
                  | .here i => σ.act (τ ⋈ i.arity) (args i)
              }
              aux.act Shape.nil (σ.sub q_dom)
          | PreOrDom.pre q_pre =>
              Expr.apply
                ((ProperTele.weaken (t := τ) (pre ⋈* cod)).apply
                  ((Subst.weakenCod σ).apply q_pre))
                (fun i => σ.act (τ ⋈ i.arity) (args i))) := by
  have h := @Subst.act.eq_1 C pre dom cod inferInstance inferInstance σ τ inferInstance α
              ((ProperTele.weaken (t := τ) (pre ⋈* dom)).apply q) args
  rw [ProperTele.classify_weaken (t := τ) (pre ⋈* dom)] at h
  exact h

/-! ## Auxiliary: η-walk on a τ-side slot -/

/-- Walking an η-expansion of a τ-side slot reproduces the η in the target
shape.  By WF recursion on the slot's arity `α`.  Uses `act_apply_embed`
as a black-box computation lemma — no `unfold Subst.act` needed. -/
theorem Subst.act_η_τ {C : Carrier} {pre dom cod : Shape C}
    [ProperTele dom] [ProperTele cod]
    (σ : Subst C pre dom cod) (t : Shape C) [ProperTele t]
    {α : C.Arity} (q_τ : t ∋ α) :
    σ.act (t ⋈ α)
        (Expr.η ((ProperTele.embed (t := t) (pre ⋈* dom)).apply q_τ))
      = Expr.η ((ProperTele.embed (t := t) (pre ⋈* cod)).apply q_τ) := by
  rw [Expr.η.eq_1]
  -- `.there ((embed_t Γ).apply q_τ) = ((embed_{t ⋈ α} Γ).apply (.there q_τ))`
  -- by instCons.embed (rfl).  `change` accepts the defeq.
  change σ.act (t ⋈ α)
      (Expr.apply ((ProperTele.embed (t := t ⋈ α) (pre ⋈* dom)).apply
                     (ListSlotAt.there q_τ))
                  (fun i => Expr.η (ListSlotAt.here i))) = _
  rw [Subst.act_apply_embed σ (t ⋈ α) (ListSlotAt.there q_τ)]
  rw [Expr.η.eq_1]
  congr 1
  funext i
  exact Subst.act_η_τ σ (t ⋈ α)
          (q_τ := @ListSlotAt.here C α t.toList i)
termination_by α
decreasing_by exact ⟨i, rfl⟩

/-! ## Monad laws -/

/-- **`act_id`** — the identity substitution acts as the identity walker.
Translates to `lift η = 𝟙` (unit_right). -/
theorem Subst.act_id {C : Carrier} (Γ : Shape C) [ProperTele Γ]
    (α : C.Arity) (e : Expr (Γ ⋈ α)) :
    (Subst.id Γ).act (Shape.nil ⋈ α) e = e := by
  sorry

/-- **`act_η`** — acting on an η-expansion reduces to applying `f`.
Translates to `lift f ∘ η = f` (unit_left). -/
theorem Subst.act_η {C : Carrier} {Γ Δ : Shape C} [ProperTele Γ] [ProperTele Δ]
    (f : ∀ {β : C.Arity}, (Γ ∋ β) → Expr (Δ ⋈ β))
    (α : C.Arity) (p : Γ ∋ α) :
    (toSubst f).act (Shape.nil ⋈ α) (Expr.η p) = f p := by
  sorry

/-- **`act_kcomp`** — acting via a Kleisli composition factors.
Translates to `lift (g ∘ f) = lift g ∘ lift f` (comp_lift). -/
theorem Subst.act_kcomp {C : Carrier} {Γ Δ Ε : Shape C}
    [ProperTele Γ] [ProperTele Δ] [ProperTele Ε]
    (f : ∀ {β : C.Arity}, (Γ ∋ β) → Expr (Δ ⋈ β))
    (g : ∀ {β : C.Arity}, (Δ ∋ β) → Expr (Ε ⋈ β))
    (α : C.Arity) (e : Expr (Γ ⋈ α)) :
    (toSubst (Subst.kcomp f g)).act (Shape.nil ⋈ α) e
      = (toSubst g).act (Shape.nil ⋈ α)
          ((toSubst f).act (Shape.nil ⋈ α) e) := by
  sorry
