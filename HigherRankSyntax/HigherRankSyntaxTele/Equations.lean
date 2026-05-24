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
the τ.classify dispatch to a clean RHS.  The reflection fields
`classify_embed` / `classify_weaken` (on `CTele`) are the rewriting
handles.  Each computation lemma is proved by `unfold Subst.act; rw
[classify_*]; rfl` (a short body), then *used as a black box* in further
proofs.

## Three monad laws (clean statements)

* `Subst.act_id` — `(Subst.id Γ).act τ e = e` (unit_right).
* `Subst.act_η` — `(toSubst f).act (cons α id) (Expr.η p) = f p` (unit_left).
* `Subst.act_kcomp` — Kleisli composition factors (comp_lift).
-/


/-! ## Computation lemmas — `Subst.act` on a specific apply head -/

/-- Computing `σ.act` on an apply whose head is a τ-embedded shape-slot:
collapses to the τ-slot branch reconstruction. -/
theorem Subst.act_apply_embed {C : Carrier} (σ : Subst C) (τ : CTele C)
    {α : C.Arity} (q_τ : τ.shape ∋ α)
    (args : (i : C.Binder α) →
      Expr (((σ.pre ⋈* σ.dom) ⋈* τ.shape) ⋈ i.arity)) :
    σ.act τ (Expr.apply ((τ.embed (σ.pre ⋈* σ.dom)).apply q_τ) args)
      = Expr.apply ((τ.embed (σ.pre ⋈* σ.cod)).apply q_τ)
          (fun j => σ.act (CTele.cons j.arity τ) (args j)) := by
  have h := Subst.act.eq_1 σ τ α ((τ.embed (σ.pre ⋈* σ.dom)).apply q_τ) args
  rw [τ.classify_embed (σ.pre ⋈* σ.dom)] at h
  exact h

/-- Computing `σ.act` on an apply whose head is a τ-weakened below-slot:
collapses to the below-τ branch, which dispatches via `σ.classifyDom`. -/
theorem Subst.act_apply_weaken {C : Carrier} (σ : Subst C) (τ : CTele C)
    {α : C.Arity} (q : (σ.pre ⋈* σ.dom) ∋ α)
    (args : (i : C.Binder α) →
      Expr (((σ.pre ⋈* σ.dom) ⋈* τ.shape) ⋈ i.arity)) :
    σ.act τ (Expr.apply ((τ.weaken (σ.pre ⋈* σ.dom)).apply q) args)
      = (match σ.classifyDom q with
          | PreOrDom.dom q_dom =>
              let aux : Subst C := {
                pre := σ.pre ⋈* σ.cod
                dom := Shape.nil ⋈ α
                cod := τ.shape
                sub := fun {_} q' => match q' with
                  | .here i => σ.act (CTele.cons i.arity τ) (args i)
                classifyDom := fun {_} p' =>
                  match p' with
                  | .here i  => PreOrDom.dom (.here i)
                  | .there q => PreOrDom.pre q
                weakenCod := τ.weaken (σ.pre ⋈* σ.cod)
              }
              aux.act CTele.id (σ.sub q_dom)
          | PreOrDom.pre q_pre =>
              Expr.apply ((τ.weaken (σ.pre ⋈* σ.cod)).apply
                           ((σ.weakenCod).apply q_pre))
                (fun i => σ.act (CTele.cons i.arity τ) (args i))) := by
  have h := Subst.act.eq_1 σ τ α ((τ.weaken (σ.pre ⋈* σ.dom)).apply q) args
  rw [τ.classify_weaken (σ.pre ⋈* σ.dom)] at h
  exact h

/-! ## Auxiliary: η-walk on a τ-side slot -/

/-- Walking an η-expansion of a τ-side slot reproduces the η in the target
shape.  By WF recursion on the slot's arity `α`.  Uses `act_apply_embed`
as a black-box computation lemma — no `unfold Subst.act` needed. -/
theorem Subst.act_η_τ {C : Carrier} (σ : Subst C) (t : CTele C)
    {α : C.Arity} (q_τ : t.shape ∋ α) :
    σ.act (CTele.cons α t)
        (Expr.η (t.embed (σ.pre ⋈* σ.dom) q_τ))
      = Expr.η (t.embed (σ.pre ⋈* σ.cod) q_τ) := by
  rw [Expr.η.eq_1]
  -- `.there ((t.embed Γ).apply q_τ) = ((cons α t).embed Γ).apply (.there q_τ)`
  -- by cons_embed_there (rfl).  `change` accepts the defeq.
  change σ.act (CTele.cons α t)
      (Expr.apply (((CTele.cons α t).embed (σ.pre ⋈* σ.dom)).apply
                     (ListSlotAt.there q_τ))
                  (fun i => Expr.η (ListSlotAt.here i))) = _
  rw [Subst.act_apply_embed σ (CTele.cons α t) (ListSlotAt.there q_τ)]
  rw [Expr.η.eq_1]
  congr 1
  funext i
  exact Subst.act_η_τ σ (CTele.cons α t)
          (q_τ := @ListSlotAt.here C α t.shape.toList i)
termination_by α
decreasing_by exact ⟨i, rfl⟩

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
