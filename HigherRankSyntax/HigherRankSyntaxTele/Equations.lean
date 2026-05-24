import HigherRankSyntaxTele.Subst

/-!
# Equations of the substitution walker

This file holds the auxiliary equations needed to prove the three
relative-monad laws (`unit_right`, `unit_left`, `comp_lift`).

`Subst.act` recurses with a lex measure on `(σ.dom.toList via DomLt,
Expr.Subterm)`.  Lemmas about it follow the same lex induction.

The critical helper is **`act_η_τ`**: walking `Expr.η q_lifted` for a
τ-side slot reproduces the η in the target shape.  It is proved by
induction on the slot's arity via `C.subWf` — the η-args inside `Expr.η`
recurse on strictly smaller arities, and CTele's `classify_embed` field
collapses the τ-classify dispatch to the shape-continuation.

From `act_η_τ`, the unit laws fold out:
* **`unit_right`** — `lift (η Γ) = 𝟙 (map Γ)`: by structural induction
  on the input, using `act_η_τ` at each τ-slot encountered and a
  separate "identity walker on the aux Subst" sub-lemma in the dom
  case.
* **`unit_left`** — `f = η Γ ≫ lift f`: the dom-aux Subst has `sub`
  computed by `act_η_τ`'s recursive application to η-args, so it acts
  as the identity walker on `f p`.

`comp_lift` is structurally harder (needs Subst composition); deferred.
-/


/-! ## Helper: η-walk on a τ-side slot -/

/-- **act_η_τ**: walking an η-expansion of a τ-side slot reproduces the η in
the target shape.  Induction on `α` via `C.subWf` — the η-args inside
`Expr.η` recurse on strictly smaller arities. -/
theorem Subst.act_η_τ {C : Carrier} (σ : Subst C) (t : CTele C)
    {α : C.Arity} (q_τ : t.shape ∋ α) :
    σ.act (CTele.cons α t)
        (Expr.η (t.embed (σ.pre ⋈* σ.dom) q_τ))
      = Expr.η (t.embed (σ.pre ⋈* σ.cod) q_τ) := by
  sorry

/-! ## Monad laws -/

/-- **unit_right** — `lift (η Γ) = 𝟙 (map Γ)`. -/
theorem Subst.unit_right {C : Carrier} {Γ : Shape C} (α : C.Arity)
    (e : Expr (Γ ⋈ α)) :
    (toSubst (fun {β : C.Arity} (p : Γ ∋ β) => Expr.η p)).act
        (CTele.cons α CTele.id) e
      = e := by
  sorry

/-- **unit_left** — `f = η Γ ≫ lift f`. -/
theorem Subst.unit_left {C : Carrier} {Γ Δ : Shape C}
    (f : ∀ {β : C.Arity}, (Γ ∋ β) → Expr (Δ ⋈ β))
    (α : C.Arity) (p : Γ ∋ α) :
    f p
      = (toSubst (fun {β} p => f p)).act (CTele.cons α CTele.id) (Expr.η p) := by
  sorry

/-- **comp_lift** — `lift (f ≫ lift g) = lift f ≫ lift g`.  Needs a Subst
composition theory; deferred. -/
theorem Subst.comp_lift {C : Carrier} {Γ Δ Ε : Shape C}
    (f : ∀ {β : C.Arity}, (Γ ∋ β) → Expr (Δ ⋈ β))
    (g : ∀ {β : C.Arity}, (Δ ∋ β) → Expr (Ε ⋈ β))
    (α : C.Arity) (e : Expr (Γ ⋈ α)) :
    (toSubst (fun {β} (p : Γ ∋ β) =>
        (toSubst (fun {γ} q => g q)).act (CTele.cons β CTele.id) (f p))).act
          (CTele.cons α CTele.id) e
      = (toSubst (fun {β} q => g q)).act (CTele.cons α CTele.id)
          ((toSubst (fun {β} p => f p)).act (CTele.cons α CTele.id) e) := by
  sorry
