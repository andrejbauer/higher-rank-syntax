import HigherRankSyntaxTele.Subst

/-!
# `IsIdentity` predicate on substitutions

`σ : Subst pre S S` (with `dom = cod = S`) "acts as the identity"
when its `sub` field returns the η-expansion of the canonical
embedding of the source slot into `pre ⋈* S`.

This is a single-Prop-field structure — the `ProperTele` instance on
`S` provides the canonical embedding, so the condition is one equation.
-/


/-- A `Subst` (with `dom = cod = S`) acts as the identity walker if its
`sub` field is the η-expansion of the canonical embedding. -/
structure Subst.IsIdentity {C : Carrier} {pre S : Shape C} [ProperTele S]
    (σ : Subst C pre S S) : Prop where
  /-- `σ.sub q` is `Expr.η` of `q` embedded into `pre ⋈* S` via the
  S-side injection given by the `ProperTele S` instance. -/
  sub_canon : ∀ {α : C.Arity} (q : S ∋ α),
    σ.sub q = Expr.η ((ProperTele.embed (t := S) pre).apply q)

/-! ## Companion lemmas -/

/-- Two `IsIdentity` Substs at the same pre/dom/cod are equal: their
`sub` fields are both pinned down by `sub_canon`. -/
theorem Subst.IsIdentity.unique {C : Carrier} {pre S : Shape C} [ProperTele S]
    {σ₁ σ₂ : Subst C pre S S} (h₁ : σ₁.IsIdentity) (h₂ : σ₂.IsIdentity) :
    σ₁ = σ₂ := by
  rcases σ₁ with ⟨sub₁⟩
  rcases σ₂ with ⟨sub₂⟩
  congr
  funext α q
  exact (h₁.sub_canon q).trans (h₂.sub_canon q).symm

/-- `Subst.id Γ` is `IsIdentity`. -/
theorem Subst.id_isIdentity {C : Carrier} (Γ : Shape C) [ProperTele Γ] :
    (Subst.id Γ).IsIdentity where
  sub_canon q := by
    show Expr.η q = Expr.η ((ProperTele.embed (t := Γ) Shape.nil).apply q)
    rw [ProperTele.embed_nil_id q]
    rfl
