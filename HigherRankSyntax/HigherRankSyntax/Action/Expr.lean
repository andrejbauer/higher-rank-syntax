import HigherRankSyntax.Action.Shape
import HigherRankSyntax.Action.Renaming

/-!
# Expressions of a higher-rank binding signature

`Expr Γ` is the type of expressions in shape `Γ` over a carrier `C`.  The primary
constructor `apply'` takes a head slot `x`, an arity `α`, a propositional witness
`hα : x.arity = α`, and a dependent family of children indexed by `C.AritySlot α`, each
child living in `Γ` extended by the binder's sub-arity.  The smart constructor `apply`
specialises to `α := x.arity` with a reflexive proof.

Carrying `α` propositionally at the constructor lets a renaming preserve the children's
index — the renamed head `ρ x` shares the same `α` via `(ρ.arity x).trans hα`, so no
`Eq.rec`-transport is needed in `Renaming.actExpr` or the functoriality proofs.

`Expr` is the W-type of `Shape ◅ Slot` decorated by `Slot.arity`, with the recursive
child's shape index shifted by the action `⋈` — the free relative monad of the decorated
container.
-/

namespace Action

/-- Expressions in shape `Γ` over a carrier `C`. -/
inductive Expr {C : Carrier} : Shape C → Type where
  /-- An application of a head slot `x` of `Γ` (with propositional arity `α`) to a
      dependent family of children, one per binder position of `α`. -/
  | apply' : {Γ : Shape C} → (x : Slot Γ) → (α : C.Arity) → (hα : x.arity = α) →
             (args : (y : C.AritySlot α) → Expr (Γ ⋈ C.arityArity α y)) →
             Expr Γ

abbrev Expr.head {C : Carrier} {Γ : Shape C}: Expr Γ → Slot Γ
| .apply' x _ _ _ => x

/-- Smart constructor: when the head's arity is intended to be its own `Slot.arity`, no
propositional proof is needed. -/
@[reducible]
def Expr.apply {C : Carrier} {Γ : Shape C} (x : Slot Γ)
    (args : (y : C.AritySlot x.arity) → Expr (Γ ⋈ C.arityArity x.arity y)) : Expr Γ :=
  Expr.apply' x x.arity rfl args

/-! ## Structural subterm relation

A heterogeneous "one-step child" relation on expressions, packaged as a relation on
`Σ Γ, Expr Γ` so the two sides — which live at different shape indices — share a
homogeneous type. -/

/-- `Expr.Subterm e' e` holds when `e` is some `apply' x α hα args` and `e'` is one of its
arguments `args z`.  The shape indices come along inside the `Σ`. -/
inductive Expr.Subterm {C : Carrier} :
    (Σ Γ : Shape C, Expr Γ) → (Σ Γ : Shape C, Expr Γ) → Prop where
  | of_arg {Γ : Shape C} (x : Slot Γ) (α : C.Arity) (hα : x.arity = α)
      (args : (y : C.AritySlot α) → Expr (Γ ⋈ C.arityArity α y))
      (z : C.AritySlot α) :
      Expr.Subterm ⟨Γ ⋈ C.arityArity α z, args z⟩ ⟨Γ, Expr.apply' x α hα args⟩

/-- The subterm relation is well-founded by structural induction on the second component. -/
theorem Expr.Subterm.wf {C : Carrier} : WellFounded (@Expr.Subterm C) := by
  refine ⟨fun ⟨Γ, e⟩ => ?_⟩
  induction e with
  | apply' x α hα args ih =>
    refine Acc.intro _ ?_
    rintro ⟨_, _⟩ h
    cases h
    exact ih _

instance Expr.Subterm.wellFoundedRelation {C : Carrier} :
    WellFoundedRelation (Σ Γ : Shape C, Expr Γ) where
  rel := @Expr.Subterm C
  wf := Expr.Subterm.wf

/-! ## J, T, η -/

/-- The variables of arity `α` at `Γ`: slots of `Γ` whose arity equals `α`. -/
def Expr.J {C : Carrier} (Γ : Shape C) (α : C.Arity) : Type :=
  { x : Slot Γ // x.arity = α }

/-- The relative monad's target: expressions with free shape `Γ` under one outer α-binder. -/
abbrev Expr.T {C : Carrier} (Γ : Shape C) (α : C.Arity) : Type := Expr (Γ ⋈ α)

/-- η-expansion: a variable `⟨x, hx⟩` of arity `α` at `Γ` becomes the fully-applied tree
`apply' (.there x) α hx (fun y => η (.here y))`, where each binder position `y` of `α`
recursively η-expands the bound variable.  Termination descends along the sub-arity
relation: each recursive call uses `C.arityArity α y`, strictly smaller than `α` via
`aritySubWf`. -/
def Expr.η {C : Carrier} : (Γ : Shape C) → (α : C.Arity) → Expr.J Γ α → Expr.T Γ α
  | Γ, α, ⟨x, hx⟩ =>
    Expr.apply' (.there x) α hx (fun y =>
      Expr.η (Γ ⋈ α) (C.arityArity α y) ⟨.here y, rfl⟩)
termination_by Γ α _ => α
decreasing_by exact ⟨_, rfl⟩

/-! ## Renaming action -/

/-- Action of a renaming on an expression.  The head slot is sent through the renaming;
the head's arity `α` is unchanged, with the new proof `(ρ.arity x).trans hα`.  Into each
child of arity-position `y` we recurse with the renaming extended through the new binder
of arity `C.arityArity α y`. -/
def Renaming.actExpr {C : Carrier} : {Γ Δ : Shape C} → (Γ →ʳ Δ) → Expr Γ → Expr Δ
  | _, _, ρ, .apply' x α hα args =>
    Expr.apply' (ρ x) α ((ρ.arity x).trans hα) (fun y =>
      Renaming.actExpr (ρ ⇑ʳ C.arityArity α y) (args y))

/-- Action of a renaming on an expression: `⟦ ρ ⟧ʳ e`. -/
scoped notation:60 "⟦" ρ "⟧ʳ " e:61 => Renaming.actExpr ρ e

@[simp]
theorem Renaming.actExpr.map_id {C : Carrier} : ∀ {Γ : Shape C} (e : Expr Γ),
    ⟦ 𝟙ʳ ⟧ʳ e = e
  | _, .apply' x α hα args => by
    show Expr.apply' x α (((𝟙ʳ : _ →ʳ _).arity x).trans hα)
           (fun y => ⟦ (𝟙ʳ : _ →ʳ _) ⇑ʳ C.arityArity α y ⟧ʳ args y)
      = Expr.apply' x α hα args
    congr 1
    funext y
    rw [Renaming.extend_id]
    exact Renaming.actExpr.map_id (args y)

@[simp]
theorem Renaming.actExpr.map_comp {C : Carrier} : ∀ {Γ Δ Ε : Shape C}
    (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ε) (e : Expr Γ), ⟦ σ ∘ʳ ρ ⟧ʳ e = ⟦ σ ⟧ʳ (⟦ ρ ⟧ʳ e)
  | _, _, _, ρ, σ, .apply' x α hα args => by
    show Expr.apply' (σ (ρ x)) α (((σ ∘ʳ ρ).arity x).trans hα)
           (fun y => ⟦ (σ ∘ʳ ρ) ⇑ʳ C.arityArity α y ⟧ʳ args y)
      = Expr.apply' (σ (ρ x)) α ((σ.arity (ρ x)).trans ((ρ.arity x).trans hα))
           (fun y => ⟦ σ ⇑ʳ C.arityArity α y ⟧ʳ (⟦ ρ ⇑ʳ C.arityArity α y ⟧ʳ args y))
    congr 1
    funext y
    rw [Renaming.extend_comp]
    exact Renaming.actExpr.map_comp _ _ (args y)

/-! ## J and T as functors

`J` and `T` are functors `C.Shape ⥤ (C.Arity → Type)`.  The shape argument is functorial
along renamings; the arity argument is discrete. -/

/-- Action of a renaming on `J`: send `⟨x, hx⟩` of arity `α` in `Γ` to `⟨ρ x, _⟩` of arity
`α` in `Δ`. -/
def Expr.J.map {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ) {α : C.Arity}
    (v : Expr.J Γ α) : Expr.J Δ α :=
  ⟨ρ v.val, (ρ.arity v.val).trans v.property⟩

@[simp] theorem Expr.J.map_id {C : Carrier} {Γ : Shape C} {α : C.Arity}
    (v : Expr.J Γ α) : Expr.J.map 𝟙ʳ v = v := rfl

@[simp] theorem Expr.J.map_comp {C : Carrier} {Γ Δ Ε : Shape C}
    (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ε) {α : C.Arity} (v : Expr.J Γ α) :
    Expr.J.map (σ ∘ʳ ρ) v = Expr.J.map σ (Expr.J.map ρ v) := rfl

/-- Action of a renaming on `T`: extend the renaming through the bound α-binder and apply
the renaming action on expressions. -/
def Expr.T.map {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ) (α : C.Arity)
    (e : Expr.T Γ α) : Expr.T Δ α := ⟦ ρ ⇑ʳ α ⟧ʳ e

@[simp] theorem Expr.T.map_id {C : Carrier} {Γ : Shape C} (α : C.Arity) (e : Expr.T Γ α) :
    Expr.T.map 𝟙ʳ α e = e := by
  show ⟦ (𝟙ʳ : Γ →ʳ Γ) ⇑ʳ α ⟧ʳ e = e
  rw [Renaming.extend_id]
  exact Renaming.actExpr.map_id e

@[simp] theorem Expr.T.map_comp {C : Carrier} {Γ Δ Ε : Shape C}
    (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ε) (α : C.Arity) (e : Expr.T Γ α) :
    Expr.T.map (σ ∘ʳ ρ) α e = Expr.T.map σ α (Expr.T.map ρ α e) := by
  show ⟦ (σ ∘ʳ ρ) ⇑ʳ α ⟧ʳ e = ⟦ σ ⇑ʳ α ⟧ʳ (⟦ ρ ⇑ʳ α ⟧ʳ e)
  rw [Renaming.extend_comp]
  exact Renaming.actExpr.map_comp _ _ e

end Action
