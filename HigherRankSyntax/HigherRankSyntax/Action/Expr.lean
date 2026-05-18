import HigherRankSyntax.Action.Shape
import HigherRankSyntax.Action.Renaming

/-!
# Expressions of a higher-rank binding signature

`Expr Γ` is the type of expressions in shape `Γ` over a carrier `C`.  The primary
constructor `apply'` takes a head slot `p`, an arity `α`, a propositional witness
`hα : p.arity = α`, and a dependent family of children indexed by `C.Binder α`, each
child living in `Γ` extended by the binder's sub-arity.  The smart constructor `apply`
specialises to `α := p.arity` with a reflexive proof.

Carrying `α` propositionally at the constructor lets a renaming preserve the children's
index — the renamed head `ρ p` shares the same `α` via `(ρ.arity p).trans hα`, so no
`Eq.rec`-transport is needed in `Renaming.actExpr` or the functoriality proofs.

`Expr` is the W-type of `Shape ◅ Slot` decorated by `Slot.arity`, with the recursive
child's shape index shifted by the action `⋈` — the free relative monad of the decorated
container.
-/

namespace Action

/-- Expressions in shape `Γ` over a carrier `C`. -/
inductive Expr {C : Carrier} : Shape C → Type where
  /-- An application of a head slot `p` of `Γ` (with propositional arity `α`) to a
      dependent family of children, one per binder of `α`. -/
  | apply' : {Γ : Shape C} → (p : Slot Γ) → (α : C.Arity) → (hα : p.arity = α) →
             (args : (i : C.Binder α) → Expr (Γ ⋈ i.arity)) →
             Expr Γ

abbrev Expr.head {C : Carrier} {Γ : Shape C}: Expr Γ → Slot Γ
| .apply' p _ _ _ => p

/-- Smart constructor: when the head's arity is intended to be its own `Slot.arity`, no
propositional proof is needed. -/
@[reducible]
def Expr.apply {C : Carrier} {Γ : Shape C} (p : Slot Γ)
    (args : (i : C.Binder p.arity) → Expr (Γ ⋈ i.arity)) : Expr Γ :=
  Expr.apply' p p.arity rfl args

/-! ## Structural subterm relation

A heterogeneous "one-step child" relation on expressions, packaged as a relation on
`Σ Γ, Expr Γ` so the two sides — which live at different shape indices — share a
homogeneous type. -/

/-- `Expr.Subterm e' e` holds when `e` is some `apply' p α hα args` and `e'` is one of its
arguments `args j`.  The shape indices come along inside the `Σ`. -/
inductive Expr.Subterm {C : Carrier} :
    (Σ Γ : Shape C, Expr Γ) → (Σ Γ : Shape C, Expr Γ) → Prop where
  | of_arg {Γ : Shape C} (p : Slot Γ) (α : C.Arity) (hα : p.arity = α)
      (args : (i : C.Binder α) → Expr (Γ ⋈ i.arity))
      (j : C.Binder α) :
      Expr.Subterm ⟨Γ ⋈ j.arity, args j⟩ ⟨Γ, Expr.apply' p α hα args⟩

/-- The subterm relation is well-founded by structural induction on the second component. -/
theorem Expr.Subterm.wf {C : Carrier} : WellFounded (@Expr.Subterm C) := by
  refine ⟨fun ⟨Γ, e⟩ => ?_⟩
  induction e with
  | apply' p α hα args ih =>
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
  { p : Slot Γ // p.arity = α }

/-- The relative monad's target: expressions with free shape `Γ` under one outer α-binder. -/
abbrev Expr.T {C : Carrier} (Γ : Shape C) (α : C.Arity) : Type := Expr (Γ ⋈ α)

/-- η-expansion: a variable `⟨p, hp⟩` of arity `α` at `Γ` becomes the fully-applied tree
`apply' (.there p) α hp (fun i => η (.here i))`, where each binder `i` of `α` recursively
η-expands the bound variable.  Termination descends along the sub-arity relation: each
recursive call uses `i.arity`, strictly smaller than `α` via `subWf`. -/
def Expr.η {C : Carrier} : (Γ : Shape C) → (α : C.Arity) → Expr.J Γ α → Expr.T Γ α
  | Γ, α, ⟨p, hp⟩ =>
    Expr.apply' (.there p) α hp (fun i =>
      Expr.η (Γ ⋈ α) i.arity ⟨.here i, rfl⟩)
termination_by Γ α _ => α
decreasing_by exact ⟨_, rfl⟩

/-! ## Renaming action -/

/-- Action of a renaming on an expression.  The head slot is sent through the renaming;
the head's arity `α` is unchanged, with the new proof `(ρ.arity p).trans hα`.  Into each
child of binder `i` we recurse with the renaming extended through the new binder of arity
`i.arity`. -/
def Renaming.actExpr {C : Carrier} : {Γ Δ : Shape C} → (Γ →ʳ Δ) → Expr Γ → Expr Δ
  | _, _, ρ, .apply' p α hα args =>
    Expr.apply' (ρ p) α ((ρ.arity p).trans hα) (fun i =>
      Renaming.actExpr (ρ ⇑ʳ i.arity) (args i))

/-- Action of a renaming on an expression: `⟦ ρ ⟧ʳ e`. -/
scoped notation:60 "⟦" ρ "⟧ʳ " e:61 => Renaming.actExpr ρ e

@[simp]
theorem Renaming.actExpr.map_id {C : Carrier} : ∀ {Γ : Shape C} (e : Expr Γ),
    ⟦ 𝟙ʳ ⟧ʳ e = e
  | _, .apply' p α hα args => by
    show Expr.apply' p α (((𝟙ʳ : _ →ʳ _).arity p).trans hα)
           (fun i => ⟦ (𝟙ʳ : _ →ʳ _) ⇑ʳ i.arity ⟧ʳ args i)
      = Expr.apply' p α hα args
    congr 1
    funext i
    rw [Renaming.extend_id]
    exact Renaming.actExpr.map_id (args i)

@[simp]
theorem Renaming.actExpr.map_comp {C : Carrier} : ∀ {Γ Δ Ε : Shape C}
    (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ε) (e : Expr Γ), ⟦ σ ∘ʳ ρ ⟧ʳ e = ⟦ σ ⟧ʳ (⟦ ρ ⟧ʳ e)
  | _, _, _, ρ, σ, .apply' p α hα args => by
    show Expr.apply' (σ (ρ p)) α (((σ ∘ʳ ρ).arity p).trans hα)
           (fun i => ⟦ (σ ∘ʳ ρ) ⇑ʳ i.arity ⟧ʳ args i)
      = Expr.apply' (σ (ρ p)) α ((σ.arity (ρ p)).trans ((ρ.arity p).trans hα))
           (fun i => ⟦ σ ⇑ʳ i.arity ⟧ʳ (⟦ ρ ⇑ʳ i.arity ⟧ʳ args i))
    congr 1
    funext i
    rw [Renaming.extend_comp]
    exact Renaming.actExpr.map_comp _ _ (args i)

/-! ## J and T as functors

`J` and `T` are functors `C.Shape ⥤ (C.Arity → Type)`.  The shape argument is functorial
along renamings; the arity argument is discrete. -/

/-- Action of a renaming on `J`: send `⟨p, hp⟩` of arity `α` in `Γ` to `⟨ρ p, _⟩` of arity
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
