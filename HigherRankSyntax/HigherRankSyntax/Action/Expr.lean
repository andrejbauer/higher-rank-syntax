import HigherRankSyntax.Action.Carrier
import HigherRankSyntax.Action.Renaming

/-!
# Expressions of a higher-rank binding signature

`Expr γ` is the type of expressions in shape γ over a carrier `C`.
The single constructor `apply` has a head slot `x` of `γ` and a
dependent family of children, one per binder position of `x`'s
arity.  The child at position `y` lives in the shape extended by
the binder's arity.

Container view: `Expr` is the W-type of the shape container
`Shape ◅ ShapeSlots` decorated by `shapeArity`, with the recursive
call's shape index shifted by the action `⋈` — the free relative
monad of the decorated container.

An expression is just a syntactic object in a shape — there is no
"arity index" on `Expr` itself.  When `Expr` is viewed through the
relative monad of binding signatures, the bound-arity index of the
monad's functor `T γ α := Expr (γ ⋈ α)` arises by *encoding* the
bound shape `α` via the action, not by adding a second index to
`Expr`.
-/

namespace Action

/-- Expressions in shape `γ` over a carrier `C`. -/
inductive Expr {C : Carrier} : C.Shape → Type where
  /-- An application of a head slot `x` of `γ` to a dependent family
      of children, one per binder position of `x`'s arity. -/
  | apply {γ : C.Shape} (x : C.ShapeSlots γ)
      (args : (y : C.AritySlots (C.shapeArity γ x)) →
              Expr (γ ⋈ C.arityArity (C.shapeArity γ x) y)) :
      Expr γ

/-! ## The relative-monad functors

The relative monad of `Expr` acts on the category of shapes (with
arity-respecting renamings) along the J-functor that picks out the
variables of a given arity.  The codomain category is
`Arity → Type`.

* `Expr.J γ α` — the variables of arity `α` in shape `γ`.
* `Expr.T γ α := Expr (γ ⋈ α)` — expressions where the bound arity
  `α` has been encoded as the outermost extension of `γ`.

Entering an arg under a binder `β` sends `T γ α` to `T (γ ⋈ α) β` —
the old bound is absorbed into the free side, the new bound is `β`.
-/

/-- The variables of arity `α` in `γ`: slots of `γ` whose
    arity equals `α`. -/
def Expr.J {C : Carrier} (γ : C.Shape) (α : C.Arity) : Type :=
  { x : C.ShapeSlots γ // C.shapeArity γ x = α }

/-- The relative monad's target: expressions with free shape `γ` and
    outermost bound arity `α` are just expressions in the extended
    shape `γ ⋈ α`. -/
abbrev Expr.T {C : Carrier} (γ : C.Shape) (α : C.Arity) : Type :=
  Expr (γ ⋈ α)

/-! ## Transport helper -/

/-- Transport preservation for `arityArity`: applying `arityArity`
to a value that has been transported along an arity equality yields
the same arity as before the transport. -/
private theorem arityArity_eq_rec {C : Carrier}
    {a b : C.Arity} (h : a = b) (y : C.AritySlots a) :
    C.arityArity b (h ▸ y) = C.arityArity a y := by
  cases h
  rfl

/-! ## `Expr.apply'`: applying with a propositional arity

When the head's arity is known propositionally (not definitionally)
to equal some target arity, `Expr.apply'` performs the implicit
transport so the children can be supplied with their type stated in
terms of the target arity directly. -/

/-- Construct an `Expr.apply` when the head's arity is known
propositionally rather than definitionally. -/
def Expr.apply' {C : Carrier} {γ : C.Shape}
    (x : C.ShapeSlots γ) (α : C.Arity)
    (hα : C.shapeArity γ x = α)
    (children : (y : C.AritySlots α) →
                Expr (γ ⋈ C.arityArity α y)) :
    Expr γ :=
  Expr.apply x (fun y =>
    (arityArity_eq_rec hα y) ▸ children (hα ▸ y))

/-- `Expr.apply'` at a reflexive arity proof reduces to a plain
`Expr.apply`. -/
@[simp]
theorem Expr.apply'_rfl {C : Carrier} {γ : C.Shape}
    (x : C.ShapeSlots γ)
    (children : (y : C.AritySlots (C.shapeArity γ x)) →
                Expr (γ ⋈ C.arityArity (C.shapeArity γ x) y)) :
    Expr.apply' x (C.shapeArity γ x) rfl children = Expr.apply x children :=
  rfl

/-! ## The unit `η`

`Expr.η γ α : J γ α → T γ α = Expr (γ ⋈ α)` η-expands a variable
into a fully-applied expression.

A variable `⟨x, hx⟩` of arity `α` in `γ` becomes
`Expr.apply' xHead α hHead children`, where
* `xHead := Carrier.inlSlot γ α x` views `x` as the γ-side slot of
  `γ ⋈ α`, with arity `α` by `shapeArity_inlSlot`;
* for each binder `y` of α, the child is the η-expansion of "the
  y-th binder of α", obtained by reflecting `y` as the bound-side
  slot of `γ ⋈ α` and recursing.

Termination descends along the sub-arity relation: each recursive
call uses `arityArity α y`, strictly smaller in `AritySub` —
witnessed by `⟨y, rfl⟩`. -/
def Expr.η {C : Carrier} :
    (γ : C.Shape) → (α : C.Arity) → Expr.J γ α → Expr.T γ α
  | γ, α, ⟨x, hx⟩ =>
    let xHead := Carrier.inlSlot γ α x
    have hHead : C.shapeArity (γ ⋈ α) xHead = α :=
      (Carrier.shapeArity_inlSlot γ α x).trans hx
    Expr.apply' xHead α hHead fun y =>
      let bound := Carrier.inrSlot γ α y
      Expr.η (γ ⋈ α) (C.arityArity α y)
        ⟨bound, Carrier.shapeArity_inrSlot γ α y⟩
termination_by γ α _ => α
decreasing_by exact ⟨_, rfl⟩

/-! ## Renaming-action on expressions

The action of a renaming `f : γ →ʳ δ` on an expression sends each
slot through `f`; under each binder of arity `β_y`, the renaming
extends via `f.extend` to handle the new bound variables.

This is the functorial action of the `T` functor in its Shape
argument: `T γ α = Expr (γ ⋈ α)` becomes a functor `Shape ⥤ Type`
once `actExpr` is in place. -/

/-- Action of a renaming on an expression. -/
def Renaming.actExpr {C : Carrier} :
    {γ δ : C.Shape} → (γ →ʳ δ) → Expr γ → Expr δ
  | _, _, f, .apply x args =>
    Expr.apply' (f x) (C.shapeArity _ x) (f.arity_preserving x)
      fun y => (f.extend (C.arityArity _ y)).actExpr (args y)

/-- Action of a renaming on an expression: `⟦ f ⟧ʳ e`. -/
scoped notation:60 "⟦" f "⟧ʳ " e:61 => Renaming.actExpr f e

/-! ## Functoriality of `actExpr`

`actExpr` preserves identity and composition, making
`T γ α = Expr (γ ⋈ α)` a functor in its Shape argument. -/

/-- `actExpr` commutes with `Expr.apply'`: the arity proof at the
combined arity is the renaming's `arity_preserving` chained with
the original proof. -/
theorem Renaming.actExpr_apply' {C : Carrier} {γ' δ : C.Shape}
    (g : γ' →ʳ δ)
    (x : C.ShapeSlots γ') (α : C.Arity) (hα : C.shapeArity γ' x = α)
    (children : (y : C.AritySlots α) →
                Expr (γ' ⋈ C.arityArity α y)) :
    ⟦ g ⟧ʳ (Expr.apply' x α hα children) =
    Expr.apply' (g x) α ((g.arity_preserving x).trans hα)
                (fun y => ⟦ g.extend (C.arityArity α y) ⟧ʳ (children y)) := by
  subst hα
  rfl

@[simp]
theorem Renaming.actExpr.map_id {C : Carrier} :
    ∀ {γ : C.Shape} (e : Expr γ), ⟦ Renaming.id γ ⟧ʳ e = e
  | _, .apply x args => by
    show Expr.apply' x (C.shapeArity _ x) rfl
           (fun y => ⟦ (Renaming.id _).extend (C.arityArity _ y) ⟧ʳ (args y))
         = Expr.apply x args
    have h : (fun y => ⟦ (Renaming.id _).extend (C.arityArity _ y) ⟧ʳ (args y))
             = args := by
      funext y
      rw [Renaming.extend_id]
      exact Renaming.actExpr.map_id (args y)
    rw [h]
    rfl

@[simp]
theorem Renaming.actExpr.map_comp {C : Carrier} :
    ∀ {γ δ ε : C.Shape} (f : γ →ʳ δ) (g : δ →ʳ ε) (e : Expr γ),
      ⟦ g ∘ʳ f ⟧ʳ e = ⟦ g ⟧ʳ (⟦ f ⟧ʳ e)
  | _, _, _, f, g, .apply x args => by
    -- Unfold both sides into a common `Expr.apply'` form, then peel off
    -- the head/arity/arity-proof (all definitionally equal) and prove the
    -- children equal pointwise via `extend_comp` and the IH.
    show Expr.apply' ((g ∘ʳ f) x) (C.shapeArity _ x)
            ((g ∘ʳ f).arity_preserving x)
            (fun y => ⟦ (g ∘ʳ f).extend (C.arityArity _ y) ⟧ʳ (args y))
       = ⟦ g ⟧ʳ (⟦ f ⟧ʳ (Expr.apply x args))
    rw [show ⟦ f ⟧ʳ (Expr.apply x args)
          = Expr.apply' (f x) (C.shapeArity _ x) (f.arity_preserving x)
              (fun y => ⟦ f.extend (C.arityArity _ y) ⟧ʳ (args y)) from rfl,
        Renaming.actExpr_apply']
    congr 1
    funext y
    rw [Renaming.extend_comp]
    exact Renaming.actExpr.map_comp _ _ (args y)

end Action
