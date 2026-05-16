import HigherRankSyntax.Action.Carrier
import HigherRankSyntax.Action.Renaming

/-!
# Expressions of a higher-rank binding signature

`Expr γ` is the type of expressions in shape γ over a carrier `C`.
The primary constructor `apply'` takes a head slot `x` and a
propositional witness `hα` that `x` has arity `α`, with the
children typed in terms of `α`.  The smart constructor `apply`
specialises to `α = shapeArity γ x` with a reflexive proof.

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

/-- Expressions in shape `γ` over a carrier `C`.

The primary constructor `apply'` carries the head's arity `α` and
a propositional proof `hα` that `x` has that arity.  Carrying the
arity explicitly lets callers describe children in terms of `α`
rather than `shapeArity γ x`, so consumers that already know
`α` (e.g. `Renaming.actExpr`, `Expr.η`) can build expressions
directly without an arity-transport. -/
inductive Expr {C : Carrier} : C.Shape → Type where
  /-- An application of a head slot `x` of `γ` (with propositional
      arity `α`) to a dependent family of children, one per binder
      position of `α`. -/
  | apply' {γ : C.Shape} (x : C.ShapeSlots γ) (α : C.Arity)
      (hα : C.shapeArity γ x = α)
      (args : (y : C.AritySlots α) →
              Expr (γ ⋈ C.arityArity α y)) :
      Expr γ

/-- Smart constructor: when the head's arity is intended to be its
own `shapeArity`, no propositional proof is needed. -/
@[reducible]
def Expr.apply {C : Carrier} {γ : C.Shape} (x : C.ShapeSlots γ)
    (args : (y : C.AritySlots (C.shapeArity γ x)) →
            Expr (γ ⋈ C.arityArity (C.shapeArity γ x) y)) :
    Expr γ :=
  Expr.apply' x (C.shapeArity γ x) rfl args

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

/-! ## The unit `η`

`Expr.η γ α : J γ α → T γ α = Expr (γ ⋈ α)` η-expands a variable
into a fully-applied expression.

A variable `⟨x, hx⟩` of arity `α` in `γ` becomes
`apply' xHead α hHead children`, where
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
      Expr.η (γ ⋈ α) (C.arityArity α y)
        ⟨Carrier.inrSlot γ α y, Carrier.shapeArity_inrSlot γ α y⟩
termination_by γ α _ => α
decreasing_by exact ⟨_, rfl⟩

/-! ## Renaming-action on expressions

The action of a renaming `f : γ →ʳ δ` on an expression sends each
slot through `f`; under each binder of arity `β_y`, the renaming
extends via `f ⇑ʳ β_y` to handle the new bound variables.

With `apply'` as the primary constructor the action is a plain
structural recursion: no arity-transport at the call site. -/

/-- Action of a renaming on an expression. -/
def Renaming.actExpr {C : Carrier} :
    {γ δ : C.Shape} → (γ →ʳ δ) → Expr γ → Expr δ
  | _, _, f, .apply' x α hα args =>
    Expr.apply' (f x) α ((f.arity_preserving x).trans hα)
      fun y => Renaming.actExpr (f ⇑ʳ C.arityArity α y) (args y)

/-- Action of a renaming on an expression: `⟦ f ⟧ʳ e`. -/
scoped notation:60 "⟦" f "⟧ʳ " e:61 => Renaming.actExpr f e

/-! ## Functoriality of `actExpr`

`actExpr` preserves identity and composition, making
`T γ α = Expr (γ ⋈ α)` a functor in its Shape argument. -/

@[simp]
theorem Renaming.actExpr.map_id {C : Carrier} :
    ∀ {γ : C.Shape} (e : Expr γ), ⟦ 𝟙ʳ ⟧ʳ e = e
  | _, .apply' x α hα args => by
    show Expr.apply' x α hα
           (fun y => ⟦ (𝟙ʳ : _ →ʳ _) ⇑ʳ C.arityArity α y ⟧ʳ (args y))
       = Expr.apply' x α hα args
    have h : (fun y => ⟦ (𝟙ʳ : _ →ʳ _) ⇑ʳ C.arityArity α y ⟧ʳ (args y))
             = args := by
      funext y
      rw [Renaming.extend_id]
      exact Renaming.actExpr.map_id (args y)
    rw [h]

@[simp]
theorem Renaming.actExpr.map_comp {C : Carrier} :
    ∀ {γ δ ε : C.Shape} (f : γ →ʳ δ) (g : δ →ʳ ε) (e : Expr γ),
      ⟦ g ∘ʳ f ⟧ʳ e = ⟦ g ⟧ʳ (⟦ f ⟧ʳ e)
  | _, _, _, f, g, .apply' x α hα args => by
    show Expr.apply' (g (f x)) α
           (((g.arity_preserving (f x)).trans (f.arity_preserving x)).trans hα)
           (fun y => ⟦ (g ∘ʳ f) ⇑ʳ C.arityArity α y ⟧ʳ (args y))
       = Expr.apply' (g (f x)) α
           ((g.arity_preserving (f x)).trans ((f.arity_preserving x).trans hα))
           (fun y => ⟦ g ⇑ʳ C.arityArity α y ⟧ʳ (⟦ f ⇑ʳ C.arityArity α y ⟧ʳ (args y)))
    congr 1
    funext y
    rw [Renaming.extend_comp]
    exact Renaming.actExpr.map_comp _ _ (args y)

/-! ## Functoriality of `J` and `T`

`J` and `T` are functors `C.Shape → (C.Arity → Type)`.  The shape
argument is functorial along renamings; the arity argument is
discrete.  We package the morphism action explicitly. -/

/-- Action of a renaming on `J`: send `⟨x, hx⟩` of arity α in γ to
`⟨f x, hx after f's arity-preservation⟩` of arity α in δ. -/
def Expr.J.map {C : Carrier} {γ δ : C.Shape} (f : γ →ʳ δ)
    {α : C.Arity} (v : Expr.J γ α) : Expr.J δ α :=
  ⟨f v.val, (f.arity_preserving v.val).trans v.property⟩

@[simp]
theorem Expr.J.map_id {C : Carrier} {γ : C.Shape} {α : C.Arity}
    (v : Expr.J γ α) : Expr.J.map 𝟙ʳ v = v := rfl

@[simp]
theorem Expr.J.map_comp {C : Carrier} {γ δ ε : C.Shape}
    (f : γ →ʳ δ) (g : δ →ʳ ε) {α : C.Arity} (v : Expr.J γ α) :
    Expr.J.map (g ∘ʳ f) v = Expr.J.map g (Expr.J.map f v) := rfl

/-- Action of a renaming on `T`: `T γ α = Expr (γ ⋈ α)`, and a
renaming `f : γ →ʳ δ` extended through the bound binder `α` acts
on expressions via `actExpr`. -/
def Expr.T.map {C : Carrier} {γ δ : C.Shape} (f : γ →ʳ δ)
    (α : C.Arity) (e : Expr.T γ α) : Expr.T δ α :=
  ⟦ f ⇑ʳ α ⟧ʳ e

@[simp]
theorem Expr.T.map_id {C : Carrier} {γ : C.Shape} (α : C.Arity)
    (e : Expr.T γ α) : Expr.T.map 𝟙ʳ α e = e := by
  show ⟦ (𝟙ʳ : γ →ʳ γ) ⇑ʳ α ⟧ʳ e = e
  rw [Renaming.extend_id]
  exact Renaming.actExpr.map_id e

@[simp]
theorem Expr.T.map_comp {C : Carrier} {γ δ ε : C.Shape}
    (f : γ →ʳ δ) (g : δ →ʳ ε) (α : C.Arity) (e : Expr.T γ α) :
    Expr.T.map (g ∘ʳ f) α e = Expr.T.map g α (Expr.T.map f α e) := by
  show ⟦ (g ∘ʳ f) ⇑ʳ α ⟧ʳ e = ⟦ g ⇑ʳ α ⟧ʳ (⟦ f ⇑ʳ α ⟧ʳ e)
  rw [Renaming.extend_comp]
  exact Renaming.actExpr.map_comp _ _ e

end Action
