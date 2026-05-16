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

open scoped Carrier

/-- Expressions in shape `γ` over a carrier `C`. -/
inductive Expr {C : Carrier} : C.Shape → Type where
  /-- An application of a head slot `x` of `γ` to a dependent family
      of children, one per binder position of `x`'s arity. -/
  | apply {γ : C.Shape} (x : C.ShapeSlots γ)
      (args : (y : C.AritySlots (C.shapeArity γ x)) →
              Expr (γ ⋈ C.arityArity (C.shapeArity γ x) y)) :
      Expr γ

namespace Expr

/-! ## The relative-monad functors

The relative monad of `Expr` acts on the category of shapes (with
arity-respecting renamings) along the J-functor that picks out the
variables of a given arity.  The codomain category is
`Arity → Type`.

* `J γ α` — the variables of arity `α` in shape `γ`.
* `T γ α := Expr (γ ⋈ α)` — expressions where the bound arity `α`
  has been encoded as the outermost extension of `γ`.

Entering an arg under a binder `β` sends `T γ α` to `T (γ ⋈ α) β` —
the old bound is absorbed into the free side, the new bound is `β`.
-/

/-- The variables of arity `α` in `γ`: slots of `γ` whose
    arity equals `α`. -/
def J {C : Carrier} (γ : C.Shape) (α : C.Arity) : Type :=
  { x : C.ShapeSlots γ // C.shapeArity γ x = α }

/-- The relative monad's target: expressions with free shape `γ` and
    outermost bound arity `α` are just expressions in the extended
    shape `γ ⋈ α`. -/
abbrev T {C : Carrier} (γ : C.Shape) (α : C.Arity) : Type :=
  Expr (γ ⋈ α)

/-! ## Helper lemmas for arity bookkeeping -/

/-- Lifting a γ-slot through the action preserves its arity. -/
private theorem shapeArity_symm_inl {C : Carrier} (γ : C.Shape)
    (α : C.Arity) (x : C.ShapeSlots γ) :
    C.shapeArity (γ ⋈ α) ((C.slotsExt γ α).symm (.inl x)) =
      C.shapeArity γ x := by
  rw [C.slotsExtCompat γ α]
  simp

/-- Reflecting a binder position as a bound-side slot of the extended
    shape gives a slot of the binder's arity. -/
private theorem shapeArity_symm_inr {C : Carrier} (γ : C.Shape)
    (α : C.Arity) (y : C.AritySlots α) :
    C.shapeArity (γ ⋈ α) ((C.slotsExt γ α).symm (.inr y)) =
      C.arityArity α y := by
  rw [C.slotsExtCompat γ α]
  simp

/-- Transport preservation for `arityArity`: applying `arityArity`
    to a value that has been transported along an arity equality
    yields the same arity as before the transport. -/
private theorem arityArity_eq_rec {C : Carrier}
    {a b : C.Arity} (h : a = b) (y : C.AritySlots a) :
    C.arityArity b (h ▸ y) = C.arityArity a y := by
  cases h
  rfl

/-- Construct an `Expr.apply` when the head's arity is known
propositionally rather than definitionally.

If the head `x` of a shape `γ` has propositional arity `α` (witness
`hα`), we may supply the children with their type stated in terms
of `α` directly — `applyAtArity` performs the transport along `hα`
that aligns these children with the constructor's child-type
`(γ ⋈ arityArity (shapeArity γ x) y)`. -/
def applyAtArity {C : Carrier} {γ : C.Shape}
    (x : C.ShapeSlots γ) (α : C.Arity)
    (hα : C.shapeArity γ x = α)
    (children : (y : C.AritySlots α) →
                Expr (γ ⋈ C.arityArity α y)) :
    Expr γ :=
  Expr.apply x (fun y =>
    (arityArity_eq_rec hα y) ▸ children (hα ▸ y))

/-! ## The unit `η`

`η γ α : J γ α → T γ α = Expr (γ ⋈ α)` η-expands a variable into a
fully-applied expression.

A variable `⟨x, hx⟩` of arity `α` in `γ` becomes `apply xHead
children`, where
* `xHead := (slotsExt γ α).symm (.inl x)` views `x` as the γ-side
  slot of `γ ⋈ α`, with arity `α` by `slotsExtCompat`;
* for each binder `y` of α, the child is the η-expansion of "the
  y-th binder of α", obtained by reflecting `y` as the bound-side
  slot of `γ ⋈ α` and recursing.

Termination descends along the sub-arity relation: each recursive
call uses `arityArity α y`, strictly smaller in `AritySub` —
witnessed by `⟨y, rfl⟩`. -/
def η {C : Carrier} :
    (γ : C.Shape) → (α : C.Arity) → J γ α → T γ α
  | γ, α, ⟨x, hx⟩ =>
    let xHead := (C.slotsExt γ α).symm (.inl x)
    have hHead : C.shapeArity (γ ⋈ α) xHead = α :=
      (shapeArity_symm_inl γ α x).trans hx
    applyAtArity xHead α hHead fun y =>
      let bound := (C.slotsExt γ α).symm (.inr y)
      η (γ ⋈ α) (C.arityArity α y) ⟨bound, shapeArity_symm_inr γ α y⟩
termination_by γ α _ => α
decreasing_by exact ⟨_, rfl⟩

/-! ## Renaming-action on expressions

The action of a renaming `f : γ →ʳ δ` on an expression sends each
slot through `f`; under each binder of arity `β_y`, the renaming
extends via `Renaming.extend` to handle the new bound variables.

This is the functorial action of the `T` functor in its Shape
argument: `T γ α = Expr (γ ⋈ α)` becomes a functor `Shape ⥤ Type`
once `rename` is in place. -/

/-- Action of a renaming on an expression. -/
def rename {C : Carrier} :
    {γ δ : C.Shape} → (γ →ʳ δ) → Expr γ → Expr δ
  | _, _, f, .apply x args =>
    applyAtArity (f.toFun x) (C.shapeArity _ x) (f.arity_preserving x)
      fun y => rename (f.extend (C.arityArity _ y)) (args y)

/-! ## Functoriality of `rename`

`rename` preserves identity and composition, making
`T γ α = Expr (γ ⋈ α)` a functor in its Shape argument. -/

/-- `applyAtArity` at a reflexive arity proof reduces to a plain
`Expr.apply`. -/
@[simp]
theorem applyAtArity_rfl {C : Carrier} {γ : C.Shape}
    (x : C.ShapeSlots γ)
    (children : (y : C.AritySlots (C.shapeArity γ x)) →
                Expr (γ ⋈ C.arityArity (C.shapeArity γ x) y)) :
    applyAtArity x (C.shapeArity γ x) rfl children = Expr.apply x children :=
  rfl

/-- Renaming commutes with `applyAtArity`: the proof at the
combined arity is the renaming's `arity_preserving` chained with
the original proof. -/
theorem rename_applyAtArity {C : Carrier} {γ' δ : C.Shape} (g : γ' →ʳ δ)
    (x : C.ShapeSlots γ') (α : C.Arity) (hα : C.shapeArity γ' x = α)
    (children : (y : C.AritySlots α) →
                Expr (γ' ⋈ C.arityArity α y)) :
    rename g (applyAtArity x α hα children) =
    applyAtArity (g.toFun x) α ((g.arity_preserving x).trans hα)
                 (fun y => rename (g.extend (C.arityArity α y)) (children y)) := by
  subst hα
  rfl

@[simp]
theorem rename_id {C : Carrier} :
    ∀ {γ : C.Shape} (e : Expr γ), rename (Renaming.id γ) e = e
  | _, .apply x args => by
    show applyAtArity x (C.shapeArity _ x) rfl
           (fun y => rename ((Renaming.id _).extend (C.arityArity _ y)) (args y))
         = Expr.apply x args
    have h : (fun y => rename ((Renaming.id _).extend (C.arityArity _ y)) (args y))
             = args := by
      funext y
      rw [Renaming.extend_id]
      exact rename_id (args y)
    rw [h]
    rfl

@[simp]
theorem rename_comp {C : Carrier} :
    ∀ {γ δ ε : C.Shape} (f : γ →ʳ δ) (g : δ →ʳ ε) (e : Expr γ),
      rename (Renaming.comp f g) e = rename g (rename f e)
  | _, _, _, f, g, .apply x args => by
    -- Unfold both sides into a common `applyAtArity` form, then peel off
    -- the head/arity/arity-proof (all definitionally equal) and prove the
    -- children equal pointwise via `extend_comp` and the IH.
    show applyAtArity ((Renaming.comp f g).toFun x) (C.shapeArity _ x)
            ((Renaming.comp f g).arity_preserving x)
            (fun y => rename ((Renaming.comp f g).extend (C.arityArity _ y)) (args y))
       = rename g (rename f (Expr.apply x args))
    rw [show rename f (Expr.apply x args)
          = applyAtArity (f.toFun x) (C.shapeArity _ x) (f.arity_preserving x)
              (fun y => rename (f.extend (C.arityArity _ y)) (args y)) from rfl,
        rename_applyAtArity]
    -- Both sides are now `applyAtArity` expressions agreeing on head,
    -- arity, and arity-proof (all definitionally equal); only children differ.
    congr 1
    funext y
    rw [Renaming.extend_comp]
    exact rename_comp _ _ (args y)

end Expr

end Action
