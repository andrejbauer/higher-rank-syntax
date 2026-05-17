import HigherRankSyntax.Action.Expr

/-!
# Substitution, instantiation, and the Kleisli extension

This file completes the relative-monad structure on `Expr` by
defining the Kleisli extension `lift` of a substitution.

Two distinct kinds of "replacement" data appear in the algorithm:

* a **substitution** replaces *free* variables — slots of a shape
  γ — by expressions (`Subst γ δ`);
* an **instantiation** replaces *bound* variables — slots of an
  arity α — by expressions (`Inst α γ`).

Each is concrete data: a dependent function from slots to
expressions of matching arity.  The α-indexed natural-transformation
form (used for the categorical relative-monad structure) is a
derived view, recoverable when needed.

The Kleisli extension `lift : Subst γ δ → (α : Arity) → Expr.T γ α
→ Expr.T δ α` is built from two internal recursions:

* `lift.aux σ τ e` walks a τ-stack of binders into `e`, structurally
  recursive on `e`.  At a γ-slot it invokes `σ` and feeds the
  recursively substituted children into `inst`.

* `inst α τ i τ' e` realises the action of an instantiation on an
  expression: `i : Inst α (γ ⋈* τ)` substitutes the α-binders of
  `e : Expr ((γ ⋈ α) ⋈* τ')` to produce `Expr ((γ ⋈* τ) ⋈* τ')`.
  Well-founded recursion on `α` via `Carrier.aritySubWf`, with
  structural recursion on `e` inside each α-step.
-/

namespace Action

/-! ## Substitutions and instantiations -/

/-- A substitution from `γ` to `δ`: a dependent function sending
each γ-slot `s` to an expression in `δ` of arity matching `s`.
Concretely the data of a Kleisli morphism in the relative monad on
`Expr`; the α-indexed `J γ α ⟶ T δ α` form is derived. -/
abbrev Subst {C : Carrier} (γ δ : C.Shape) : Type :=
  (s : C.ShapeSlots γ) → Expr (δ ⋈ C.shapeArity γ s)

/-- An instantiation of the binders of an arity `α` into a shape
`γ`: a dependent function sending each binder slot `z` of `α` to an
expression in `γ` of arity `arityArity α z`.  The arity-source
analogue of `Subst`. -/
abbrev Inst {C : Carrier} (α : C.Arity) (γ : C.Shape) : Type :=
  (z : C.AritySlots α) → Expr (γ ⋈ C.arityArity α z)

/-! ## Head-slot classification

`inst` and `lift.aux` decide where the head slot of an expression
lies: in the "free" part of the shape (a γ-slot or a τ-binder, both
surviving into the target shape), or in the "to be substituted"
part (α-binders for `inst`, γ-slots themselves for `lift.aux`).
The classification carries an arity-preservation equation so the
reassembled `apply'` type-checks. -/

/-- Classification for `inst`: a head slot of `(γ ⋈ α) ⋈* τ'` is
either an α-binder, or a slot of `(γ ⋈* τ) ⋈* τ'` (the lifted image
of a γ-slot or τ'-binder, with the γ-side weakened through τ to
land in the target shape). -/
inductive ClassifiedInst {C : Carrier} (γ : C.Shape) (α : C.Arity)
    (τ τ' : List C.Arity) (target_arity : C.Arity) : Type where
  | inExt (s : C.ShapeSlots ((γ ⋈* τ) ⋈* τ'))
          (h : C.shapeArity ((γ ⋈* τ) ⋈* τ') s = target_arity) :
      ClassifiedInst γ α τ τ' target_arity
  | inAlpha (z : C.AritySlots α)
            (h : C.arityArity α z = target_arity) :
      ClassifiedInst γ α τ τ' target_arity

/-- Classification for `lift.aux`: a head slot of `γ ⋈* τ` is
either a γ-slot (to be substituted by the Kleisli morphism) or a
τ-binder (which stays as a slot of `δ ⋈* τ`). -/
inductive ClassifiedLift {C : Carrier} (γ δ : C.Shape)
    (τ : List C.Arity) (target_arity : C.Arity) : Type where
  | inGamma (p : C.ShapeSlots γ)
            (h : C.shapeArity γ p = target_arity) :
      ClassifiedLift γ δ τ target_arity
  | inLifted (s : C.ShapeSlots (δ ⋈* τ))
             (h : C.shapeArity (δ ⋈* τ) s = target_arity) :
      ClassifiedLift γ δ τ target_arity

/-- Classify a head slot in `(γ ⋈ α) ⋈* τ'`.  Walks τ' from the
outside in, splitting at each τ'-layer via `slotsExt`; once τ' is
exhausted, splits the bottom against `γ ⋈ α` via `slotsExt γ α`.
γ-slots get weakened through `τ` (the output context) to land in
`(γ ⋈* τ) ⋈* τ'`; τ'-binders keep their position; α-binders are
reported as `inAlpha`. -/
def classifyInst {C : Carrier} {γ : C.Shape} (α : C.Arity)
    (τ : List C.Arity) :
    (τ' : List C.Arity) → (x : C.ShapeSlots ((γ ⋈ α) ⋈* τ')) →
    ClassifiedInst γ α τ τ' (C.shapeArity ((γ ⋈ α) ⋈* τ') x)
  | [], x =>
    match h : C.slotsExt γ α x with
    | .inl q =>
        .inExt ((Renaming.weakenList γ τ) q)
          (((Renaming.weakenList γ τ).arity_preserving q).trans
            (Carrier.shapeArity_of_slotsExt_inl h).symm)
    | .inr z =>
        .inAlpha z (Carrier.shapeArity_of_slotsExt_inr h).symm
  | β_0 :: rest, x =>
    match h : C.slotsExt ((γ ⋈ α) ⋈* rest) β_0 x with
    | .inr z =>
        .inExt (Carrier.inrSlot ((γ ⋈* τ) ⋈* rest) β_0 z)
          ((Carrier.shapeArity_inrSlot ((γ ⋈* τ) ⋈* rest) β_0 z).trans
            (Carrier.shapeArity_of_slotsExt_inr h).symm)
    | .inl q =>
        match classifyInst α τ rest q with
        | .inExt s h_s =>
            .inExt (Carrier.inlSlot ((γ ⋈* τ) ⋈* rest) β_0 s)
              ((Carrier.shapeArity_inlSlot ((γ ⋈* τ) ⋈* rest) β_0 s).trans
                (h_s.trans (Carrier.shapeArity_of_slotsExt_inl h).symm))
        | .inAlpha z h_z =>
            .inAlpha z (h_z.trans (Carrier.shapeArity_of_slotsExt_inl h).symm)

/-- Classify a head slot in `γ ⋈* τ` by walking τ. -/
def classifyLift {C : Carrier} {γ : C.Shape} (δ : C.Shape) :
    (τ : List C.Arity) → (x : C.ShapeSlots (γ ⋈* τ)) →
    ClassifiedLift γ δ τ (C.shapeArity (γ ⋈* τ) x)
  | [], x => .inGamma x rfl
  | β_0 :: rest, x =>
    match h : C.slotsExt (γ ⋈* rest) β_0 x with
    | .inr z =>
        .inLifted (Carrier.inrSlot (δ ⋈* rest) β_0 z)
          ((Carrier.shapeArity_inrSlot (δ ⋈* rest) β_0 z).trans
            (Carrier.shapeArity_of_slotsExt_inr h).symm)
    | .inl q =>
        match classifyLift δ rest q with
        | .inGamma p h_p =>
            .inGamma p (h_p.trans (Carrier.shapeArity_of_slotsExt_inl h).symm)
        | .inLifted s h_s =>
            .inLifted (Carrier.inlSlot (δ ⋈* rest) β_0 s)
              ((Carrier.shapeArity_inlSlot (δ ⋈* rest) β_0 s).trans
                (h_s.trans (Carrier.shapeArity_of_slotsExt_inl h).symm))

/-! ## The instantiation operation

`inst α τ i τ' e` substitutes the α-binders of `e` by `i`, producing
an expression in the target context.  Well-founded recursion on `α`
via `aritySubWf`; structural recursion on `e` inside each α-step. -/

/-- Realise an instantiation on an expression.  Two kinds of
recursive calls, both decreasing in the lex order on
`(α, ⟨_, e⟩)`:
* children-descent (`α` unchanged, `e` shrinks structurally via
  `Expr.Subterm.of_arg`);
* α-binder encounter (`α` strictly smaller via `Carrier.aritySubWf`
  with witness `z`).
The α-binder substitute is `i z`, transported along
`arityArity α z = α_h` to match the head's arity from the apply'
destructure. -/
def inst {C : Carrier} {γ : C.Shape} (α : C.Arity) (τ : List C.Arity)
    (i : Inst α (γ ⋈* τ)) (τ' : List C.Arity)
    (e : Expr ((γ ⋈ α) ⋈* τ')) : Expr ((γ ⋈* τ) ⋈* τ') :=
  match e with
  | .apply' x α_h h_α_h args =>
      let new_args : (y : C.AritySlots α_h) →
                     Expr (((γ ⋈* τ) ⋈* τ') ⋈ C.arityArity α_h y) :=
        fun y => inst α τ i (C.arityArity α_h y :: τ') (args y)
      match classifyInst α τ τ' x with
      | .inExt s h_s =>
          Expr.apply' s α_h (h_s.trans h_α_h) new_args
      | .inAlpha z h_z =>
          let replacement : Expr ((γ ⋈* τ) ⋈ α_h) :=
            h_z.trans h_α_h ▸ i z
          inst (γ := γ ⋈* τ) α_h τ' new_args [] replacement
termination_by (α, Sigma.mk _ e)
decreasing_by
  all_goals first
    | exact Prod.Lex.right _ (Expr.Subterm.of_arg _ _ _ _ _)
    | exact Prod.Lex.left _ _ ⟨z, h_z.trans h_α_h⟩

/-! ## The lift-walk operation

Structural recursion on `e`.  At a γ-slot it invokes `σ` for the
replacement and feeds the recursively substituted children into
`inst`.  The σ-image at slot `p` is `σ p : Expr (δ ⋈ shapeArity γ p)`
and gets transported along `shapeArity γ p = α_h` to match the
head's arity from the apply' destructure. -/

/-- Walk a τ-stack into `e`, substituting γ-slots by `σ`.  The only
recursive call is the children-descent (`e` shrinks structurally
via `Expr.Subterm.of_arg`); the γ-slot branch delegates to `inst`. -/
def lift.aux {C : Carrier} {γ δ : C.Shape} (σ : Subst γ δ)
    (τ : List C.Arity) (e : Expr (γ ⋈* τ)) : Expr (δ ⋈* τ) :=
  match e with
  | .apply' x α_h h_α_h args =>
      let new_args : (y : C.AritySlots α_h) →
                     Expr ((δ ⋈* τ) ⋈ C.arityArity α_h y) :=
        fun y => lift.aux σ (C.arityArity α_h y :: τ) (args y)
      match classifyLift δ τ x with
      | .inLifted s h_s =>
          Expr.apply' s α_h (h_s.trans h_α_h) new_args
      | .inGamma p h_p =>
          let replacement : Expr (δ ⋈ α_h) := h_p.trans h_α_h ▸ σ p
          inst (γ := δ) α_h τ new_args [] replacement
termination_by Sigma.mk _ e
decreasing_by exact Expr.Subterm.of_arg _ _ _ _ _

/-! ## The Kleisli extension -/

/-- Kleisli extension of a substitution.  Given `σ : Subst γ δ` and
an arity `α`, lift `σ` to a map `Expr.T γ α → Expr.T δ α`.  This is
the relative-monad's extension operator. -/
def lift {C : Carrier} {γ δ : C.Shape} (σ : Subst γ δ)
    (α : C.Arity) (e : Expr.T γ α) : Expr.T δ α :=
  lift.aux σ [α] e

end Action
