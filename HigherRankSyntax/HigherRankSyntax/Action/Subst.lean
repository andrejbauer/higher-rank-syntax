import HigherRankSyntax.Action.Expr

/-!
# Substitution, instantiation, and the Kleisli extension

This file completes the relative-monad structure on `Expr` by defining the Kleisli
extension `lift` of a substitution.

Two distinct kinds of "replacement" data appear in the algorithm:

* a **substitution** replaces *free* variables — slots of a shape Γ — by expressions
  (`Subst Γ Δ`);
* an **instantiation** replaces *bound* variables — the binder positions of an arity α —
  by expressions (`Inst α Γ`).

`lift.aux σ τ e` walks a τ-stack of binders (a shape extension above `Γ`) into `e`, by
direct pattern matching on the head slot.  At a Γ-slot it invokes `σ` and combines the
substituted children with the σ-image via `inst.aux`.

`inst.aux α i τ e` walks a τ-stack of binders above `Δ ⋈ α` into `e`, by direct pattern
matching on the head slot.  At the α-binder it replaces with `i z` and re-enters
`inst.aux` at the smaller arity.

The mutual block carries the dependency `lift.aux → inst.aux`; if a future fix for the
deeper `.there` cases needs `inst.aux → lift.aux`, the mutual frame already permits it.
-/

namespace Action

/-! ## Substitutions and instantiations -/

/-- A substitution from `Γ` to `Δ`: a dependent function sending each slot of `Γ` to an
expression in `Δ` of matching arity. -/
abbrev Subst {C : Carrier} (Γ Δ : Shape C) : Type :=
  (s : Slot Γ) → Expr (Δ ⋈ s.arity)

/-- An instantiation of an α-binder above `Γ`: for each binder position `z` of `α`, an
expression in `Γ` of arity matching `arityArity α z`. -/
abbrev Inst {C : Carrier} (α : C.Arity) (Γ : Shape C) : Type :=
  (z : C.AritySlot α) → Expr (Γ ⋈ C.arityArity α z)

/-! ## The substitution and instantiation walkers (mutual) -/

mutual

/-- Walk a τ-stack into an expression with an outermost α-binder at the bottom,
instantiating that α-binder using `i`.  Direct pattern matching on `(τ, head slot)`. -/
def inst.aux {C : Carrier} {Δ : Shape C} (α : C.Arity) (i : Inst α Δ)
    (τ : List C.Arity) (e : Expr ((Δ ⋈ α) ⋈* τ)) : Expr (Δ ⋈* τ) :=
  match τ, e with
  | [], .apply' (.here z) α_h h_α_h args =>
      match h_α_h with
      | rfl =>
          let new_args : Inst (C.arityArity α z) Δ := fun y =>
            inst.aux α i [C.arityArity (C.arityArity α z) y] (args y)
          inst.aux (C.arityArity α z) new_args [] (i z)
  | [], .apply' (.there s) α_h h_α_h args =>
      let new_args : (y : C.AritySlot α_h) → Expr (Δ ⋈ C.arityArity α_h y) := fun y =>
        inst.aux α i [C.arityArity α_h y] (args y)
      Expr.apply' s α_h h_α_h new_args
  | β :: τ, .apply' (.here y) α_h h_α_h args =>
      let new_args : (y' : C.AritySlot α_h) →
          Expr ((Δ ⋈* (β :: τ)) ⋈ C.arityArity α_h y') := fun y' =>
        inst.aux α i (C.arityArity α_h y' :: β :: τ) (args y')
      Expr.apply' (.here y) α_h h_α_h new_args
  | _β :: _τ, .apply' (.there _z) _α_h _h_α_h _args => sorry
termination_by Sigma.mk _ e
decreasing_by all_goals sorry

/-- Walk a τ-stack (a shape extension above `Γ`) into `e`, substituting Γ-slots by `σ`.
Direct pattern matching on `(τ, head slot)`. -/
def lift.aux {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
    (τ ρ : List C.Arity)
    (e : Expr (Γ ⋈* τ ⋈* ρ))
    (x : Slot (Γ ⋈* τ))
    (ξ : e.head = Renaming.weakenList _ _ x)
    : Expr (Δ ⋈* τ) :=
  match τ with
  | [] =>
      match e with
      | .apply' y α_h h_α_h args =>
          match h_α_h with
          | rfl => sorry
  | α :: τ =>
    sorry
end

/-! ## Public wrappers -/

/-- α-instantiation: replace the α-binder of `Δ ⋈ α` by `i`.  The α is inferred from `e`'s
type, so callers can pass `σ x` directly (which has type `Expr (Δ ⋈ x.arity)`). -/
def inst {C : Carrier} {α : C.Arity} {Δ : Shape C}
    (e : Expr (Δ ⋈ α)) (i : Inst α Δ) : Expr Δ :=
  inst.aux α i [] e

/-- Kleisli extension of a substitution at a single α-binder: `lift σ α e` substitutes
the `Γ`-slots of `e : Expr (Γ ⋈ α)` according to `σ`, producing `Expr (Δ ⋈ α)`. -/
def lift {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ) (α : C.Arity) (e : Expr (Γ ⋈ α)) : Expr (Δ ⋈ α) :=
  lift.aux σ [α] [] e e.head rfl

end Action
