import HigherRankSyntax.PrefixedSyntaxMonad

/-!
# Equation presentations over fixed-prefix syntax

An equation presentation fixes a signature arity `S`.  A schema relates two
raw expressions over `S ⋈ Γ ⋈ Φ` of the same coarse class.  The slots in `Γ`
are substitutable metavariables, while `Φ` consists of local variables that
remain fixed when the schema is instantiated.

This layer only declares equations between raw expressions.  It does not
quotient syntax or introduce typing and well-formedness judgments.
-/

variable {A : Type} {C : Carrier A}

namespace Equations

/-- Raw fixed-signature terms with metavariable context `Γ` and local context
`Φ`. -/
abbrev STerm (S Γ Φ : C.Arity) (τ : C.Ty) := Expr (S ⋈ Γ ⋈ Φ) τ

/-- A family of equation schemas over the fixed signature prefix `S`. -/
structure EquationPresentation (C : Carrier A) (S : C.Arity) where
  axioms : {Γ Φ : C.Arity} → {τ : C.Ty} →
    STerm S Γ Φ τ → STerm S Γ Φ τ → Prop

end Equations
