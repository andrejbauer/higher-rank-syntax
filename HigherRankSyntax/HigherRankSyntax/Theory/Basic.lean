import Mathlib.CategoryTheory.Comma.Over.Basic
import HigherRankSyntax.Ctx.Model
import HigherRankSyntax.Initiality.Chain

/-!
# Theories

`Ctx.entry Γ x` is the class over `Γ` of the entry of the slot `x`: its binding and
declaration, weakened into all of `Γ`.

A theory is a signature together with, for each object `X` of the slice of the context
classes over the signature, a predicate on the types over `X.left`: the admissible types
over `X`. Admissibility is stable under the maps of the slice.

A schema over a signature is an object of the slice over it together with a type over its
domain. `Theory.ofSchemas` is the theory whose admissible types are the types of a family of
schemas reindexed along the maps of the slice.

`Theory.AdmissibleChain κ c` says that every type of the chain `c` over `Y` is admissible
over the extension of `Y` by the types before it, mapped to the signature by the
projections followed by `κ`.
-/

open CategoryTheory

universe u

namespace Ctx

/-- The class of the entry binding what the slot `x` of `Γ` binds and declaring what it
declares, over `Γ`. -/
def entry (Γ : Ctx) {α : C.Arity} (x : Γ.arity ∋ α) : Ty₁ Γ.toOb :=
  Quotient.mk _
    { arity := α
      binding := Γ.ambient.binding x
      declaration := Γ.ambient.declaration x
      wf := Wf_t.cons (Wf_t.binding Γ.wf x) (Wf_t.declaration Γ.wf x) Wf_t.nil }

end Ctx

/-- A signature, together with, for each object `X` of the slice over the signature, a
predicate on the types over `X.left`, stable under the maps of the slice. -/
structure Theory where
  /-- The signature. -/
  signature : Ctx
  /-- The admissible types over `X.left`. -/
  admissible : (X : Over signature.toOb) → Ctx.model.Ty X.left → Prop
  /-- A type admissible over `Y`, reindexed along a map `σ : X ⟶ Y` of the slice, is
  admissible over `X`. -/
  admissible_subst : ∀ {X Y : Over signature.toOb} (σ : X ⟶ Y) {a : Ctx.model.Ty Y.left},
    admissible Y a → admissible X (Ctx.model.substTy a σ.left)

namespace Theory

/-- An object of the slice over `Ξ`, together with a type over its domain. -/
structure Schema (Ξ : Ctx) where
  /-- The object of the slice. -/
  context : Over Ξ.toOb
  /-- The type over the domain of `context`. -/
  type : Ctx.model.Ty context.left

/-- The theory with signature `Ξ` whose admissible types over `X` are the types of the
schemas reindexed along the maps of the slice from `X` to their contexts. -/
def ofSchemas (Ξ : Ctx) {ι : Type u} (schema : ι → Schema Ξ) : Theory where
  signature := Ξ
  admissible X a := ∃ (i : ι) (σ : X ⟶ (schema i).context),
    Ctx.model.substTy (schema i).type σ.left = a
  admissible_subst := by
    rintro X Y σ a ⟨i, θ, rfl⟩
    use i, σ ≫ θ
    apply Ctx.model.substTy_comp

/-- Every type of the chain `c` is admissible over the extension of `Y` by the types before
it, mapped to the signature by the projections followed by `κ`. -/
def AdmissibleChain (T : Theory) : {Y : Ctx.Ob} → {Ω : C.Arity} →
    (Y ⟶ T.signature.toOb) → HrS.Chain Ctx.model Y Ω → Prop
  | _, _, _, .nil => True
  | _, _, κ, .cons a c => T.admissible (Over.mk κ) a ∧
      AdmissibleChain T (Ctx.model.projection a ≫ κ) c

end Theory
