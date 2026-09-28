import HigherRankSyntax.HrS.Structure
import HigherRankSyntax.ListCarrier

/-!
# Chains of types

A chain over an object `Γ` of a model is a finite sequence of types, each over `Γ`
extended by the ones before it. Its last object is `Γ` extended by all of them in
turn. Iterating the operations of the model along a chain gives the projection from
the last object back to `Γ`, the binding of a type over the last object into a type
over `Γ`, and `lam` and `unlam` between the terms of the two.

Reindexing a chain along a substitution into `Γ` reindexes its first type along the
substitution, and the rest of the chain along the substitution lifted through the
extension by the first type. The lift of the substitution through the whole chain
goes from the last object of the reindexed chain to the last object of the chain.
-/

universe u

namespace HrS

variable {M : Structure.{u}}

variable (M) in
/-- A chain of types over `Γ`: either empty, or a type `A` over `Γ` followed by a
chain over `Γ` extended by `A`. The arity index has one slot per type, the first
type's slot being `C.single α`; the chain places no condition on `α`. -/
inductive Chain : M.Ob → C.Arity → Type u
  | nil {Γ : M.Ob} : Chain Γ 1
  | cons {Γ : M.Ob} {α Ω : C.Arity} (A : M.Ty Γ) (c : Chain (M.extend Γ A) Ω) :
      Chain Γ (C.single α ⋈ Ω)

namespace Chain

/-- The object at the end of a chain: its base extended by each of its types in
turn. -/
def last : {Γ : M.Ob} → {Ω : C.Arity} → Chain M Γ Ω → M.Ob
  | Γ, _, .nil => Γ
  | _, _, .cons _ c => c.last

/-- The substitution from the end of a chain back to its base: the composite of the
projections off each of its types. -/
def projection : {Γ : M.Ob} → {Ω : C.Arity} → (c : Chain M Γ Ω) → M.Sub c.last Γ
  | Γ, _, .nil => M.identity Γ
  | _, _, .cons A c => M.comp (M.projection A) c.projection

/-- A type `B` over the end of a chain, bound over each of the chain's types in turn:
a type over the base. -/
def Bind : {Γ : M.Ob} → {Ω : C.Arity} → (c : Chain M Γ Ω) → M.Ty c.last → M.Ty Γ
  | _, _, .nil, B => B
  | _, _, .cons A c, B => M.Bind A (c.Bind B)

/-- A term over the end of a chain, read as a term of the bound type over the base:
`lam` once for each type of the chain. -/
def lam : {Γ : M.Ob} → {Ω : C.Arity} → (c : Chain M Γ Ω) → {B : M.Ty c.last} →
    M.Tm c.last B → M.Tm Γ (c.Bind B)
  | _, _, .nil, _, t => t
  | _, _, .cons _ c, _, t => M.lam (c.lam t)

/-- A term of a bound type over the base, read as a term over the end of the chain:
`unlam` once for each type of the chain. -/
def unlam : {Γ : M.Ob} → {Ω : C.Arity} → (c : Chain M Γ Ω) → {B : M.Ty c.last} →
    M.Tm Γ (c.Bind B) → M.Tm c.last B
  | _, _, .nil, _, t => t
  | _, _, .cons _ c, _, t => c.unlam (M.unlam t)

/-- `lam` after `unlam` along a chain is the identity. -/
theorem lam_unlam :
    ∀ {Γ : M.Ob} {Ω : C.Arity} (c : Chain M Γ Ω) {B : M.Ty c.last} (t : M.Tm Γ (c.Bind B)),
      c.lam (c.unlam t) = t
  | _, _, .nil, _, _ => rfl
  | _, _, .cons _ c, _, t => by
      rw [lam, unlam, lam_unlam c, M.lam_unlam]

/-- `unlam` after `lam` along a chain is the identity. -/
theorem unlam_lam :
    ∀ {Γ : M.Ob} {Ω : C.Arity} (c : Chain M Γ Ω) {B : M.Ty c.last} (t : M.Tm c.last B),
      c.unlam (c.lam t) = t
  | _, _, .nil, _, _ => rfl
  | _, _, .cons _ c, _, t => by
      rw [lam, unlam, M.unlam_lam, unlam_lam c]

/-- A chain over `Γ` reindexed along `σ : Sub Δ Γ`: its first type reindexed along
`σ`, followed by the rest reindexed along `σ` lifted through the extension by the
first type. -/
def subst : {Γ Δ : M.Ob} → {Ω : C.Arity} → Chain M Γ Ω → M.Sub Δ Γ → Chain M Δ Ω
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons A c, σ => .cons (M.substTy A σ) (c.subst (M.lift A σ))

/-- `σ` lifted through every type of a chain: the substitution from the end of the
reindexed chain to the end of the chain. -/
def lift : {Γ Δ : M.Ob} → {Ω : C.Arity} → (c : Chain M Γ Ω) → (σ : M.Sub Δ Γ) →
    M.Sub (c.subst σ).last c.last
  | _, _, _, .nil, σ => σ
  | _, _, _, .cons A c, σ => c.lift (M.lift A σ)

/-- Lifting `σ` through a chain and then projecting to the base is projecting the
reindexed chain to its base and then applying `σ`. -/
theorem projection_lift :
    ∀ {Γ Δ : M.Ob} {Ω : C.Arity} (c : Chain M Γ Ω) (σ : M.Sub Δ Γ),
      M.comp c.projection (c.lift σ) = M.comp σ (c.subst σ).projection
  | _, _, _, .nil, σ => by
      apply Eq.trans (M.identity_comp σ)
      symm
      apply M.comp_identity
  | _, _, _, .cons A c, σ =>
      calc M.comp (M.comp (M.projection A) c.projection) (c.lift (M.lift A σ))
          = M.comp (M.projection A) (M.comp c.projection (c.lift (M.lift A σ))) := by
            rw [M.comp_assoc]
        _ = M.comp (M.projection A)
              (M.comp (M.lift A σ) (c.subst (M.lift A σ)).projection) := by
            rw [projection_lift c]
        _ = M.comp (M.comp σ (M.projection (M.substTy A σ)))
              (c.subst (M.lift A σ)).projection := by
            rw [← M.comp_assoc, Structure.projection_lift]
        _ = M.comp σ
              (M.comp (M.projection (M.substTy A σ)) (c.subst (M.lift A σ)).projection) := by
            rw [M.comp_assoc]

/-- Reindexing a bound type along `σ` is binding the reindexed chain at the type
reindexed along the lift of `σ` through the chain. -/
theorem Bind_subst :
    ∀ {Γ Δ : M.Ob} {Ω : C.Arity} (c : Chain M Γ Ω) (B : M.Ty c.last) (σ : M.Sub Δ Γ),
      M.substTy (c.Bind B) σ = (c.subst σ).Bind (M.substTy B (c.lift σ))
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, .cons A c, B, σ => by
      rw [Bind, M.Bind_subst]
      apply congrArg (M.Bind (M.substTy A σ))
      apply Bind_subst

/-- `unlam` along a chain commutes with reindexing: reindexing the unbound term along
the lift of `σ` is unbinding the term reindexed along `σ`. -/
theorem unlam_subst :
    ∀ {Γ Δ : M.Ob} {Ω : C.Arity} (c : Chain M Γ Ω) {B : M.Ty c.last}
      (t : M.Tm Γ (c.Bind B)) (σ : M.Sub Δ Γ),
      M.substTm (c.unlam t) (c.lift σ) = (c.subst σ).unlam (c.Bind_subst B σ ▸ M.substTm t σ)
  | _, _, _, .nil, _, _, _ => rfl
  | _, _, _, .cons A c, B, t, σ => by
      apply Eq.trans (unlam_subst c (M.unlam t) (M.lift A σ))
      apply congrArg (c.subst (M.lift A σ)).unlam
      apply eq_of_heq
      apply HEq.trans (eqRec_heq _ _)
      symm
      apply HEq.trans (b := M.unlam (M.lam (M.substTm (M.unlam t) (M.lift A σ))))
      · congr 1
        · symm
          apply Bind_subst
        · apply HEq.trans (eqRec_heq _ _)
          apply HEq.trans _ (heq_of_eq (M.lam_subst (M.unlam t) σ))
          rw [M.lam_unlam]
          symm
          apply eqRec_heq
      · rw [M.unlam_lam]

/-- `lam` along a chain commutes with reindexing: reindexing the bound term along `σ`
is binding the term reindexed along the lift of `σ`. -/
theorem lam_subst
    {Γ Δ : M.Ob} {Ω : C.Arity} (c : Chain M Γ Ω) {B : M.Ty c.last} (t : M.Tm c.last B)
    (σ : M.Sub Δ Γ) :
  c.Bind_subst B σ ▸ M.substTm (c.lam t) σ = (c.subst σ).lam (M.substTm t (c.lift σ))
  := by
  have h := unlam_subst c (c.lam t) σ
  rw [unlam_lam] at h
  rw [h, lam_unlam]

/-- Reindexing a chain along a composite is reindexing it along each factor in
turn. -/
theorem subst_comp :
    ∀ {Γ Δ Ξ : M.Ob} {Ω : C.Arity} (c : Chain M Γ Ω) (σ : M.Sub Δ Γ) (θ : M.Sub Ξ Δ),
      c.subst (M.comp σ θ) = (c.subst σ).subst θ
  | _, _, _, _, .nil, _, _ => rfl
  | _, _, _, _, .cons A c, σ, θ => by
      rw [subst, subst, subst, ← subst_comp c]
      congr 1
      · apply M.substTy_comp
      · congr 1
        · rw [M.substTy_comp]
        · apply Structure.lift_comp

/-- The lift of a composite through a chain is the composite of the lifts. The two
sides have domains that are equal by `subst_comp`. -/
theorem lift_comp :
    ∀ {Γ Δ Ξ : M.Ob} {Ω : C.Arity} (c : Chain M Γ Ω) (σ : M.Sub Δ Γ) (θ : M.Sub Ξ Δ),
      HEq (c.lift (M.comp σ θ)) (M.comp (c.lift σ) ((c.subst σ).lift θ))
  | _, _, _, _, .nil, _, _ => HEq.rfl
  | _, _, _, _, .cons A c, σ, θ => by
      apply HEq.trans _ (lift_comp c (M.lift A σ) (M.lift (M.substTy A σ) θ))
      rw [lift]
      congr 1
      · rw [M.substTy_comp]
      · apply Structure.lift_comp

/-- Reindexing a chain along the identity leaves it unchanged. -/
theorem subst_identity :
    ∀ {Γ : M.Ob} {Ω : C.Arity} (c : Chain M Γ Ω), c.subst (M.identity Γ) = c
  | _, _, .nil => rfl
  | _, _, .cons A c => by
      rw [subst]
      congr 1
      · apply M.substTy_identity
      · apply HEq.trans _ (heq_of_eq (subst_identity c))
        congr 1
        · rw [M.substTy_identity]
        · apply Structure.lift_identity

/-- The lift of the identity through a chain is the identity. The two sides have
domains that are equal by `subst_identity`. -/
theorem lift_identity :
    ∀ {Γ : M.Ob} {Ω : C.Arity} (c : Chain M Γ Ω),
      HEq (c.lift (M.identity Γ)) (M.identity c.last)
  | _, _, .nil => HEq.rfl
  | _, _, .cons A c => by
      simp only [lift, subst]
      apply HEq.trans _ (lift_identity c)
      congr 1
      · rw [M.substTy_identity]
      · apply Structure.lift_identity

end Chain

end HrS
