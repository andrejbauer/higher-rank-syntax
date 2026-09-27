/-!
# Models of the framework

A model of the framework `HrS` has four sorts: objects, substitutions between
two objects, types over an object, and terms of a type over an object.  Its
operations and their laws come in four groups: a category with a terminal
object, reindexing and context extension; a universe of sorts with its decoding
into types of elements; binding, a type over an extension read as a type over
the base, with a bijection on terms; and extensional equality types of sorts
and of elements of a sort.

Lifting a substitution through an extension is not an operation of its own: it is
derived from pairing, at the end of the file, together with its laws. The end of the
file also restates the reindexing laws of terms for reindexed terms transported along
equations of types.
-/

universe u

namespace HrS

/-- A model of the framework. -/
structure Structure where
  /-- The objects. -/
  Ob : Type u
  /-- The substitutions from one object to another. -/
  Sub : Ob → Ob → Type u
  /-- The types over an object. -/
  Ty : Ob → Type u
  /-- The terms of a type over an object. -/
  Tm : (Γ : Ob) → Ty Γ → Type u
  -- A category with a terminal object
  /-- The identity substitution. -/
  identity : (Γ : Ob) → Sub Γ Γ
  /-- The composite of two substitutions. -/
  comp : {Γ Δ Ξ : Ob} → Sub Δ Γ → Sub Ξ Δ → Sub Ξ Γ
  /-- Composition is associative. -/
  comp_assoc : ∀ {Γ Δ Ξ Ψ : Ob} (σ : Sub Δ Γ) (θ : Sub Ξ Δ) (κ : Sub Ψ Ξ),
    comp (comp σ θ) κ = comp σ (comp θ κ)
  /-- The identity is a left unit. -/
  identity_comp : ∀ {Γ Δ : Ob} (σ : Sub Δ Γ), comp (identity Γ) σ = σ
  /-- The identity is a right unit. -/
  comp_identity : ∀ {Γ Δ : Ob} (σ : Sub Δ Γ), comp σ (identity Δ) = σ
  /-- The terminal object. -/
  empty : Ob
  /-- The substitution into the empty object. -/
  toEmpty : (Γ : Ob) → Sub Γ empty
  /-- Every substitution into the empty object is `toEmpty`. -/
  toEmpty_unique : ∀ {Γ : Ob} (σ : Sub Γ empty), σ = toEmpty Γ
  -- Reindexing
  /-- A type reindexed along a substitution. -/
  substTy : {Γ Δ : Ob} → Ty Γ → Sub Δ Γ → Ty Δ
  /-- A term reindexed along a substitution. -/
  substTm : {Γ Δ : Ob} → {a : Ty Γ} → Tm Γ a → (σ : Sub Δ Γ) →
    Tm Δ (substTy a σ)
  /-- Reindexing a type along the identity leaves it unchanged. -/
  substTy_identity : ∀ {Γ : Ob} (a : Ty Γ), substTy a (identity Γ) = a
  /-- Reindexing a term along the identity leaves it unchanged. -/
  substTm_identity : ∀ {Γ : Ob} {a : Ty Γ} (t : Tm Γ a),
    substTy_identity a ▸ substTm t (identity Γ) = t
  /-- Reindexing a type along `comp σ θ` is reindexing it along `σ`, then along
  `θ`. -/
  substTy_comp : ∀ {Γ Δ Ξ : Ob} (a : Ty Γ) (σ : Sub Δ Γ) (θ : Sub Ξ Δ),
    substTy a (comp σ θ) = substTy (substTy a σ) θ
  /-- Reindexing a term along `comp σ θ` is reindexing it along `σ`, then along
  `θ`. -/
  substTm_comp : ∀ {Γ Δ Ξ : Ob} {a : Ty Γ} (t : Tm Γ a) (σ : Sub Δ Γ)
      (θ : Sub Ξ Δ),
    substTy_comp a σ θ ▸ substTm t (comp σ θ) = substTm (substTm t σ) θ
  -- Extension
  /-- An object extended by a type over it. -/
  extend : (Γ : Ob) → Ty Γ → Ob
  /-- The projection off an extension. -/
  projection : {Γ : Ob} → (a : Ty Γ) → Sub (extend Γ a) Γ
  /-- The generic term over the extension by `a`, of type `a` reindexed along the
  projection. -/
  generic : {Γ : Ob} → (a : Ty Γ) → Tm (extend Γ a) (substTy a (projection a))
  /-- A substitution paired with a term of the type reindexed along it, as a
  substitution into the extension. -/
  pair : {Γ Δ : Ob} → {a : Ty Γ} → (σ : Sub Δ Γ) → Tm Δ (substTy a σ) →
    Sub Δ (extend Γ a)
  /-- The projection after `pair σ t` is `σ`. -/
  projection_pair : ∀ {Γ Δ : Ob} {a : Ty Γ} (σ : Sub Δ Γ)
      (t : Tm Δ (substTy a σ)),
    comp (projection a) (pair σ t) = σ
  /-- The generic term reindexed along `pair σ t` is `t`. -/
  generic_pair : ∀ {Γ Δ : Ob} {a : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (substTy a σ)),
    HEq (substTm (generic a) (pair σ t)) t
  /-- The projection paired with the generic term is the identity. -/
  pair_eta : ∀ {Γ : Ob} (a : Ty Γ),
    pair (projection a) (generic a) = identity (extend Γ a)
  /-- `pair σ t` after `θ` is `σ` after `θ` paired with `t` reindexed along
  `θ`. -/
  pair_comp : ∀ {Γ Δ Ξ : Ob} {a : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (substTy a σ))
      (θ : Sub Ξ Δ),
    comp (pair σ t) θ = pair (comp σ θ) (substTy_comp a σ θ ▸ substTm t θ)
  -- The universe of sorts
  /-- The type whose terms are the sorts. -/
  U : (Γ : Ob) → Ty Γ
  /-- The universe is stable under reindexing. -/
  U_subst : ∀ {Γ Δ : Ob} (σ : Sub Δ Γ), substTy (U Γ) σ = U Δ
  /-- The type whose terms are the elements of a sort. -/
  El : {Γ : Ob} → Tm Γ (U Γ) → Ty Γ
  /-- Decoding is stable under reindexing. -/
  El_subst : ∀ {Γ Δ : Ob} (S : Tm Γ (U Γ)) (σ : Sub Δ Γ),
    substTy (El S) σ = El (U_subst σ ▸ substTm S σ)
  -- Binding
  /-- A type over the extension by `a`, bound over `a` into a type over the
  base. -/
  Bind : {Γ : Ob} → (a : Ty Γ) → Ty (extend Γ a) → Ty Γ
  /-- A term over an extension, read as a term of a binding type. -/
  lam : {Γ : Ob} → {a : Ty Γ} → {c : Ty (extend Γ a)} →
    Tm (extend Γ a) c → Tm Γ (Bind a c)
  /-- A term of a binding type, read as a term over an extension. -/
  unlam : {Γ : Ob} → {a : Ty Γ} → {c : Ty (extend Γ a)} →
    Tm Γ (Bind a c) → Tm (extend Γ a) c
  /-- `lam` after `unlam` is the identity. -/
  lam_unlam : ∀ {Γ : Ob} {a : Ty Γ} {c : Ty (extend Γ a)} (t : Tm Γ (Bind a c)),
    lam (unlam t) = t
  /-- `unlam` after `lam` is the identity. -/
  unlam_lam : ∀ {Γ : Ob} {a : Ty Γ} {c : Ty (extend Γ a)} (e : Tm (extend Γ a) c),
    unlam (lam e) = e
  /-- A binding type reindexed along `σ` binds its reindexed domain, with the
  type over the extension reindexed along `σ` carried through the extension:
  `σ` after the projection, paired with the generic term. -/
  Bind_subst : ∀ {Γ Δ : Ob} (a : Ty Γ) (c : Ty (extend Γ a)) (σ : Sub Δ Γ),
    substTy (Bind a c) σ
      = Bind (substTy a σ)
        (substTy c (pair (comp σ (projection (substTy a σ)))
          (substTy_comp a σ (projection (substTy a σ)) ▸ generic (substTy a σ))))
  /-- `lam` commutes with reindexing, the term over the extension being
  reindexed along `σ` carried through the extension. -/
  lam_subst : ∀ {Γ Δ : Ob} {a : Ty Γ} {c : Ty (extend Γ a)}
      (e : Tm (extend Γ a) c) (σ : Sub Δ Γ),
    Bind_subst a c σ ▸ substTm (lam e) σ
      = lam (substTm e (pair (comp σ (projection (substTy a σ)))
          (substTy_comp a σ (projection (substTy a σ)) ▸ generic (substTy a σ))))
  -- Equality of sorts
  /-- The type asserting that two sorts are equal. -/
  IdSort : {Γ : Ob} → Tm Γ (U Γ) → Tm Γ (U Γ) → Ty Γ
  /-- Every sort equals itself. -/
  IdSort_refl : {Γ : Ob} → (S : Tm Γ (U Γ)) → Tm Γ (IdSort S S)
  /-- Equality of sorts is stable under reindexing. -/
  IdSort_subst : ∀ {Γ Δ : Ob} (S S' : Tm Γ (U Γ)) (σ : Sub Δ Γ),
    substTy (IdSort S S') σ
      = IdSort (U_subst σ ▸ substTm S σ) (U_subst σ ▸ substTm S' σ)
  /-- Any two terms of `IdSort S S'` are equal. -/
  IdSort_irrelevant : ∀ {Γ : Ob} {S S' : Tm Γ (U Γ)} (t t' : Tm Γ (IdSort S S')),
    t = t'
  /-- A term of `IdSort S S'` gives `S = S'`. -/
  IdSort_reflect : ∀ {Γ : Ob} {S S' : Tm Γ (U Γ)}, Tm Γ (IdSort S S') → S = S'
  -- Equality of elements
  /-- The type asserting that two elements of a sort are equal. -/
  IdElement : {Γ : Ob} → {S : Tm Γ (U Γ)} → Tm Γ (El S) → Tm Γ (El S) → Ty Γ
  /-- Every element equals itself. -/
  IdElement_refl : {Γ : Ob} → {S : Tm Γ (U Γ)} → (t : Tm Γ (El S)) →
    Tm Γ (IdElement t t)
  /-- Equality of elements is stable under reindexing. -/
  IdElement_subst : ∀ {Γ Δ : Ob} {S : Tm Γ (U Γ)} (l r : Tm Γ (El S))
      (σ : Sub Δ Γ),
    substTy (IdElement l r) σ
      = IdElement (El_subst S σ ▸ substTm l σ) (El_subst S σ ▸ substTm r σ)
  /-- Any two terms of `IdElement l r` are equal. -/
  IdElement_irrelevant : ∀ {Γ : Ob} {S : Tm Γ (U Γ)} {l r : Tm Γ (El S)}
    (t t' : Tm Γ (IdElement l r)), t = t'
  /-- A term of `IdElement l r` gives `l = r`. -/
  IdElement_reflect : ∀ {Γ : Ob} {S : Tm Γ (U Γ)} {l r : Tm Γ (El S)},
    Tm Γ (IdElement l r) → l = r

namespace Structure

variable {M : Structure.{u}}

/-- Reindexing a term along `comp σ θ` and reindexing it along `σ` and then along `θ`
give heterogeneously equal terms, whatever equations of types the reindexed terms are
transported along. -/
theorem substTm_comp_heq
    {Γ Δ Ξ : M.Ob} {a : M.Ty Γ} {b : M.Ty Δ} {c e : M.Ty Ξ} (t : M.Tm Γ a)
    (σ : M.Sub Δ Γ) (θ : M.Sub Ξ Δ) (h : M.substTy a σ = b) (h' : M.substTy b θ = c)
    (h'' : M.substTy a (M.comp σ θ) = e) :
  HEq (h'' ▸ M.substTm t (M.comp σ θ)) (h' ▸ M.substTm (h ▸ M.substTm t σ) θ)
  := by
  subst h h' h''
  apply HEq.trans _ (heq_of_eq (M.substTm_comp t σ θ))
  symm
  apply eqRec_heq

/-- A term reindexed along the identity is heterogeneously equal to the term, whatever
equation of types the reindexed term is transported along. -/
theorem substTm_identity_heq
    {Γ : M.Ob} {a b : M.Ty Γ} (t : M.Tm Γ a) (h : M.substTy a (M.identity Γ) = b) :
  HEq (h ▸ M.substTm t (M.identity Γ)) t
  := by
  subst h
  apply HEq.trans _ (heq_of_eq (M.substTm_identity t))
  symm
  apply eqRec_heq

/-- The substitution `σ` carried through the extension by `a`. It goes from `Δ`
extended by `a` reindexed along `σ` to `Γ` extended by `a`, and is `σ` after the
projection, paired with the generic term: on the base it acts as `σ`, and it sends
the generic term to the generic term. `Bind_subst` and `lam_subst` reindex the type
and the term over the extension along exactly this substitution. -/
def lift {Γ Δ : M.Ob} (a : M.Ty Γ) (σ : M.Sub Δ Γ) :
    M.Sub (M.extend Δ (M.substTy a σ)) (M.extend Γ a) :=
  M.pair (M.comp σ (M.projection (M.substTy a σ)))
    (M.substTy_comp a σ (M.projection (M.substTy a σ)) ▸ M.generic (M.substTy a σ))

/-- Lifting `σ` and then projecting is projecting and then applying `σ`. -/
theorem projection_lift
    {Γ Δ : M.Ob} (a : M.Ty Γ) (σ : M.Sub Δ Γ) :
  M.comp (M.projection a) (M.lift a σ) = M.comp σ (M.projection (M.substTy a σ))
  := by
  apply M.projection_pair

/-- The generic term reindexed along the lift of `σ` is the generic term of the
reindexed type. -/
theorem generic_lift
    {Γ Δ : M.Ob} (a : M.Ty Γ) (σ : M.Sub Δ Γ) :
  HEq (M.substTm (M.generic a) (M.lift a σ)) (M.generic (M.substTy a σ))
  := by
  apply HEq.trans (M.generic_pair _ _)
  apply eqRec_heq

/-- A substitution into an extension is the pair of its two components: its
composite with the projection, and the generic term reindexed along it. -/
theorem pair_components
    {Γ Δ : M.Ob} {a : M.Ty Γ} (τ : M.Sub Δ (M.extend Γ a)) :
  M.pair (M.comp (M.projection a) τ)
      (M.substTy_comp a (M.projection a) τ ▸ M.substTm (M.generic a) τ)
    = τ
  := by
  rw [← M.pair_comp, M.pair_eta, M.identity_comp]

/-- Lifting the identity is the identity. The two sides have domains that are equal
by `substTy_identity`. -/
theorem lift_identity
    {Γ : M.Ob} (a : M.Ty Γ) :
  HEq (M.lift a (M.identity Γ)) (M.identity (M.extend Γ a))
  := by
  rw [← M.pair_eta a, lift]
  congr 1
  · rw [M.substTy_identity]
  · rw [M.identity_comp, M.substTy_identity]
  · apply HEq.trans (eqRec_heq _ _)
    rw [M.substTy_identity]

/-- Lifting along a composite is lifting along each factor in turn. The two sides
have domains that are equal by `substTy_comp`. -/
theorem lift_comp
    {Γ Δ Ξ : M.Ob} (a : M.Ty Γ) (σ : M.Sub Δ Γ) (θ : M.Sub Ξ Δ) :
  HEq (M.lift a (M.comp σ θ)) (M.comp (M.lift a σ) (M.lift (M.substTy a σ) θ))
  := by
  rw [← M.pair_components (M.comp (M.lift a σ) (M.lift (M.substTy a σ) θ)), lift]
  congr 1
  · rw [M.substTy_comp]
  · conv =>
      rhs
      rw [← M.comp_assoc, projection_lift, M.comp_assoc, projection_lift, ← M.comp_assoc]
    rw [M.substTy_comp]
  · apply HEq.trans (eqRec_heq _ _)
    symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (b := M.substTm (M.substTm (M.generic a) (M.lift a σ)) (M.lift (M.substTy a σ) θ))
    · apply HEq.trans _ (heq_of_eq (M.substTm_comp _ _ _))
      symm
      apply eqRec_heq
    · apply HEq.trans (b := M.substTm (M.generic (M.substTy a σ)) (M.lift (M.substTy a σ) θ))
      · congr 1
        · rw [← M.substTy_comp, projection_lift, M.substTy_comp]
        · apply generic_lift
      · apply HEq.trans (generic_lift _ _)
        rw [M.substTy_comp]

end Structure

end HrS
