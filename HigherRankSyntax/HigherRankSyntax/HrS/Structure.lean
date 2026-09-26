/-!
# Models of the framework

A model of the framework `HrS` has four sorts: objects, substitutions between
two objects, types over an object, and terms of a type over an object.  Its
operations and their laws come in four groups: a category with a terminal
object, reindexing and context extension; a universe of sorts with its decoding
into types of elements; binding, a type over an extension read as a type over
the base, with a bijection on terms; and extensional equality types of sorts
and of elements of a sort.
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

end HrS
