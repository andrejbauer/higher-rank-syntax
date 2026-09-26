import HigherRankSyntax.HrS.Structure

/-!
# Morphisms of models

A morphism of models carries each of the four sorts of the source to the
corresponding sort of the target and commutes with every operation other than
`toEmpty` and `unlam`.  A law whose two sides lie in types identified by an
earlier law is a heterogeneous equality.
-/

universe u

namespace HrS

/-- A morphism of models: a map for each sort, commuting with the operations
other than `toEmpty` and `unlam`. -/
structure Morphism (M N : Structure.{u}) where
  /-- The map on objects. -/
  onOb : M.Ob → N.Ob
  /-- The map on substitutions. -/
  onSub : {Γ Δ : M.Ob} → M.Sub Δ Γ → N.Sub (onOb Δ) (onOb Γ)
  /-- The map on types. -/
  onTy : {Γ : M.Ob} → M.Ty Γ → N.Ty (onOb Γ)
  /-- The map on terms. -/
  onTm : {Γ : M.Ob} → {a : M.Ty Γ} → M.Tm Γ a → N.Tm (onOb Γ) (onTy a)
  -- The category and its terminal object
  /-- The identity is preserved. -/
  onSub_identity : ∀ (Γ : M.Ob), onSub (M.identity Γ) = N.identity (onOb Γ)
  /-- Composition is preserved. -/
  onSub_comp : ∀ {Γ Δ Ξ : M.Ob} (σ : M.Sub Δ Γ) (θ : M.Sub Ξ Δ),
    onSub (M.comp σ θ) = N.comp (onSub σ) (onSub θ)
  /-- The empty object is preserved. -/
  onOb_empty : onOb M.empty = N.empty
  -- Reindexing
  /-- Reindexing of types is preserved. -/
  onTy_substTy : ∀ {Γ Δ : M.Ob} (a : M.Ty Γ) (σ : M.Sub Δ Γ),
    onTy (M.substTy a σ) = N.substTy (onTy a) (onSub σ)
  /-- Reindexing of terms is preserved. -/
  onTm_substTm : ∀ {Γ Δ : M.Ob} {a : M.Ty Γ} (t : M.Tm Γ a) (σ : M.Sub Δ Γ),
    HEq (onTm (M.substTm t σ)) (N.substTm (onTm t) (onSub σ))
  -- Extension
  /-- Extension is preserved. -/
  onOb_extend : ∀ (Γ : M.Ob) (a : M.Ty Γ),
    onOb (M.extend Γ a) = N.extend (onOb Γ) (onTy a)
  /-- The projection is preserved. -/
  onSub_projection : ∀ {Γ : M.Ob} (a : M.Ty Γ),
    HEq (onSub (M.projection a)) (N.projection (onTy a))
  /-- The adjoined term is preserved. -/
  onTm_generic : ∀ {Γ : M.Ob} (a : M.Ty Γ),
    HEq (onTm (M.generic a)) (N.generic (onTy a))
  /-- Pairing is preserved. -/
  onSub_pair : ∀ {Γ Δ : M.Ob} {a : M.Ty Γ} (σ : M.Sub Δ Γ)
      (t : M.Tm Δ (M.substTy a σ)),
    HEq (onSub (M.pair σ t))
      (N.pair (onSub σ) (onTy_substTy a σ ▸ onTm t))
  /-- The lifted substitution is preserved. -/
  onSub_lift : ∀ {Γ Δ : M.Ob} (a : M.Ty Γ) (σ : M.Sub Δ Γ),
    HEq (onSub (M.lift a σ)) (N.lift (onTy a) (onSub σ))
  -- The universe of sorts
  /-- The universe is preserved. -/
  onTy_U : ∀ (Γ : M.Ob), onTy (M.U Γ) = N.U (onOb Γ)
  /-- Decoding is preserved. -/
  onTy_El : ∀ {Γ : M.Ob} (S : M.Tm Γ (M.U Γ)),
    onTy (M.El S) = N.El (onTy_U Γ ▸ onTm S)
  -- Binding
  /-- Binding is preserved. -/
  onTy_Bind : ∀ {Γ : M.Ob} (a : M.Ty Γ) (c : M.Ty (M.extend Γ a))
      (c' : N.Ty (N.extend (onOb Γ) (onTy a))), HEq (onTy c) c' →
    onTy (M.Bind a c) = N.Bind (onTy a) c'
  /-- `lam` is preserved. -/
  onTm_lam : ∀ {Γ : M.Ob} {a : M.Ty Γ} {c : M.Ty (M.extend Γ a)}
      (e : M.Tm (M.extend Γ a) c) (c' : N.Ty (N.extend (onOb Γ) (onTy a)))
      (e' : N.Tm (N.extend (onOb Γ) (onTy a)) c'),
    HEq (onTy c) c' → HEq (onTm e) e' → HEq (onTm (M.lam e)) (N.lam e')
  -- Equality of sorts and of elements
  /-- Equality of sorts is preserved. -/
  onTy_IdSort : ∀ {Γ : M.Ob} (S S' : M.Tm Γ (M.U Γ)),
    onTy (M.IdSort S S') = N.IdSort (onTy_U Γ ▸ onTm S) (onTy_U Γ ▸ onTm S')
  /-- Reflexivity of equality of sorts is preserved. -/
  onTm_IdSort_refl : ∀ {Γ : M.Ob} (S : M.Tm Γ (M.U Γ)),
    HEq (onTm (M.IdSort_refl S)) (N.IdSort_refl (onTy_U Γ ▸ onTm S))
  /-- Equality of elements is preserved. -/
  onTy_IdElement : ∀ {Γ : M.Ob} {S : M.Tm Γ (M.U Γ)} (l r : M.Tm Γ (M.El S)),
    HEq (onTy (M.IdElement l r))
      (N.IdElement (onTy_El S ▸ onTm l) (onTy_El S ▸ onTm r))
  /-- Reflexivity of equality of elements is preserved. -/
  onTm_IdElement_refl : ∀ {Γ : M.Ob} {S : M.Tm Γ (M.U Γ)} (t : M.Tm Γ (M.El S)),
    HEq (onTm (M.IdElement_refl t)) (N.IdElement_refl (onTy_El S ▸ onTm t))

end HrS
