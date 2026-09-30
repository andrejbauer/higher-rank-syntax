import HigherRankSyntax.HrS.Morphism

/-!
# Families closed under the operations of a model

A family of predicates on the objects, substitutions, types and terms of a model is
closed when each operation, applied to arguments satisfying the predicates, gives a
result satisfying them, and every term of an equality type satisfies the predicate on
terms as soon as the type satisfies the predicate on types.

Two morphisms of models are equal when they agree on the four sorts, and where two
morphisms agree is closed.
-/

universe u v

namespace HrS

variable (S : Structure.{u}) in
/-- A family of predicates on the four sorts of `S` closed under the operations of `S`:
each operation, applied to arguments satisfying the predicates, with every object involved
satisfying `P_Ob`, gives a result satisfying them. `P_Tm` also holds of every term of an
equality type satisfying `P_Ty`. -/
structure Structure.Closed (P_Ob : S.Ob → Prop) (P_Sub : ∀ {Γ Δ : S.Ob}, S.Sub Δ Γ → Prop)
    (P_Ty : ∀ {Γ : S.Ob}, S.Ty Γ → Prop) (P_Tm : ∀ {Γ : S.Ob} {a : S.Ty Γ}, S.Tm Γ a → Prop) :
    Prop where
  /-- The empty object satisfies `P_Ob`. -/
  empty : P_Ob S.empty
  /-- Closure under `extend`. -/
  extend : ∀ {Γ : S.Ob} {a : S.Ty Γ}, P_Ob Γ → P_Ty a → P_Ob (S.extend Γ a)
  /-- Closure under `identity`. -/
  identity : ∀ {Γ : S.Ob}, P_Ob Γ → P_Sub (S.identity Γ)
  /-- Closure under `comp`. -/
  comp : ∀ {Γ Δ Ξ : S.Ob} {σ : S.Sub Δ Γ} {θ : S.Sub Ξ Δ}, P_Ob Γ → P_Ob Δ → P_Ob Ξ →
    P_Sub σ → P_Sub θ → P_Sub (S.comp σ θ)
  /-- Closure under `toEmpty`. -/
  toEmpty : ∀ {Γ : S.Ob}, P_Ob Γ → P_Sub (S.toEmpty Γ)
  /-- Closure under `substTy`. -/
  substTy : ∀ {Γ Δ : S.Ob} {a : S.Ty Γ} {σ : S.Sub Δ Γ}, P_Ob Γ → P_Ob Δ → P_Ty a →
    P_Sub σ → P_Ty (S.substTy a σ)
  /-- Closure under `substTm`. -/
  substTm : ∀ {Γ Δ : S.Ob} {a : S.Ty Γ} {t : S.Tm Γ a} {σ : S.Sub Δ Γ}, P_Ob Γ → P_Ob Δ →
    P_Ty a → P_Tm t → P_Sub σ → P_Tm (S.substTm t σ)
  /-- Closure under `projection`. -/
  projection : ∀ {Γ : S.Ob} {a : S.Ty Γ}, P_Ob Γ → P_Ty a → P_Sub (S.projection a)
  /-- Closure under `generic`. -/
  generic : ∀ {Γ : S.Ob} {a : S.Ty Γ}, P_Ob Γ → P_Ty a → P_Tm (S.generic a)
  /-- Closure under `pair`. -/
  pair : ∀ {Γ Δ : S.Ob} {a : S.Ty Γ} {σ : S.Sub Δ Γ} {t : S.Tm Δ (S.substTy a σ)},
    P_Ob Γ → P_Ob Δ → P_Ty a → P_Sub σ → P_Tm t → P_Sub (S.pair σ t)
  /-- Closure under `U`. -/
  U : ∀ {Γ : S.Ob}, P_Ob Γ → P_Ty (S.U Γ)
  /-- Closure under `El`. -/
  El : ∀ {Γ : S.Ob} {s : S.Tm Γ (S.U Γ)}, P_Ob Γ → P_Tm s → P_Ty (S.El s)
  /-- Closure under `Bind`. -/
  Bind : ∀ {Γ : S.Ob} {a : S.Ty Γ} {c : S.Ty (S.extend Γ a)}, P_Ob Γ → P_Ty a → P_Ty c →
    P_Ty (S.Bind a c)
  /-- Closure under `lam`. -/
  lam : ∀ {Γ : S.Ob} {a : S.Ty Γ} {c : S.Ty (S.extend Γ a)} {e : S.Tm (S.extend Γ a) c},
    P_Ob Γ → P_Ty a → P_Ty c → P_Tm e → P_Tm (S.lam e)
  /-- Closure under `unlam`. -/
  unlam : ∀ {Γ : S.Ob} {a : S.Ty Γ} {c : S.Ty (S.extend Γ a)} {t : S.Tm Γ (S.Bind a c)},
    P_Ob Γ → P_Ty a → P_Ty c → P_Tm t → P_Tm (S.unlam t)
  /-- Closure under `IdSort`. -/
  IdSort : ∀ {Γ : S.Ob} {s s' : S.Tm Γ (S.U Γ)}, P_Ob Γ → P_Tm s → P_Tm s' →
    P_Ty (S.IdSort s s')
  /-- Closure under `IdElement`. -/
  IdElement : ∀ {Γ : S.Ob} {s : S.Tm Γ (S.U Γ)} {l r : S.Tm Γ (S.El s)}, P_Ob Γ → P_Tm s →
    P_Tm l → P_Tm r → P_Ty (S.IdElement l r)
  /-- `P_Tm` holds of every term of `IdSort s s'` over `Γ` when `P_Ob` holds of `Γ` and
  `P_Ty` of `IdSort s s'`. -/
  IdSort_term : ∀ {Γ : S.Ob} {s s' : S.Tm Γ (S.U Γ)} (t : S.Tm Γ (S.IdSort s s')), P_Ob Γ →
    P_Ty (S.IdSort s s') → P_Tm t
  /-- `P_Tm` holds of every term of `IdElement l r` over `Γ` when `P_Ob` holds of `Γ` and
  `P_Ty` of `IdElement l r`. -/
  IdElement_term : ∀ {Γ : S.Ob} {s : S.Tm Γ (S.U Γ)} {l r : S.Tm Γ (S.El s)}
    (t : S.Tm Γ (S.IdElement l r)), P_Ob Γ → P_Ty (S.IdElement l r) → P_Tm t

namespace Morphism

variable {S : Structure.{u}} {N : Structure.{v}}

/-- Two morphisms agreeing on objects, substitutions, types and terms are equal. -/
theorem ext
    {F G : Morphism S N} (hOb : ∀ Γ, F.onOb Γ = G.onOb Γ)
    (hSub : ∀ {Γ Δ : S.Ob} (σ : S.Sub Δ Γ), HEq (F.onSub σ) (G.onSub σ))
    (hTy : ∀ {Γ : S.Ob} (a : S.Ty Γ), HEq (F.onTy a) (G.onTy a))
    (hTm : ∀ {Γ : S.Ob} {a : S.Ty Γ} (t : S.Tm Γ a), HEq (F.onTm t) (G.onTm t)) :
  F = G
  := by
  obtain ⟨onOb, onSub, onTy, onTm⟩ := F
  obtain ⟨onOb', onSub', onTy', onTm'⟩ := G
  obtain rfl : onOb = onOb' := funext hOb
  obtain rfl : @onTy = @onTy' := by
    funext Γ a
    apply eq_of_heq (hTy a)
  obtain rfl : @onSub = @onSub' := by
    funext Γ Δ σ
    apply eq_of_heq (hSub σ)
  obtain rfl : @onTm = @onTm' := by
    funext Γ a t
    apply eq_of_heq (hTm t)
  rfl

/-- Where two morphisms agree is closed under the operations of the source. -/
theorem agree_closed (F G : Morphism S N) :
  S.Closed (fun Γ => F.onOb Γ = G.onOb Γ) (fun σ => HEq (F.onSub σ) (G.onSub σ))
    (fun a => HEq (F.onTy a) (G.onTy a)) (fun t => HEq (F.onTm t) (G.onTm t)) where
  empty := by
    rw [F.onOb_empty, G.onOb_empty]
  extend hΓ ha := by
    rw [F.onOb_extend, G.onOb_extend]
    congr 1
  identity hΓ := by
    rw [F.onSub_identity, G.onSub_identity, hΓ]
  comp hΓ hΔ hΞ hσ hθ := by
    rw [F.onSub_comp, G.onSub_comp]
    congr 1
  toEmpty {Γ} hΓ := by
    have unique : ∀ x y : N.Sub (G.onOb Γ) (G.onOb S.empty), x = y := by
      rw [G.onOb_empty]
      intro x y
      rw [N.toEmpty_unique x, N.toEmpty_unique y]
    apply heq_of_eqRec_eq (by rw [hΓ, F.onOb_empty, G.onOb_empty])
    apply unique
  substTy hΓ hΔ ha hσ := by
    rw [F.onTy_substTy, G.onTy_substTy]
    congr 1
  substTm hΓ hΔ ha ht hσ := by
    apply HEq.trans (F.onTm_substTm _ _)
    apply HEq.trans _ (HEq.symm (G.onTm_substTm _ _))
    congr 1
  projection hΓ ha := by
    apply HEq.trans (F.onSub_projection _)
    apply HEq.trans _ (HEq.symm (G.onSub_projection _))
    congr 1
  generic hΓ ha := by
    apply HEq.trans (F.onTm_generic _)
    apply HEq.trans _ (HEq.symm (G.onTm_generic _))
    congr 1
  pair hΓ hΔ ha hσ ht := by
    apply HEq.trans (F.onSub_pair _ _)
    apply HEq.trans _ (HEq.symm (G.onSub_pair _ _))
    congr 1
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans _ (HEq.symm (eqRec_heq _ _))
    apply ht
  U hΓ := by
    rw [F.onTy_U, G.onTy_U, hΓ]
  El hΓ hs := by
    rw [F.onTy_El, G.onTy_El]
    congr 1
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans _ (HEq.symm (eqRec_heq _ _))
    apply hs
  Bind {Γ a c} hΓ ha hc := by
    rw [F.onTy_Bind a c _ (HEq.symm (cast_heq (congrArg N.Ty (F.onOb_extend Γ a)) _)),
      G.onTy_Bind a c _ (HEq.symm (cast_heq (congrArg N.Ty (G.onOb_extend Γ a)) _))]
    congr 1
    apply HEq.trans (cast_heq _ _)
    apply HEq.trans _ (HEq.symm (cast_heq _ _))
    apply hc
  lam {Γ a c e} hΓ ha hc he := by
    have hOF := F.onOb_extend Γ a
    have hOG := G.onOb_extend Γ a
    have hcF := HEq.symm (cast_heq (congrArg N.Ty hOF) (F.onTy c))
    have hcG := HEq.symm (cast_heq (congrArg N.Ty hOG) (G.onTy c))
    apply HEq.trans (F.onTm_lam e _ _ hcF (HEq.symm (cast_heq (by congr 1) _)))
    apply HEq.trans _ (HEq.symm (G.onTm_lam e _ _ hcG (HEq.symm (cast_heq (by congr 1) _))))
    congr 1
    · apply HEq.trans (HEq.symm hcF)
      apply HEq.trans hc hcG
    · apply HEq.trans (cast_heq _ _)
      apply HEq.trans _ (HEq.symm (cast_heq _ _))
      apply he
  unlam {Γ a c t} hΓ ha hc ht := by
    have hOF := F.onOb_extend Γ a
    have hOG := G.onOb_extend Γ a
    have hcF := HEq.symm (cast_heq (congrArg N.Ty hOF) (F.onTy c))
    have hcG := HEq.symm (cast_heq (congrArg N.Ty hOG) (G.onTy c))
    have hTF : N.Tm _ (F.onTy c) = N.Tm _ (cast (congrArg N.Ty hOF) (F.onTy c)) := by congr 1
    have hTG : N.Tm _ (G.onTy c) = N.Tm _ (cast (congrArg N.Ty hOG) (G.onTy c)) := by congr 1
    have hlF := F.onTm_lam (S.unlam t) _ _ hcF (HEq.symm (cast_heq hTF _))
    have hlG := G.onTm_lam (S.unlam t) _ _ hcG (HEq.symm (cast_heq hTG _))
    rw [S.lam_unlam] at hlF hlG
    apply HEq.trans (HEq.symm (cast_heq hTF _))
    apply HEq.trans _ (cast_heq hTG _)
    rw [← N.unlam_lam (cast hTF _), ← N.unlam_lam (cast hTG _)]
    congr 1
    · apply HEq.trans (HEq.symm hcF)
      apply HEq.trans hc hcG
    · apply HEq.trans (HEq.symm hlF)
      apply HEq.trans ht hlG
  IdSort hΓ hs hs' := by
    rw [F.onTy_IdSort, G.onTy_IdSort]
    congr 1
    · apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans _ (HEq.symm (eqRec_heq _ _))
      apply hs
    · apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans _ (HEq.symm (eqRec_heq _ _))
      apply hs'
  IdElement hΓ hs hl hr := by
    apply HEq.trans (F.onTy_IdElement _ _)
    apply HEq.trans _ (HEq.symm (G.onTy_IdElement _ _))
    congr 1
    · apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans _ (HEq.symm (eqRec_heq _ _))
      apply hs
    · apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans _ (HEq.symm (eqRec_heq _ _))
      apply hl
    · apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans _ (HEq.symm (eqRec_heq _ _))
      apply hr
  IdSort_term {Γ s s'} t hΓ ha := by
    have irrelevant : ∀ x y : N.Tm (G.onOb Γ) (G.onTy (S.IdSort s s')), x = y := by
      rw [G.onTy_IdSort]
      apply N.IdSort_irrelevant
    apply heq_of_eqRec_eq (by congr 1)
    apply irrelevant
  IdElement_term {Γ s l r} t hΓ ha := by
    have irrelevant : ∀ x y : N.Tm (G.onOb Γ) (G.onTy (S.IdElement l r)), x = y := by
      rw [eq_of_heq (G.onTy_IdElement l r)]
      apply N.IdElement_irrelevant
    apply heq_of_eqRec_eq (by congr 1)
    apply irrelevant

end Morphism

end HrS
