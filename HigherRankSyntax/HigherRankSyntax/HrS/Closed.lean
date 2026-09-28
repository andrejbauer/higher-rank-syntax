import HigherRankSyntax.HrS.Morphism

/-!
# Families closed under the operations of a model

A family of predicates on the objects, substitutions, types and terms of a model is
closed when each operation, applied to arguments satisfying the predicates, gives a
result satisfying them; every term of an equation type satisfies the predicate on terms
as soon as the type satisfies the predicate on types.

Two morphisms of models are equal when they agree on the four sorts, and where two
morphisms agree is closed.
-/

universe u v

namespace HrS

variable (S : Structure.{u}) in
/-- A family of predicates on the four sorts of `S` closed under the operations of `S`,
and holding of every term of an equation type satisfying the predicate on types. -/
structure Structure.Closed (P_Ob : S.Ob → Prop) (P_Sub : ∀ {Γ Δ : S.Ob}, S.Sub Δ Γ → Prop)
    (P_Ty : ∀ {Γ : S.Ob}, S.Ty Γ → Prop) (P_Tm : ∀ {Γ : S.Ob} {a : S.Ty Γ}, S.Tm Γ a → Prop) :
    Prop where
  /-- The empty object. -/
  empty : P_Ob S.empty
  /-- Extensions of objects by types. -/
  extend : ∀ {Γ : S.Ob} {a : S.Ty Γ}, P_Ob Γ → P_Ty a → P_Ob (S.extend Γ a)
  /-- Identities. -/
  identity : ∀ {Γ : S.Ob}, P_Ob Γ → P_Sub (S.identity Γ)
  /-- Composites. -/
  comp : ∀ {Γ Δ Ξ : S.Ob} {σ : S.Sub Δ Γ} {θ : S.Sub Ξ Δ}, P_Ob Γ → P_Ob Δ → P_Ob Ξ →
    P_Sub σ → P_Sub θ → P_Sub (S.comp σ θ)
  /-- Substitutions into the empty object. -/
  toEmpty : ∀ {Γ : S.Ob}, P_Ob Γ → P_Sub (S.toEmpty Γ)
  /-- Reindexed types. -/
  substTy : ∀ {Γ Δ : S.Ob} {a : S.Ty Γ} {σ : S.Sub Δ Γ}, P_Ob Γ → P_Ob Δ → P_Ty a →
    P_Sub σ → P_Ty (S.substTy a σ)
  /-- Reindexed terms. -/
  substTm : ∀ {Γ Δ : S.Ob} {a : S.Ty Γ} {t : S.Tm Γ a} {σ : S.Sub Δ Γ}, P_Ob Γ → P_Ob Δ →
    P_Ty a → P_Tm t → P_Sub σ → P_Tm (S.substTm t σ)
  /-- Projections. -/
  projection : ∀ {Γ : S.Ob} {a : S.Ty Γ}, P_Ob Γ → P_Ty a → P_Sub (S.projection a)
  /-- Generic terms. -/
  generic : ∀ {Γ : S.Ob} {a : S.Ty Γ}, P_Ob Γ → P_Ty a → P_Tm (S.generic a)
  /-- Pairs. -/
  pair : ∀ {Γ Δ : S.Ob} {a : S.Ty Γ} {σ : S.Sub Δ Γ} {t : S.Tm Δ (S.substTy a σ)},
    P_Ob Γ → P_Ob Δ → P_Ty a → P_Sub σ → P_Tm t → P_Sub (S.pair σ t)
  /-- Types of sorts. -/
  U : ∀ {Γ : S.Ob}, P_Ob Γ → P_Ty (S.U Γ)
  /-- Types of elements. -/
  El : ∀ {Γ : S.Ob} {s : S.Tm Γ (S.U Γ)}, P_Ob Γ → P_Tm s → P_Ty (S.El s)
  /-- Bound types. -/
  Bind : ∀ {Γ : S.Ob} {a : S.Ty Γ} {c : S.Ty (S.extend Γ a)}, P_Ob Γ → P_Ty a → P_Ty c →
    P_Ty (S.Bind a c)
  /-- `lam` of terms. -/
  lam : ∀ {Γ : S.Ob} {a : S.Ty Γ} {c : S.Ty (S.extend Γ a)} {e : S.Tm (S.extend Γ a) c},
    P_Ob Γ → P_Ty a → P_Ty c → P_Tm e → P_Tm (S.lam e)
  /-- `unlam` of terms. -/
  unlam : ∀ {Γ : S.Ob} {a : S.Ty Γ} {c : S.Ty (S.extend Γ a)} {t : S.Tm Γ (S.Bind a c)},
    P_Ob Γ → P_Ty a → P_Ty c → P_Tm t → P_Tm (S.unlam t)
  /-- Equations of sorts. -/
  IdSort : ∀ {Γ : S.Ob} {s s' : S.Tm Γ (S.U Γ)}, P_Ob Γ → P_Tm s → P_Tm s' →
    P_Ty (S.IdSort s s')
  /-- Equations of elements. -/
  IdElement : ∀ {Γ : S.Ob} {s : S.Tm Γ (S.U Γ)} {l r : S.Tm Γ (S.El s)}, P_Ob Γ → P_Tm s →
    P_Tm l → P_Tm r → P_Ty (S.IdElement l r)
  /-- Terms of equations of sorts. -/
  IdSort_term : ∀ {Γ : S.Ob} {s s' : S.Tm Γ (S.U Γ)} (t : S.Tm Γ (S.IdSort s s')), P_Ob Γ →
    P_Ty (S.IdSort s s') → P_Tm t
  /-- Terms of equations of elements. -/
  IdElement_term : ∀ {Γ : S.Ob} {s : S.Tm Γ (S.U Γ)} {l r : S.Tm Γ (S.El s)}
    (t : S.Tm Γ (S.IdElement l r)), P_Ob Γ → P_Ty (S.IdElement l r) → P_Tm t

namespace Morphism

variable {S : Structure.{u}} {N : Structure.{v}}

/-- Two morphisms agreeing on objects, substitutions, types and terms are equal. -/
theorem ext {F G : Morphism S N} (hOb : ∀ Γ, F.onOb Γ = G.onOb Γ)
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
    have key : ∀ H : Morphism S N, HEq (H.onSub (S.toEmpty Γ)) (N.toEmpty (H.onOb Γ)) := by
      intro H
      generalize H.onSub (S.toEmpty Γ) = p
      revert p
      rw [H.onOb_empty]
      intro p
      rw [N.toEmpty_unique p]
    apply HEq.trans (key F)
    apply HEq.trans _ (HEq.symm (key G))
    rw [hΓ]
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
    apply HEq.trans ht
    symm
    apply eqRec_heq
  U hΓ := by
    rw [F.onTy_U, G.onTy_U, hΓ]
  El hΓ hs := by
    rw [F.onTy_El, G.onTy_El]
    congr 1
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans hs
    symm
    apply eqRec_heq
  Bind {Γ a c} hΓ ha hc := by
    rw [F.onTy_Bind a c _ (HEq.symm (cast_heq (congrArg N.Ty (F.onOb_extend Γ a)) _)),
      G.onTy_Bind a c _ (HEq.symm (cast_heq (congrArg N.Ty (G.onOb_extend Γ a)) _))]
    congr 1
    apply HEq.trans (cast_heq _ _)
    apply HEq.trans hc
    symm
    apply cast_heq
  lam {Γ a c e} hΓ ha hc he := by
    have hOF := F.onOb_extend Γ a
    have hOG := G.onOb_extend Γ a
    have hcF := HEq.symm (cast_heq (congrArg N.Ty hOF) (F.onTy c))
    have hcG := HEq.symm (cast_heq (congrArg N.Ty hOG) (G.onTy c))
    have hTF : N.Tm (F.onOb (S.extend Γ a)) (F.onTy c)
        = N.Tm (N.extend (F.onOb Γ) (F.onTy a)) (cast (congrArg N.Ty hOF) (F.onTy c)) := by
      congr 1
    have hTG : N.Tm (G.onOb (S.extend Γ a)) (G.onTy c)
        = N.Tm (N.extend (G.onOb Γ) (G.onTy a)) (cast (congrArg N.Ty hOG) (G.onTy c)) := by
      congr 1
    have heF := HEq.symm (cast_heq hTF (F.onTm e))
    have heG := HEq.symm (cast_heq hTG (G.onTm e))
    apply HEq.trans (F.onTm_lam e _ _ hcF heF)
    apply HEq.trans _ (HEq.symm (G.onTm_lam e _ _ hcG heG))
    congr 1
    · apply HEq.trans (HEq.symm hcF)
      apply HEq.trans hc hcG
    · apply HEq.trans (HEq.symm heF)
      apply HEq.trans he heG
  unlam {Γ a c t} hΓ ha hc ht := by
    have hOF := F.onOb_extend Γ a
    have hOG := G.onOb_extend Γ a
    have hcF := HEq.symm (cast_heq (congrArg N.Ty hOF) (F.onTy c))
    have hcG := HEq.symm (cast_heq (congrArg N.Ty hOG) (G.onTy c))
    have hTF : N.Tm (F.onOb (S.extend Γ a)) (F.onTy c)
        = N.Tm (N.extend (F.onOb Γ) (F.onTy a)) (cast (congrArg N.Ty hOF) (F.onTy c)) := by
      congr 1
    have hTG : N.Tm (G.onOb (S.extend Γ a)) (G.onTy c)
        = N.Tm (N.extend (G.onOb Γ) (G.onTy a)) (cast (congrArg N.Ty hOG) (G.onTy c)) := by
      congr 1
    have heF := HEq.symm (cast_heq hTF (F.onTm (S.unlam t)))
    have heG := HEq.symm (cast_heq hTG (G.onTm (S.unlam t)))
    have hlF := F.onTm_lam (S.unlam t) _ _ hcF heF
    have hlG := G.onTm_lam (S.unlam t) _ _ hcG heG
    rw [S.lam_unlam] at hlF hlG
    have key : ∀ {X₁ X₂ : N.Ob} {A₁ : N.Ty X₁} {A₂ : N.Ty X₂} {C₁ : N.Ty (N.extend X₁ A₁)}
        {C₂ : N.Ty (N.extend X₂ A₂)} (e₁ : N.Tm (N.extend X₁ A₁) C₁)
        (e₂ : N.Tm (N.extend X₂ A₂) C₂), X₁ = X₂ → HEq A₁ A₂ → HEq C₁ C₂ →
        HEq (N.lam e₁) (N.lam e₂) → HEq e₁ e₂ := by
      rintro X₁ _ A₁ _ C₁ _ e₁ e₂ rfl hA hC hl
      obtain rfl := eq_of_heq hA
      obtain rfl := eq_of_heq hC
      rw [← N.unlam_lam e₁, ← N.unlam_lam e₂, eq_of_heq hl]
    apply HEq.trans heF
    apply HEq.trans _ (HEq.symm heG)
    apply key _ _ hΓ ha
    · apply HEq.trans (HEq.symm hcF)
      apply HEq.trans hc hcG
    · apply HEq.trans (HEq.symm hlF)
      apply HEq.trans ht hlG
  IdSort hΓ hs hs' := by
    rw [F.onTy_IdSort, G.onTy_IdSort]
    congr 1
    · apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans hs
      symm
      apply eqRec_heq
    · apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans hs'
      symm
      apply eqRec_heq
  IdElement hΓ hs hl hr := by
    apply HEq.trans (F.onTy_IdElement _ _)
    apply HEq.trans _ (HEq.symm (G.onTy_IdElement _ _))
    congr 1
    · apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans hs
      symm
      apply eqRec_heq
    · apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans hl
      symm
      apply eqRec_heq
    · apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans hr
      symm
      apply eqRec_heq
  IdSort_term {Γ s s'} t hΓ ha := by
    have key : ∀ {X₁ X₂ : N.Ob} {A₁ : N.Ty X₁} {A₂ : N.Ty X₂} (t₁ : N.Tm X₁ A₁)
        (t₂ : N.Tm X₂ A₂), X₁ = X₂ → HEq A₁ A₂ → (∃ u u', A₁ = N.IdSort u u') →
        HEq t₁ t₂ := by
      rintro X₁ _ A₁ _ t₁ t₂ rfl hA ⟨u, u', rfl⟩
      obtain rfl := eq_of_heq hA
      apply heq_of_eq (N.IdSort_irrelevant t₁ t₂)
    apply key _ _ hΓ ha ⟨_, _, F.onTy_IdSort s s'⟩
  IdElement_term {Γ s l r} t hΓ ha := by
    have key : ∀ {X₁ X₂ : N.Ob} {A₁ : N.Ty X₁} {A₂ : N.Ty X₂} (t₁ : N.Tm X₁ A₁)
        (t₂ : N.Tm X₂ A₂), X₁ = X₂ → HEq A₁ A₂ →
        (∃ (u : N.Tm X₁ (N.U X₁)) (l' r' : N.Tm X₁ (N.El u)), A₁ = N.IdElement l' r') →
        HEq t₁ t₂ := by
      rintro X₁ _ A₁ _ t₁ t₂ rfl hA ⟨u, l', r', rfl⟩
      obtain rfl := eq_of_heq hA
      apply heq_of_eq (N.IdElement_irrelevant t₁ t₂)
    apply key _ _ hΓ ha ⟨_, _, _, eq_of_heq (F.onTy_IdElement l r)⟩

end Morphism

end HrS
