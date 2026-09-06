import HigherRankSyntax.Typing.Weakening

/-!
# The variable rule

A slot, applied to the entries it binds, is well formed; and the fresh slots of
an extension fill the telescope they were added for.  The two are mutually
recursive on the binding arity, and depend on `Wf_t.declaration` rather than on
the substitution lemma.
-/

mutual

/-- 8(5): a non-equational slot, fully applied, is well formed over the ambient
extended by the entries it binds. -/
theorem Wf_e.eta : ∀ {Δ α : C.Arity} (Ξ : Ambient Δ) (x : Δ ∋ α),
    Wf_t Ξ (Ξ.binding x) → ¬ (Ξ.declaration x).isEq →
    Wf_e ((Ξ ⋈ Ξ.binding x)) (Expr.η x)
  | Δ, α, Ξ, x, hb, hx => by
      rw [Expr.η.eq_1]
      refine Wf_e.ap (C.inl x) (Subst.instId Δ α) ?head ?fill
      case head =>
        refine fun hEq => hx ?_
        refine (Bd.isEq_rename (Renaming.inl Δ α ⇑ʳ α) (Ξ.declaration x)).mp ?_
        exact (dTel.declaration_concatenate_inl Ξ (Ξ.binding x) x) ▸ hEq
      case fill =>
        refine Eq.mp ?_ (Wf_s.eta Ξ (Ξ.binding x) hb)
        exact congrArg (fun T => Wf_s ((Ξ ⋈ Ξ.binding x)) T (Subst.instId Δ α))
          (dTel.binding_concatenate_inl Ξ (Ξ.binding x) x).symm
termination_by Δ α _ _ _ _ => (α, 1)
decreasing_by exact Prod.Lex.right α (by omega)

/-- 8(5): the fresh slots of an extension fill the telescope they were added for. -/
theorem Wf_s.eta : ∀ {Δ Ω : C.Arity} (Ξ : Ambient Δ) (Θ : dTel Δ Ω),
    Wf_t Ξ Θ → Wf_s ((Ξ ⋈ Θ)) (dTel.rename (Renaming.inl Δ Ω) Θ) (Subst.instId Δ Ω)
  | Δ, Ω, Ξ, Θ, hΘ => by
      refine Wf_s.mk ?equation ?filler ?declared
      case equation =>
        intro Λ z l r h
        replace h := (dTel.act_declaration_instId Θ z).symm.trans h
        have hbd := (h ▸ Wf_t.declaration hΘ z :
          Wf_bd ((Ξ ⋈ Θ)) (Θ.binding z) (Bd.eq l r))
        refine Eq.mp ?_ (Eq_e.hyp (Ξ := (((Ξ ⋈ Θ)) ⋈ Θ.binding z))
          (C.inl (C.inr z)) (⟦ Renaming.inl (Δ ⋈ Ω) Λ ⇑ʳ Λ ⟧ʳ l)
          (⟦ Renaming.inl (Δ ⋈ Ω) Λ ⇑ʳ Λ ⟧ʳ r) (Subst.instId (Δ ⋈ Ω) Λ)
          ?decl ?hl ?hr ?fill)
        case decl =>
          refine Eq.trans (dTel.declaration_concatenate_inl ((Ξ ⋈ Θ))
            (Θ.binding z) (C.inr z)) ?_
          refine Eq.trans (congrArg (Bd.rename (Renaming.inl (Δ ⋈ Ω) Λ ⇑ʳ Λ))
            ((dTel.declaration_concatenate_inr Ξ Θ z).trans h)) ?_
          exact Bd.rename_eq _ l r
        case hl =>
          refine Eq.mp ?_ (Wf_e.weaken
            ((Ambient.Renaming.weaken ((Ξ ⋈ Θ)) (Θ.binding z)).extend (Θ.binding z))
            hbd.1)
          exact congrArg (fun T => Wf_e ((((((Ξ ⋈ Θ)) ⋈ Θ.binding z)) ⋈ T))
              (⟦ Renaming.inl (Δ ⋈ Ω) Λ ⇑ʳ Λ ⟧ʳ l))
            (((dTel.binding_concatenate_inl ((Ξ ⋈ Θ)) (Θ.binding z) (C.inr z)).trans
              (congrArg (dTel.rename (Renaming.inl (Δ ⋈ Ω) Λ))
                (dTel.binding_concatenate_inr Ξ Θ z))).symm)
        case hr =>
          refine Eq.mp ?_ (Wf_e.weaken
            ((Ambient.Renaming.weaken ((Ξ ⋈ Θ)) (Θ.binding z)).extend (Θ.binding z))
            hbd.2.1)
          exact congrArg (fun T => Wf_e ((((((Ξ ⋈ Θ)) ⋈ Θ.binding z)) ⋈ T))
              (⟦ Renaming.inl (Δ ⋈ Ω) Λ ⇑ʳ Λ ⟧ʳ r))
            (((dTel.binding_concatenate_inl ((Ξ ⋈ Θ)) (Θ.binding z) (C.inr z)).trans
              (congrArg (dTel.rename (Renaming.inl (Δ ⋈ Ω) Λ))
                (dTel.binding_concatenate_inr Ξ Θ z))).symm)
        case fill =>
          refine Eq.mp ?_ (Wf_s.eta ((Ξ ⋈ Θ)) (Θ.binding z) (Wf_t.binding hΘ z))
          exact congrArg (fun T => Wf_s ((((Ξ ⋈ Θ)) ⋈ Θ.binding z)) T
              (Subst.instId (Δ ⋈ Ω) Λ))
            (((dTel.binding_concatenate_inl ((Ξ ⋈ Θ)) (Θ.binding z) (C.inr z)).trans
              (congrArg (dTel.rename (Renaming.inl (Δ ⋈ Ω) Λ))
                (dTel.binding_concatenate_inr Ξ Θ z))).symm)
        have hcancel : ∀ e : Expr ((Δ ⋈ Ω) ⋈ Λ),
            Subst.act (Γ := (Δ ⋈ Ω) ⋈ Λ) (Δ := Λ) (Ξ := 1) (Subst.instId (Δ ⋈ Ω) Λ) 1
                (⟦ Renaming.inl (Δ ⋈ Ω) Λ ⇑ʳ Λ ⟧ʳ e) = e := by
          intro e
          refine Eq.trans (congrArg (fun ρ =>
            Subst.act (Γ := (Δ ⋈ Ω) ⋈ Λ) (Δ := Λ) (Ξ := 1) (Subst.instId (Δ ⋈ Ω) Λ) 1
              (Renaming.act ρ e)) (Renaming.extend_unit (Renaming.inl (Δ ⋈ Ω) Λ ⇑ʳ Λ)).symm) ?_
          exact act_instId_weaken (Δ ⋈ Ω) Λ (Φ := 1) e
        refine Eq.trans (congrArg₂ (Eq_e ((((Ξ ⋈ Θ)) ⋈ Θ.binding z)))
          (hcancel l) (hcancel r)) ?_
        exact congrArg (fun T => Eq_e ((((Ξ ⋈ Θ)) ⋈ T)) l r)
          (dTel.instantiate_binding_instId Θ z).symm
      case filler =>
        intro Λ z hne
        have hx : ¬ (((Ξ ⋈ Θ)).declaration (C.inr z)).isEq := by
          refine fun hEq => hne ?_
          exact Eq.mp (congrArg Bd.isEq (dTel.act_declaration_instId Θ z)).symm
            ((dTel.declaration_concatenate_inr Ξ Θ z) ▸ hEq)
        have hb : Wf_t ((Ξ ⋈ Θ)) (((Ξ ⋈ Θ)).binding (C.inr z)) := by
          refine Eq.mp ?_ (Wf_t.binding hΘ z)
          exact congrArg (fun T => Wf_t ((Ξ ⋈ Θ)) T)
            (dTel.binding_concatenate_inr Ξ Θ z).symm
        refine Eq.mp ?_ (Wf_e.eta ((Ξ ⋈ Θ)) (C.inr z) hb hx)
        exact congrArg (fun T => Wf_e ((((Ξ ⋈ Θ)) ⋈ T)) (Expr.η (C.inr z)))
          ((dTel.binding_concatenate_inr Ξ Θ z).trans
            (dTel.instantiate_binding_instId Θ z).symm)
      case declared =>
        intro Λ z hne
        have hB : ((((Ξ ⋈ Θ)) ⋈ Θ.binding z)).boundaryOf (Expr.η (C.inr z))
            = Θ.declaration z := by
          refine Eq.trans (congrArg (fun (T : dTel (Δ ⋈ Ω) Λ) =>
            ((((Ξ ⋈ Θ)) ⋈ T)).boundaryOf (Expr.η (C.inr z)))
            (dTel.binding_concatenate_inr Ξ Θ z).symm) ?_
          exact (dTel.boundaryOf_eta ((Ξ ⋈ Θ)) (C.inr z)).trans
            (dTel.declaration_concatenate_inr Ξ Θ z)
        refine Eq.mp ?_ (Wf_bd.refl (Wf_t.declaration hΘ z))
        refine Eq.trans (congrArg₂ (fun (b c : Bd ((Δ ⋈ Ω) ⋈ Λ)) =>
            Eq_bd ((((Ξ ⋈ Θ)) ⋈ Θ.binding z)) b c) hB.symm
          (dTel.act_declaration_instId Θ z).symm) ?_
        exact congrArg (fun (T : dTel (Δ ⋈ Ω) Λ) =>
            Eq_bd ((((Ξ ⋈ Θ)) ⋈ T))
              (((((Ξ ⋈ Θ)) ⋈ T)).boundaryOf (Expr.η (C.inr z)))
              (Bd.act (Ξ := 1) (Subst.instId Δ Ω) Λ
                ((dTel.rename (Renaming.inl Δ Ω) Θ).declaration z)))
          (dTel.instantiate_binding_instId Θ z).symm
termination_by Δ Ω _ _ _ => (Ω, 0)
decreasing_by all_goals exact Prod.Lex.left _ _ ⟨z⟩

end
