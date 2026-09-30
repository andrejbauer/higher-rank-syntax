import HigherRankSyntax.Typing.Weakening

/-!
# The variable rule

Over an ambient `Ξ`: the η-expansion of a slot `x` whose declaration is not an
equation and whose bound entries form a well-formed telescope is well formed
over `Ξ ⋈ Ξ.binding x`; and for a well-formed telescope `Θ`, the η-expansions
of the slots of `Θ` in `Ξ ⋈ Θ` fill the renaming of `Θ` along `Renaming.inl`
over `Ξ ⋈ Θ`.
-/

mutual

/-- If the entries bound by `x` form a telescope well formed over `Ξ` and the
declaration of `x` is not an equation, then `Expr.η x` is well formed over
`Ξ ⋈ Ξ.binding x`. -/
theorem Wf_e.eta :
  ∀ {Δ α : C.Arity} (Ξ : Ambient Δ) (x : Δ ∋ α),
    Wf_t Ξ (Ξ.binding x) → ¬ (Ξ.declaration x).isEq →
    Wf_e (Ξ ⋈ Ξ.binding x) (Expr.η x)
  | _, _, Ξ, x, hb, hx => by
      rw [Expr.η.eq_1]
      apply Wf_e.ap
      case head =>
        erw [dTel.declaration_concatenate_inl, Bd.isEq_rename]
        apply hx
      case fill =>
        rw [dTel.binding_concatenate_inl]
        apply Wf_s.eta Ξ (Ξ.binding x) hb
termination_by Δ α _ _ _ _ => (α, 1)
decreasing_by exact Prod.Lex.right _ (by omega)

/-- If `Θ` is well formed over `Ξ`, then `Subst.instId Δ Ω`, which sends each slot
`i` of `Θ` to `Expr.η (C.inr i)`, fills `dTel.rename (Renaming.inl Δ Ω) Θ` over
`Ξ ⋈ Θ`. -/
theorem Wf_s.eta :
  ∀ {Δ Ω : C.Arity} (Ξ : Ambient Δ) (Θ : dTel Δ Ω),
    Wf_t Ξ Θ → Wf_s (Ξ ⋈ Θ) (dTel.rename (Renaming.inl Δ Ω) Θ) (Subst.instId Δ Ω)
  | Δ, Ω, Ξ, Θ, hΘ => by
      apply Wf_s.slotwise
      case equation =>
        intro Λ z l r h
        have hdecl : Θ.declaration z = .eq l r := by
          rw [← h]
          symm
          apply dTel.act_declaration_instId
        have hbd := Wf_t.declaration hΘ z
        rw [hdecl] at hbd
        erw [dTel.instantiate_binding_instId]
        obtain ⟨hl, hr⟩ := Bd.eq.inj (Bd.instantiate_rename_inl (Δ ⋈ Ω) Λ (.eq l r))
        rw [← hl, ← hr]
        apply Eq_e.hyp (C.inl (C.inr z))
        · rw [dTel.declaration_concatenate_inl, dTel.declaration_concatenate_inr]
          apply congrArg (Bd.rename _) hdecl
        · rw [dTel.binding_concatenate_inl, dTel.binding_concatenate_inr]
          apply Wf_e.weaken
            ((Ambient.Renaming.weaken (Ξ ⋈ Θ) (Θ.binding z)).extend (Θ.binding z))
            hbd.eq_left
        · rw [dTel.binding_concatenate_inl, dTel.binding_concatenate_inr]
          apply Wf_e.weaken
            ((Ambient.Renaming.weaken (Ξ ⋈ Θ) (Θ.binding z)).extend (Θ.binding z))
            hbd.eq_right
        · rw [dTel.binding_concatenate_inl, dTel.binding_concatenate_inr]
          apply Wf_s.eta (Ξ ⋈ Θ) (Θ.binding z) (Wf_t.binding hΘ z)
      case filler =>
        intro Λ z hne
        erw [dTel.instantiate_binding_instId, ← dTel.binding_concatenate_inr Ξ Θ]
        apply Wf_e.eta (Ξ ⋈ Θ) (C.inr z)
        · rw [dTel.binding_concatenate_inr]
          apply Wf_t.binding hΘ z
        · erw [dTel.declaration_concatenate_inr, ← dTel.act_declaration_instId Θ z]
          apply hne
      case declared =>
        intro Λ z _
        erw [dTel.instantiate_binding_instId]
        convert Wf_bd.refl (Wf_t.declaration hΘ z) using 2
        · erw [← dTel.declaration_concatenate_inr Ξ Θ, ← dTel.binding_concatenate_inr Ξ Θ]
          apply dTel.boundaryOf_eta
        · apply dTel.act_declaration_instId
termination_by Δ Ω _ _ _ => (Ω, 0)
decreasing_by all_goals exact Prod.Lex.left _ _ ⟨z⟩

end
