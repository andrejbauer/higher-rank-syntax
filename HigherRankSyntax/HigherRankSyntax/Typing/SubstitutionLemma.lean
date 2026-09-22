import HigherRankSyntax.Typing.Eta

/-!
# Substitution

A derivation stays valid when the slots of its ambient are filled by a
well-formed substitution.  Stated over a filling of ambients rather than over a
literal block, so that the source ambient is a variable and the induction can
case on the derivation; filling a block is recovered by `Wf_s.filling`.
-/

/-! ## Fillings of ambients -/

/-- A filling of one ambient by another, filling only slots of arities below
`Ω`: at every slot the substitution is either the η of a slot carrying the same
declaration and the same entries bound, both under the substitution, or a filler
for the slot's declared boundary, well formed over the entries it binds. -/
structure Ambient.Filling {Γ Γ' : C.Arity} (A : Ambient Γ) (A' : Ambient Γ')
    (Ω : C.Arity) where
  fill : Subst Γ Γ'
  slot : ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α),
    (∃ y : Γ' ∋ α, fill x = Expr.η y ∧
        A'.declaration y = Bd.applyAt fill α (A.declaration x) ∧
        A'.binding y = fill ⋆ A.binding x)
      ∨ (Carrier.Sub α Ω ∧
          (∀ l r : Expr (Γ' ⋈ α),
              Bd.applyAt fill α (A.declaration x) = .eq l r →
              Eq_e (A' ⋈ fill ⋆ A.binding x) l r) ∧
          (¬ (Bd.applyAt fill α (A.declaration x)).isEq →
              Wf_e (A' ⋈ fill ⋆ A.binding x) (fill x)) ∧
          (¬ (Bd.applyAt fill α (A.declaration x)).isEq →
              Eq_bd (A' ⋈ fill ⋆ A.binding x)
                ((A' ⋈ fill ⋆ A.binding x).boundaryOf (fill x))
                (Bd.applyAt fill α (A.declaration x))))

/-- A filling of ambients extends along a telescope. -/
def Ambient.Filling.extend {Γ Γ' Ω Χ : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (F : Ambient.Filling A A' Ω) (T : dTel Γ Χ) :
    Ambient.Filling (A ⋈ T) (A' ⋈ F.fill ⋆ T) Ω where
  fill := Subst.lift F.fill Χ
  slot := by
    intro α x
    rcases C.cover Γ Χ x with ⟨w, rfl⟩ | ⟨i, rfl⟩
    · rcases F.slot w with ⟨y, hη, hdecl, hbind⟩ | ⟨hsub, heq, hwf, hbd⟩
      · refine Or.inl ⟨C.inl y, ?_, ?_, ?_⟩
        · rw [Subst.lift_inl, hη, Renaming.act_eta]
          rfl
        · refine Eq.trans (dTel.declaration_concatenate_inl A' (F.fill ⋆ T) y) ?_
          refine Eq.trans (congrArg (Bd.rename (Renaming.inl Γ' Χ ⇑ʳ α)) hdecl) ?_
          refine Eq.trans ?_ (congrArg
            (Bd.act (Γ := 1) (Ξ := Γ' ⋈ Χ) (Subst.lift F.fill Χ) α)
            (dTel.declaration_concatenate_inl A T w)).symm
          exact (Bd.act_square (Renaming.inl Γ Χ) (Renaming.inl Γ' Χ)
            (Subst.lift F.fill Χ) F.fill (fun ⦃_⦄ u => Subst.lift_inl F.fill u) α
            (A.declaration w)).symm
        · refine Eq.trans (dTel.binding_concatenate_inl A' (F.fill ⋆ T) y) ?_
          refine Eq.trans (congrArg (dTel.rename (Renaming.inl Γ' Χ)) hbind) ?_
          refine Eq.trans ?_ (congrArg (dTel.actBase (Subst.lift F.fill Χ))
            (dTel.binding_concatenate_inl A T w)).symm
          exact (dTel.actBase_square (Renaming.inl Γ Χ) (Renaming.inl Γ' Χ)
            (Subst.lift F.fill Χ) F.fill (fun ⦃_⦄ u => Subst.lift_inl F.fill u)
            (A.binding w)).symm
      · have hd : Bd.act (Γ := 1) (Ξ := Γ' ⋈ Χ) (Subst.lift F.fill Χ) α
                (((A ⋈ T)).declaration (C.inl w))
              = Bd.rename (Renaming.inl Γ' Χ ⇑ʳ α)
                  (Bd.act (Γ := 1) F.fill α (A.declaration w)) := by
          refine Eq.trans (congrArg
            (Bd.act (Γ := 1) (Ξ := Γ' ⋈ Χ) (Subst.lift F.fill Χ) α)
            (dTel.declaration_concatenate_inl A T w)) ?_
          exact Bd.act_square (Renaming.inl Γ Χ) (Renaming.inl Γ' Χ)
            (Subst.lift F.fill Χ) F.fill (fun ⦃_⦄ u => Subst.lift_inl F.fill u) α
            (A.declaration w)
        have hb : dTel.actBase (Subst.lift F.fill Χ) ((A ⋈ T).binding (C.inl w))
              = dTel.rename (Renaming.inl Γ' Χ) (dTel.actBase F.fill (A.binding w)) := by
          refine Eq.trans (congrArg (dTel.actBase (Subst.lift F.fill Χ))
            (dTel.binding_concatenate_inl A T w)) ?_
          exact dTel.actBase_square (Renaming.inl Γ Χ) (Renaming.inl Γ' Χ)
            (Subst.lift F.fill Χ) F.fill (fun ⦃_⦄ u => Subst.lift_inl F.fill u)
            (A.binding w)
        have hne : ¬ (Bd.act (Γ := 1) (Ξ := Γ' ⋈ Χ) (Subst.lift F.fill Χ) α
              (((A ⋈ T)).declaration (C.inl w))).isEq →
            ¬ (Bd.act (Γ := 1) F.fill α (A.declaration w)).isEq := by
          refine fun h hEq => h ?_
          exact hd ▸ (Bd.isEq_rename (Renaming.inl Γ' Χ ⇑ʳ α) _).mpr hEq
        refine Or.inr ⟨hsub, ?equation, ?filler, ?declared⟩
        case equation =>
          intro l r hlr
          replace hlr := hd.symm.trans hlr
          cases hc : Bd.act (Γ := 1) F.fill α (A.declaration w) with
          | sort =>
              rw [hc] at hlr
              replace hlr := (Bd.rename_sort _).symm.trans hlr
              cases hlr
          | of S =>
              rw [hc] at hlr
              replace hlr := (Bd.rename_of _ _).symm.trans hlr
              cases hlr
          | eq l₀ r₀ =>
              rw [hc] at hlr
              replace hlr := (Bd.rename_eq _ _ _).symm.trans hlr
              injection hlr with hl hr
              subst hl
              subst hr
              refine Eq.mp ?_ (Eq_e.weaken
                ((Ambient.Renaming.weaken A' (F.fill ⋆ T)).extend (F.fill ⋆ A.binding w))
                (heq l₀ r₀ hc))
              exact congrArg (fun S => Eq_e ((A' ⋈ F.fill ⋆ T) ⋈ S)
                  (⟦ Renaming.inl Γ' Χ ⇑ʳ α ⟧ʳ l₀) (⟦ Renaming.inl Γ' Χ ⇑ʳ α ⟧ʳ r₀))
                hb.symm
        case filler =>
          intro h
          refine Eq.mp ?_ (Wf_e.weaken
            ((Ambient.Renaming.weaken A' (F.fill ⋆ T)).extend (F.fill ⋆ A.binding w))
            (hwf (hne h)))
          refine Eq.trans (congrArg (fun S => Wf_e ((A' ⋈ F.fill ⋆ T) ⋈ S)
            (⟦ Renaming.inl Γ' Χ ⇑ʳ α ⟧ʳ (F.fill w))) hb.symm) ?_
          exact congrArg (fun e => Wf_e ((A' ⋈ F.fill ⋆ T) ⋈
              Subst.lift F.fill Χ ⋆ (A ⋈ T).binding (C.inl w)) e)
            (Subst.lift_inl F.fill w).symm
        case declared =>
          intro h
          refine Eq.mp ?_ (Eq_bd.weaken
            ((Ambient.Renaming.weaken A' (F.fill ⋆ T)).extend (F.fill ⋆ A.binding w))
            (hbd (hne h)))
          refine Eq.trans (congrArg₂ (fun (b c : Bd ((Γ' ⋈ Χ) ⋈ α)) =>
              Eq_bd ((A' ⋈ F.fill ⋆ T) ⋈
                dTel.rename (Renaming.inl Γ' Χ) (F.fill ⋆ A.binding w)) b c)
            (Ambient.Renaming.boundaryOf
              ((Ambient.Renaming.weaken A' (F.fill ⋆ T)).extend (F.fill ⋆ A.binding w))
              (F.fill w)).symm hd.symm) ?_
          refine Eq.trans (congrArg (fun S =>
              Eq_bd ((A' ⋈ F.fill ⋆ T) ⋈ S)
                (((A' ⋈ F.fill ⋆ T) ⋈ S).boundaryOf
                  (⟦ Renaming.inl Γ' Χ ⇑ʳ α ⟧ʳ (F.fill w)))
                (Bd.act (Γ := 1) (Ξ := Γ' ⋈ Χ) (Subst.lift F.fill Χ) α
                  ((A ⋈ T).declaration (C.inl w)))) hb.symm) ?_
          exact congrArg (fun e =>
              Eq_bd ((A' ⋈ F.fill ⋆ T) ⋈ Subst.lift F.fill Χ ⋆ (A ⋈ T).binding (C.inl w))
                (((A' ⋈ F.fill ⋆ T) ⋈
                  Subst.lift F.fill Χ ⋆ (A ⋈ T).binding (C.inl w)).boundaryOf e)
                (Bd.act (Γ := 1) (Ξ := Γ' ⋈ Χ) (Subst.lift F.fill Χ) α
                  ((A ⋈ T).declaration (C.inl w))))
            (Subst.lift_inl F.fill w).symm
    · refine Or.inl ⟨C.inr i, ?_, ?_, ?_⟩
      · exact Subst.lift_inr F.fill i
      · refine Eq.trans (dTel.declaration_concatenate_inr A' (dTel.actBase F.fill T) i) ?_
        refine Eq.trans (dTel.declaration_actBase F.fill T i) ?_
        exact congrArg (Bd.act (Γ := 1) (Ξ := Γ' ⋈ Χ) (Subst.lift F.fill Χ) α)
          (dTel.declaration_concatenate_inr A T i).symm
      · refine Eq.trans (dTel.binding_concatenate_inr A' (dTel.actBase F.fill T) i) ?_
        refine Eq.trans (dTel.binding_actBase F.fill T i) ?_
        exact congrArg (dTel.actBase (Subst.lift F.fill Χ))
          (dTel.binding_concatenate_inr A T i).symm

/-- A filling of a telescope is a filling of the ambient it extends. -/
def Wf_s.filling {Γ Ω : C.Arity} {A : Ambient Γ} {T : dTel Γ Ω} {τ : Subst Ω Γ}
    (h : Wf_s A T τ) : Ambient.Filling (A ⋈ T) A Ω where
  fill := Subst.copair (Subst.id Γ) τ
  slot := by
    intro α x
    rcases C.cover Γ Ω x with ⟨w, rfl⟩ | ⟨z, rfl⟩
    · refine Or.inl ⟨w, Subst.copair_inl _ _ w, ?_, ?_⟩
      · refine Eq.trans ?_ (congrArg (Bd.act (Γ := 1) (Ξ := Γ) (Subst.copair (Subst.id Γ) τ) α)
          (dTel.declaration_concatenate_inl A T w)).symm
        refine Eq.trans ?_ (Bd.act_rename_cancel (Renaming.inl Γ Ω) (𝟙ʳ Γ)
          (Subst.copair (Subst.id Γ) τ) (fun ⦃_⦄ u => Subst.copair_inl _ _ u) α
          (A.declaration w)).symm
        exact (Eq.trans (congrArg (fun ρ => Bd.rename ρ (A.declaration w))
          (Renaming.extend_id Γ α)) (Bd.rename_id _)).symm
      · refine Eq.trans ?_ (congrArg (dTel.actBase (Subst.copair (Subst.id Γ) τ))
          (dTel.binding_concatenate_inl A T w)).symm
        refine Eq.trans ?_ (dTel.actBase_rename_cancel (Renaming.inl Γ Ω) (𝟙ʳ Γ)
          (Subst.copair (Subst.id Γ) τ) (fun ⦃_⦄ u => Subst.copair_inl _ _ u)
          (A.binding w)).symm
        exact (dTel.rename_id _).symm
    · have equation := h.equation
      have filler := h.filler
      have declared := h.declared
      have hd : Bd.act (Γ := 1) (Ξ := Γ) (Subst.copair (Subst.id Γ) τ) α
              (((A ⋈ T)).declaration (C.inr z))
            = Bd.act (Γ := Γ) (Ξ := 1) τ α (T.declaration z) :=
        Eq.trans (congrArg (Bd.act (Γ := 1) (Ξ := Γ) (Subst.copair (Subst.id Γ) τ) α)
          (dTel.declaration_concatenate_inr A T z))
          (Bd.act_copair_prefix τ α (T.declaration z))
      have hb : dTel.actBase (Subst.copair (Subst.id Γ) τ)
              (((A ⋈ T)).binding (C.inr z))
            = dTel.instantiate τ (T.binding z) :=
        congrArg (dTel.actBase (Subst.copair (Subst.id Γ) τ))
          (dTel.binding_concatenate_inr A T z)
      refine Or.inr ⟨⟨z⟩, ?equation, ?filler, ?declared⟩
      case equation =>
        intro l r hlr
        refine Eq.mp (congrArg (fun S => Eq_e ((A ⋈ S)) l r) hb.symm)
          (equation z l r (hd.symm.trans hlr))
      case filler =>
        intro hne
        refine Eq.mp ?_ (filler z (fun hEq => hne (Eq.mp (congrArg Bd.isEq hd).symm hEq)))
        refine Eq.trans (congrArg (fun S => Wf_e ((A ⋈ S)) (τ z)) hb.symm) ?_
        exact congrArg (fun e => Wf_e (A ⋈ Subst.copair (Subst.id Γ) τ ⋆
            (A ⋈ T).binding (C.inr z)) e) (Subst.copair_inr (Subst.id Γ) τ z).symm
      case declared =>
        intro hne
        refine Eq.mp ?_ (declared z (fun hEq => hne (Eq.mp (congrArg Bd.isEq hd).symm hEq)))
        refine Eq.trans (congrArg (fun S => Eq_bd ((A ⋈ S))
            (((A ⋈ S)).boundaryOf (τ z)) (Bd.act (Γ := Γ) (Ξ := 1) τ α
              (T.declaration z))) hb.symm) ?_
        refine Eq.trans (congrArg (fun e => Eq_bd
            (A ⋈ Subst.copair (Subst.id Γ) τ ⋆ (A ⋈ T).binding (C.inr z))
            ((A ⋈ Subst.copair (Subst.id Γ) τ ⋆
              (A ⋈ T).binding (C.inr z)).boundaryOf e)
            (Bd.act (Γ := Γ) (Ξ := 1) τ α (T.declaration z)))
          (Subst.copair_inr (Subst.id Γ) τ z).symm) ?_
        exact congrArg (fun b => Eq_bd
            (A ⋈ Subst.copair (Subst.id Γ) τ ⋆ (A ⋈ T).binding (C.inr z))
            ((A ⋈ Subst.copair (Subst.id Γ) τ ⋆ (A ⋈ T).binding (C.inr z)).boundaryOf
              (Subst.copair (Subst.id Γ) τ (C.inr z))) b) hd.symm

/-! ## The substitution lemma -/

/-- The substitution lemma for fillings that fill only slots of arities below
`Ω`. -/
structure SubstitutionAt (Ω : C.Arity) : Prop where
  /-- 8(3) at `Ω`. -/
  expr : ∀ {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (F : Ambient.Filling A A' Ω) {g : Expr Γ},
      Wf_e A g → Wf_e A' (F.fill ⋆ g)
  /-- 8(2) at `Ω`. -/
  boundary : ∀ {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (F : Ambient.Filling A A' Ω) {g : Expr Γ},
      Wf_e A g →
      Eq_bd A' (F.fill ⋆ A.boundaryOf g) (F.fill ⋆ A.boundaryOf g) →
      Eq_bd A' (A'.boundaryOf (F.fill ⋆ g)) (F.fill ⋆ A.boundaryOf g)
  /-- Equality of boundaries at `Ω`. -/
  boundaryEquality : ∀ {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (F : Ambient.Filling A A' Ω) {β β' : Bd Γ}, Eq_bd A β β' →
      Eq_bd A' (F.fill ⋆ β) (F.fill ⋆ β')
  /-- Equality of expressions at `Ω`. -/
  equality : ∀ {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (F : Ambient.Filling A A' Ω) {l r : Expr Γ}, Eq_e A l r →
      Eq_e A' (F.fill ⋆ l) (F.fill ⋆ r)
  /-- 8(9) for declarations at `Ω`. -/
  declaration : ∀ {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (F : Ambient.Filling A A' Ω) {Λ : C.Arity} {T : dTel Γ Λ} {β : Bd (Γ ⋈ Λ)},
      Wf_bd A T β → Wf_bd A' (F.fill ⋆ T) (Bd.applyAt F.fill Λ β)
  /-- 8(9) for telescopes at `Ω`. -/
  telescope : ∀ {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (F : Ambient.Filling A A' Ω) {Λ : C.Arity} {T : dTel Γ Λ},
      Wf_t A T → Wf_t A' (F.fill ⋆ T)
  /-- 8(4) at `Ω`. -/
  filling : ∀ {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (F : Ambient.Filling A A' Ω) {Χ : C.Arity} {X : dTel Γ Χ} {τ : Subst Χ Γ},
      Wf_s A X τ →
        Wf_s A' (F.fill ⋆ X) (F.fill ⋆ τ)

mutual

/-- 8(3): well-formedness of expressions is stable under a filling. -/
theorem Wf_e.subst_step {Γ Γ' Ω : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ih : ∀ ⦃α : C.Arity⦄, Carrier.Sub α Ω → SubstitutionAt α)
    (F : Ambient.Filling A A' Ω) :
    ∀ {g : Expr Γ}, Wf_e A g → Wf_e A' (F.fill ⋆ g)
  | _, .ap (α := α) x args head fill => by
      rcases F.slot x with ⟨y, hη, hdecl, hbind⟩ | ⟨hsub, heq, hwf, hbd⟩
      · refine Eq.mp (congrArg (Wf_e A') (act_ap_eta F.fill x y hη args).symm) ?_
        refine Wf_e.ap y _ ?head ?fill
        case head =>
          refine fun hEq => head ?_
          exact (Bd.isEq_act (Γ := 1) F.fill α (A.declaration x)).mp
            (Eq.mp (congrArg Bd.isEq hdecl) hEq)
        case fill =>
          refine Eq.mp ?_ (Wf_s.subst_step ih F fill)
          exact congrArg (fun S => Wf_s A' S
              (F.fill ⋆ args))
            hbind.symm
      · have hne : ¬ (Bd.act (Γ := 1) F.fill α (A.declaration x)).isEq :=
          fun hEq => head ((Bd.isEq_act (Γ := 1) F.fill α (A.declaration x)).mp hEq)
        refine Eq.mp (congrArg (Wf_e A') (act_ap F.fill x args).symm) ?_
        refine Eq.mp (congrArg (Wf_e A') (act_copair_prefix
          (F.fill ⋆ args) 1
          (F.fill x))) ?_
        exact (ih hsub).expr (Wf_s.filling (Wf_s.subst_step ih F fill)) (hwf hne)

/-- 8(2): the computed boundary of a filled expression is the filled boundary. -/
theorem boundaryOf_subst_step {Γ Γ' Ω : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ih : ∀ ⦃α : C.Arity⦄, Carrier.Sub α Ω → SubstitutionAt α)
    (F : Ambient.Filling A A' Ω) :
    ∀ {g : Expr Γ}, Wf_e A g →
      Eq_bd A' (F.fill ⋆ A.boundaryOf g) (F.fill ⋆ A.boundaryOf g) →
      Eq_bd A' (A'.boundaryOf (F.fill ⋆ g)) (F.fill ⋆ A.boundaryOf g)
  | _, .ap (α := α) x args head fill, refl => by
      rcases F.slot x with ⟨y, hη, hdecl, hbind⟩ | ⟨hsub, heq, hwf, hbd⟩
      · have hchain : A'.boundaryOf (Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill 1
                (Expr.ap x args))
              = Bd.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill 1
                  (A.boundaryOf (Expr.ap x args)) := by
          refine Eq.trans (congrArg A'.boundaryOf (act_ap_eta F.fill x y hη args)) ?_
          refine Eq.trans (congrArg (Bd.instantiate
            (F.fill ⋆ args))
            hdecl) ?_
          refine Eq.trans (congrArg (Bd.act (Γ := Γ') (Δ := α) (Ξ := 1)
            (F.fill ⋆ args) 1)
            (Bd.act_lift_depth F.fill (A.declaration x)).symm) ?_
          exact Bd.act_lift_fillers (Γ := Γ) (Γ' := Γ') (Χ := α) (Λ := 1) F.fill args
            (A.declaration x)
        exact Eq.mp (congrArg (fun b => Eq_bd A' b
          (Bd.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill 1
            (A.boundaryOf (Expr.ap x args)))) hchain.symm) refl
      · have hne : ¬ (Bd.act (Γ := 1) F.fill α (A.declaration x)).isEq :=
          fun hEq => head ((Bd.isEq_act (Γ := 1) F.fill α (A.declaration x)).mp hEq)
        have hmove := (ih hsub).boundaryEquality
          (Wf_s.filling (Wf_s.subst_step ih F fill)) (hbd hne)
        have hexpr : Subst.act (Γ := 1) (Wf_s.filling (Wf_s.subst_step ih F fill)).fill 1
                (F.fill x)
              = Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill 1 (Expr.ap x args) :=
          (act_copair_prefix
            (F.fill ⋆ args) 1
            (F.fill x)).trans (act_ap F.fill x args).symm
        have hbound : Bd.act (Γ := 1) (Wf_s.filling (Wf_s.subst_step ih F fill)).fill 1
                (Bd.act (Γ := 1) F.fill α (A.declaration x))
              = Bd.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill 1
                  (A.boundaryOf (Expr.ap x args)) := by
          refine Eq.trans (Bd.act_copair_prefix
            (F.fill ⋆ args) 1
            (Bd.act (Γ := 1) F.fill α (A.declaration x))) ?_
          refine Eq.trans (congrArg (Bd.act (Γ := Γ') (Δ := α) (Ξ := 1)
            (F.fill ⋆ args) 1)
            (Bd.act_lift_depth F.fill (A.declaration x)).symm) ?_
          exact Bd.act_lift_fillers (Γ := Γ) (Γ' := Γ') (Χ := α) (Λ := 1) F.fill args
            (A.declaration x)
        refine Eq.mp (congrArg₂ (fun a b => Eq_bd A' a b)
          (congrArg A'.boundaryOf hexpr) hbound) ?_
        exact Eq_bd.trans ((ih hsub).boundary (Wf_s.filling (Wf_s.subst_step ih F fill))
          (hwf hne) (Eq_bd.trans hmove hmove.symm)) hmove

/-- Equality of expressions is stable under a filling. -/
theorem Eq_e.subst_step {Γ Γ' Ω : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ih : ∀ ⦃α : C.Arity⦄, Carrier.Sub α Ω → SubstitutionAt α)
    (F : Ambient.Filling A A' Ω) :
    ∀ {l r : Expr Γ}, Eq_e A l r →
      Eq_e A' (F.fill ⋆ l) (F.fill ⋆ r)
  | _, _, .refl h => .refl (Wf_e.subst_step ih F h)
  | _, _, .symm h => .symm (Eq_e.subst_step ih F h)
  | _, _, .trans h h' => .trans (Eq_e.subst_step ih F h) (Eq_e.subst_step ih F h')
  | _, _, .hyp (Λ := Λ₀) q l r args decl hl hr fill => by
      have hdeclEq : Bd.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ₀ (A.declaration q)
          = Bd.eq (Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ₀ l)
              (Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ₀ r) :=
        (congrArg (Bd.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ₀) decl).trans
          (Bd.act_eq (Γ := 1) F.fill Λ₀ l r)
      have hmove : ∀ e : Expr (Γ ⋈ Λ₀),
          Subst.act (Γ := Γ') (Δ := Λ₀) (Ξ := 1)
              (F.fill ⋆ args) 1
              (Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ₀ e)
            = Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill 1
                (Subst.act (Γ := Γ) (Δ := Λ₀) (Ξ := 1) args 1 e) := by
        intro e
        refine Eq.trans (congrArg (Subst.act (Γ := Γ') (Δ := Λ₀) (Ξ := 1)
          (F.fill ⋆ args) 1)
          (Subst.act_lift_depth F.fill e).symm) ?_
        exact Subst.act_lift_fillers (Χ := Λ₀) (Λ := 1) F.fill args e
      refine Eq.mp (congrArg₂ (fun a b => Eq_e A' a b) (hmove l) (hmove r)) ?_
      rcases F.slot q with ⟨y, hη, hdecl, hbind⟩ | ⟨hsub, heq, hwf, hbd⟩
      · refine Eq_e.hyp (Ξ := A') y (Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ₀ l)
          (Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ₀ r)
          (F.fill ⋆ args)
          (hdecl.trans hdeclEq) ?hl ?hr ?fill
        case hl =>
          refine Eq.mp ?_ (Wf_e.subst_step ih (F.extend (A.binding q)) hl)
          refine Eq.trans (congrArg (fun e =>
              Wf_e ((A' ⋈ dTel.actBase F.fill (A.binding q))) e)
            (Subst.act_lift_depth F.fill l)) ?_
          exact congrArg (fun S => Wf_e ((A' ⋈ S))
            (Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ₀ l)) hbind.symm
        case hr =>
          refine Eq.mp ?_ (Wf_e.subst_step ih (F.extend (A.binding q)) hr)
          refine Eq.trans (congrArg (fun e =>
              Wf_e ((A' ⋈ dTel.actBase F.fill (A.binding q))) e)
            (Subst.act_lift_depth F.fill r)) ?_
          exact congrArg (fun S => Wf_e ((A' ⋈ S))
            (Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ₀ r)) hbind.symm
        case fill =>
          refine Eq.mp ?_ (Wf_s.subst_step ih F fill)
          exact congrArg (fun S => Wf_s A' S
              (F.fill ⋆ args))
            hbind.symm
      · refine Eq.mp (congrArg₂ (fun a b => Eq_e A' a b)
          (act_copair_prefix
            (F.fill ⋆ args) 1
            (Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ₀ l))
          (act_copair_prefix
            (F.fill ⋆ args) 1
            (Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ₀ r))) ?_
        exact (ih hsub).equality (Wf_s.filling (Wf_s.subst_step ih F fill))
          (heq (Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ₀ l)
            (Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ₀ r) hdeclEq)
  | _, _, .congr (Ω := Ω₀) (Θ := Θ₀) (e := e₀) (e' := e₀') s t hΘ₀ hs ht agree h => by
      refine Eq.mp (congrArg₂ (fun a b => Eq_e A' a b)
        (Subst.act_lift_fillers (Χ := Ω₀) (Λ := 1) F.fill s e₀)
        (Subst.act_lift_fillers (Χ := Ω₀) (Λ := 1) F.fill t e₀')) ?_
      exact Eq_e.congr (Ξ := A') (Θ := dTel.actBase F.fill Θ₀)
        (F.fill ⋆ s) (F.fill ⋆ t)
        (Wf_t.subst_step ih F hΘ₀) (Wf_s.subst_step ih F hs)
        (Wf_s.subst_step ih F ht) (Eq_s.subst_step ih F agree)
        (Eq_e.subst_step ih (F.extend Θ₀) h)

/-- 8(4): agreement of fillings is stable under a filling of the ambient. -/
theorem Eq_s.subst_step {Γ Γ' Ω : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ih : ∀ ⦃α : C.Arity⦄, Carrier.Sub α Ω → SubstitutionAt α)
    (F : Ambient.Filling A A' Ω) :
    ∀ {Χ : C.Arity} {X : dTel Γ Χ} {σ θ : Subst Χ Γ}, Eq_s A X σ θ →
      Eq_s A' (F.fill ⋆ X) (F.fill ⋆ σ) (F.fill ⋆ θ)
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons (α := α) (σ := σ) (θ := θ) (bind := bind)
      (boundary := boundary) (rest := rest) slot hrest => by
      refine .cons ?slot ?hrest
      case slot =>
        intro hne
        have h₀ : ¬ boundary.isEq :=
          fun hEq => hne ((Bd.isEq_act (Γ := 1) F.fill α boundary).mpr hEq)
        refine Eq.mp (congrArg₂ (Eq_e ((A' ⋈ F.fill ⋆ bind)))
          (Subst.act_lift_depth F.fill (σ (C.inl (C.singleSlot α))))
          (Subst.act_lift_depth F.fill (θ (C.inl (C.singleSlot α))))) ?_
        exact Eq_e.subst_step ih (F.extend bind) (slot h₀)
      case hrest =>
        refine Eq.mp (congrArg (fun T => Eq_s A' T
          (fun ⦃β⦄ (j : _ ∋ β) => Subst.act (Γ := 1) F.fill β (σ (C.inr j)))
          (fun ⦃β⦄ (j : _ ∋ β) => Subst.act (Γ := 1) F.fill β (θ (C.inr j))))
          (dTel.actBase_instantiate F.fill
            (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) rest)) ?_
        exact Eq_s.subst_step ih F hrest

/-- Equality of boundaries is stable under a filling. -/
theorem Eq_bd.subst_step {Γ Γ' Ω : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ih : ∀ ⦃α : C.Arity⦄, Carrier.Sub α Ω → SubstitutionAt α)
    (F : Ambient.Filling A A' Ω) :
    ∀ {β β' : Bd Γ}, Eq_bd A β β' →
      Eq_bd A' (F.fill ⋆ β) (F.fill ⋆ β')
  | _, _, .sort => .sort
  | _, _, .of h => .of (Eq_e.subst_step ih F h)
  | _, _, .eq hl hr => .eq (Eq_e.subst_step ih F hl) (Eq_e.subst_step ih F hr)

/-- 8(4): filling a telescope is stable under a filling of the ambient. -/
theorem Wf_s.subst_step {Γ Γ' Ω : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ih : ∀ ⦃α : C.Arity⦄, Carrier.Sub α Ω → SubstitutionAt α)
    (F : Ambient.Filling A A' Ω) :
    ∀ {Χ : C.Arity} {X : dTel Γ Χ} {τ : Subst Χ Γ}, Wf_s A X τ →
      Wf_s A' (F.fill ⋆ X) (F.fill ⋆ τ)
  | _, _, _, .nil => .nil
  | _, _, _, .cons (α := α) (σ := τ) (bind := bind) (boundary := boundary)
      (rest := rest) equation filler declared hrest => by
      refine .cons ?equation ?filler ?declared ?hrest
      case equation =>
        intro l r h
        obtain ⟨l₀, r₀, hβ, hl, hr⟩ := Bd.act_eq_inv (Γ := 1) F.fill α h
        subst hl
        subst hr
        refine Eq.mp (congrArg₂ (Eq_e (A' ⋈ F.fill ⋆ bind))
          (Subst.act_lift_depth F.fill l₀) (Subst.act_lift_depth F.fill r₀)) ?_
        exact Eq_e.subst_step ih (F.extend bind) (equation l₀ r₀ hβ)
      case filler =>
        intro hne
        have h₀ : ¬ boundary.isEq :=
          fun hEq => hne ((Bd.isEq_act (Γ := 1) F.fill α boundary).mpr hEq)
        refine Eq.mp (congrArg (Wf_e (A' ⋈ F.fill ⋆ bind))
          (Subst.act_lift_depth F.fill (τ (C.inl (C.singleSlot α))))) ?_
        exact Wf_e.subst_step ih (F.extend bind) (filler h₀)
      case declared =>
        intro hne
        have h₀ : ¬ boundary.isEq :=
          fun hEq => hne ((Bd.isEq_act (Γ := 1) F.fill α boundary).mpr hEq)
        have hmove := Eq_bd.subst_step ih (F.extend bind) (declared h₀)
        refine Eq.mp ?_ (Eq_bd.trans (boundaryOf_subst_step ih (F.extend bind)
          (filler h₀) (Eq_bd.trans hmove hmove.symm)) hmove)
        exact congrArg₂ (fun (e : Expr (Γ' ⋈ α)) (b : Bd (Γ' ⋈ α)) =>
            Eq_bd (A' ⋈ F.fill ⋆ bind) ((A' ⋈ F.fill ⋆ bind).boundaryOf e) b)
          (Subst.act_lift_depth F.fill (τ (C.inl (C.singleSlot α))))
          (Bd.act_lift_depth F.fill boundary)
      case hrest =>
        refine Eq.mp (congrArg (fun T => Wf_s A' T
          (fun ⦃β⦄ (j : _ ∋ β) => Subst.act (Γ := 1) F.fill β (τ (C.inr j))))
          (dTel.actBase_instantiate F.fill
            (fun ⦃β⦄ (i : C.single α ∋ β) => τ (C.inl i)) rest)) ?_
        exact Wf_s.subst_step ih F hrest

/-- 8(9): a well-formed declaration is stable under a filling. -/
theorem Wf_bd.subst_step {Γ Γ' Ω : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ih : ∀ ⦃α : C.Arity⦄, Carrier.Sub α Ω → SubstitutionAt α)
    (F : Ambient.Filling A A' Ω) :
    ∀ {Λ : C.Arity} {T : dTel Γ Λ} {β : Bd (Γ ⋈ Λ)}, Wf_bd A T β →
      Wf_bd A' (F.fill ⋆ T) (Bd.applyAt F.fill Λ β)
  | _, _, _, .sort => .sort
  | _, T, _, .of (S := S) hS hsort => by
      have hmove := Eq_bd.subst_step ih (F.extend T) hsort
      refine Wf_bd.of ?hS ?hsort
      case hS =>
        exact Eq.mp (congrArg (Wf_e (A' ⋈ F.fill ⋆ T))
          (Subst.act_lift_depth F.fill S)) (Wf_e.subst_step ih (F.extend T) hS)
      case hsort =>
        refine Eq.mp ?_ (Eq_bd.trans (boundaryOf_subst_step ih (F.extend T) hS
          (Eq_bd.trans hmove hmove.symm)) hmove)
        exact congrArg (fun e => Eq_bd (A' ⋈ F.fill ⋆ T)
          ((A' ⋈ F.fill ⋆ T).boundaryOf e) Bd.sort) (Subst.act_lift_depth F.fill S)
  | _, T, _, .eq (l := l) (r := r) hl hr heq => by
      have hmove := Eq_bd.subst_step ih (F.extend T) heq
      refine Wf_bd.eq ?hl ?hr ?heq
      case hl =>
        exact Eq.mp (congrArg (Wf_e (A' ⋈ F.fill ⋆ T))
          (Subst.act_lift_depth F.fill l)) (Wf_e.subst_step ih (F.extend T) hl)
      case hr =>
        exact Eq.mp (congrArg (Wf_e (A' ⋈ F.fill ⋆ T))
          (Subst.act_lift_depth F.fill r)) (Wf_e.subst_step ih (F.extend T) hr)
      case heq =>
        refine Eq.mp ?_ (Eq_bd.trans (Eq_bd.trans
          (boundaryOf_subst_step ih (F.extend T) hl (Eq_bd.trans hmove hmove.symm))
          hmove)
          (boundaryOf_subst_step ih (F.extend T) hr
            (Eq_bd.trans hmove.symm hmove)).symm)
        exact congrArg₂ (fun a b => Eq_bd (A' ⋈ F.fill ⋆ T)
            ((A' ⋈ F.fill ⋆ T).boundaryOf a) ((A' ⋈ F.fill ⋆ T).boundaryOf b))
          (Subst.act_lift_depth F.fill l) (Subst.act_lift_depth F.fill r)

/-- 8(9): a well-formed telescope is stable under a filling. -/
theorem Wf_t.subst_step {Γ Γ' Ω : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ih : ∀ ⦃α : C.Arity⦄, Carrier.Sub α Ω → SubstitutionAt α)
    (F : Ambient.Filling A A' Ω) :
    ∀ {Λ : C.Arity} {T : dTel Γ Λ}, Wf_t A T → Wf_t A' (F.fill ⋆ T)
  | _, _, .nil => .nil
  | _, _, .cons (bind := bind) (boundary := boundary) hbind hboundary hrest =>
      .cons (Wf_t.subst_step ih F hbind) (Wf_bd.subst_step ih F hboundary)
        (Wf_t.subst_step ih (F.extend (dTel.cons bind boundary .nil)) hrest)

end

/-- The substitution lemma, by induction on the arity of the filled slots. -/
theorem substitutionAt : ∀ Ω : C.Arity, SubstitutionAt Ω
  | Ω =>
      { expr := fun {_ _ _ _} F {_} h =>
          Wf_e.subst_step (fun _ hs => substitutionAt _) F h
        boundary := fun {_ _ _ _} F {_} h refl =>
          boundaryOf_subst_step (fun _ hs => substitutionAt _) F h refl
        boundaryEquality := fun {_ _ _ _} F {_ _} h =>
          Eq_bd.subst_step (fun _ hs => substitutionAt _) F h
        equality := fun {_ _ _ _} F {_ _} h =>
          Eq_e.subst_step (fun _ hs => substitutionAt _) F h
        filling := fun {_ _ _ _} F {_ _ _} h =>
          Wf_s.subst_step (fun _ hs => substitutionAt _) F h
        declaration := fun {_ _ _ _} F {_ _ _} h =>
          Wf_bd.subst_step (fun _ hs => substitutionAt _) F h
        telescope := fun {_ _ _ _} F {_ _} h =>
          Wf_t.subst_step (fun _ hs => substitutionAt _) F h }
termination_by Ω => Ω
decreasing_by all_goals exact hs

/-! ## Filling a block -/

section

variable {Δ Ω Φ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω} {σ : Subst Ω Δ}
  {Ψ : dTel (Δ ⋈ Ω) Φ}

/-- Filling `Θ` by `σ` under a suffix telescope. -/
def Wf_s.fillBefore (hσ : Wf_s Ξ Θ σ) (Ψ : dTel (Δ ⋈ Ω) Φ) :
    Ambient.Filling (Ξ ⋈ Θ ⋈ Ψ) (Ξ ⋈ σ ⋆ Ψ) Ω :=
  (Wf_s.filling hσ).extend Ψ

/-- Acting by `Wf_s.fillBefore` is acting by `σ` at depth `Φ`. -/
theorem Wf_s.fillBefore_act (hσ : Wf_s Ξ Θ σ) (Ψ : dTel (Δ ⋈ Ω) Φ)
    (g : Expr ((Δ ⋈ Ω) ⋈ Φ)) : (hσ.fillBefore Ψ).fill ⋆ g = σ ⋆ g :=
  (Subst.act_lift_depth (Subst.copair (Subst.id Δ) σ) g).trans
    (act_copair_prefix σ Φ g)

/-- Acting by `Wf_s.fillBefore` on a boundary is acting by `σ` at depth `Φ`. -/
theorem Wf_s.fillBefore_act_boundary (hσ : Wf_s Ξ Θ σ) (Ψ : dTel (Δ ⋈ Ω) Φ)
    (β : Bd ((Δ ⋈ Ω) ⋈ Φ)) : (hσ.fillBefore Ψ).fill ⋆ β = σ ⋆ β :=
  (Bd.act_lift_depth (Subst.copair (Subst.id Δ) σ) β).trans
    (Bd.act_copair_prefix σ Φ β)

/-- 8(3): well-formedness of expressions is stable under filling a block. -/
theorem Wf_e.subst (hσ : Wf_s Ξ Θ σ) {g : Expr ((Δ ⋈ Ω) ⋈ Φ)}
    (h : Ξ ⋈ Θ ⋈ Ψ ⊢ g) : Ξ ⋈ σ ⋆ Ψ ⊢ σ ⋆ g := by
  rw [← hσ.fillBefore_act Ψ g]
  exact (substitutionAt Ω).expr (hσ.fillBefore Ψ) h

/-- Equality of expressions is stable under filling a block. -/
theorem Eq_e.subst (hσ : Wf_s Ξ Θ σ) {l r : Expr ((Δ ⋈ Ω) ⋈ Φ)}
    (h : Ξ ⋈ Θ ⋈ Ψ ⊢ l ≈ r) : Ξ ⋈ σ ⋆ Ψ ⊢ σ ⋆ l ≈ σ ⋆ r := by
  rw [← hσ.fillBefore_act Ψ l, ← hσ.fillBefore_act Ψ r]
  exact (substitutionAt Ω).equality (hσ.fillBefore Ψ) h

/-- Equality of boundaries is stable under filling a block. -/
theorem Eq_bd.subst (hσ : Wf_s Ξ Θ σ) {β β' : Bd ((Δ ⋈ Ω) ⋈ Φ)}
    (h : Ξ ⋈ Θ ⋈ Ψ ⊢ β ≈ β') : Ξ ⋈ σ ⋆ Ψ ⊢ σ ⋆ β ≈ σ ⋆ β' := by
  rw [← hσ.fillBefore_act_boundary Ψ β, ← hσ.fillBefore_act_boundary Ψ β']
  exact (substitutionAt Ω).boundaryEquality (hσ.fillBefore Ψ) h

/-- The computed boundary of a well-formed expression over a well-formed ambient
is equal to itself. -/
theorem boundaryOf_refl {Δ : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ) :
    ∀ {e : Expr Δ}, Ξ ⊢ e → Ξ ⊢ Ξ.boundaryOf e ≈ Ξ.boundaryOf e
  | _, .ap (α := α) x args head fill => by
      refine Eq.mp ?_ (Eq_bd.subst (Ψ := (.nil : dTel (Δ ⋈ α) 1))
        (β := Ξ.declaration x) (β' := Ξ.declaration x) fill
        (Eq.mp ?_ (Wf_bd.refl (Wf_t.declaration hΞ x))))
      · exact congrArg (fun T => Eq_bd T
          (Bd.instantiate args (Ξ.declaration x)) (Bd.instantiate args (Ξ.declaration x)))
          (dTel.concatenate_nil Ξ)
      · exact congrArg (fun T => Eq_bd T (Ξ.declaration x) (Ξ.declaration x))
          (dTel.concatenate_nil (Ξ ⋈ Ξ.binding x)).symm

/-- 8(2): the computed boundary of a filled expression is the filled boundary. -/
theorem boundaryOf_subst (hΞ : Ambient.Wf (Ξ ⋈ Θ ⋈ Ψ)) (hσ : Wf_s Ξ Θ σ)
    {g : Expr ((Δ ⋈ Ω) ⋈ Φ)} (h : Ξ ⋈ Θ ⋈ Ψ ⊢ g) :
    Ξ ⋈ σ ⋆ Ψ ⊢ (Ξ ⋈ σ ⋆ Ψ).boundaryOf (σ ⋆ g) ≈ σ ⋆ (Ξ ⋈ Θ ⋈ Ψ).boundaryOf g := by
  rw [← hσ.fillBefore_act Ψ g,
    ← hσ.fillBefore_act_boundary Ψ ((Ξ ⋈ Θ ⋈ Ψ).boundaryOf g)]
  refine (substitutionAt Ω).boundary (hσ.fillBefore Ψ) h ?_
  rw [hσ.fillBefore_act_boundary Ψ]
  exact Eq_bd.subst hσ (boundaryOf_refl hΞ h)

/-- 8(9): a well-formed telescope stays well formed under filling a block. -/
theorem Wf_t.subst (hσ : Wf_s Ξ Θ σ) {Λ : C.Arity} {T : dTel ((Δ ⋈ Ω) ⋈ Φ) Λ}
    (h : Wf_t (Ξ ⋈ Θ ⋈ Ψ) T) : Wf_t (Ξ ⋈ σ ⋆ Ψ) (σ ⋆ T) :=
  (substitutionAt Ω).telescope (hσ.fillBefore Ψ) h

/-- 8(3) with no suffix: well-formedness is stable under a well-formed
substitution. -/
theorem Wf_e.instantiate (hσ : Wf_s Ξ Θ σ) {g : Expr (Δ ⋈ Ω)} (h : Ξ ⋈ Θ ⊢ g) :
    Ξ ⊢ σ ⋆ g := by
  refine Eq.mp (congrArg (fun A => Wf_e A (Subst.instantiate σ g))
    (dTel.concatenate_nil Ξ)) ?_
  refine Wf_e.subst (Ψ := .nil) hσ ?_
  exact Eq.mp (congrArg (fun A => Wf_e A g) (dTel.concatenate_nil (Ξ ⋈ Θ)).symm) h

/-- Equality of expressions is stable under a well-formed substitution. -/
theorem Eq_e.instantiate (hσ : Wf_s Ξ Θ σ) {l r : Expr (Δ ⋈ Ω)}
    (h : Ξ ⋈ Θ ⊢ l ≈ r) : Ξ ⊢ σ ⋆ l ≈ σ ⋆ r := by
  refine Eq.mp (congrArg (fun A => Eq_e A (Subst.instantiate σ l)
    (Subst.instantiate σ r)) (dTel.concatenate_nil Ξ)) ?_
  refine Eq_e.subst (Ψ := .nil) hσ ?_
  exact Eq.mp (congrArg (fun A => Eq_e A l r)
    (dTel.concatenate_nil (Ξ ⋈ Θ)).symm) h

/-- Equality of boundaries is stable under a well-formed substitution. -/
theorem Eq_bd.instantiate (hσ : Wf_s Ξ Θ σ) {β β' : Bd (Δ ⋈ Ω)}
    (h : Ξ ⋈ Θ ⊢ β ≈ β') : Ξ ⊢ σ ⋆ β ≈ σ ⋆ β' := by
  refine Eq.mp (congrArg (fun A => Eq_bd A (Bd.instantiate σ β)
    (Bd.instantiate σ β')) (dTel.concatenate_nil Ξ)) ?_
  refine Eq_bd.subst (Ψ := .nil) hσ ?_
  exact Eq.mp (congrArg (fun A => Eq_bd A β β')
    (dTel.concatenate_nil (Ξ ⋈ Θ)).symm) h

/-- 8(9) with no suffix: a well-formed telescope stays well formed under a
well-formed substitution. -/
theorem Wf_t.instantiate (hσ : Wf_s Ξ Θ σ) {Λ : C.Arity} {T : dTel (Δ ⋈ Ω) Λ}
    (h : Wf_t ((Ξ ⋈ Θ)) T) : Wf_t Ξ (σ ⋆ T) := by
  refine Eq.mp (congrArg (fun A => Wf_t A (dTel.instantiate σ T))
    (dTel.concatenate_nil Ξ)) ?_
  refine Eq.mp (congrArg (fun s => Wf_t ((Ξ ⋈ (.nil : dTel Δ 1)))
    (dTel.actBase s T)) (Subst.lift_one (Subst.copair (Subst.id Δ) σ))) ?_
  refine Wf_t.subst (Ψ := .nil) hσ ?_
  exact Eq.mp (congrArg (fun A => Wf_t A T)
    (dTel.concatenate_nil (Ξ ⋈ Θ)).symm) h

/-- 8(2) with no suffix: the computed boundary of an instantiated expression is
the instantiated boundary. -/
theorem boundaryOf_instantiate (hΞ : Ambient.Wf (Ξ ⋈ Θ)) (hσ : Wf_s Ξ Θ σ)
    {g : Expr (Δ ⋈ Ω)} (h : Ξ ⋈ Θ ⊢ g) :
    Ξ ⊢ Ξ.boundaryOf (σ ⋆ g) ≈ σ ⋆ (Ξ ⋈ Θ).boundaryOf g := by
  have hnil := dTel.concatenate_nil (Ξ ⋈ Θ)
  refine Eq.mp (congrArg₂ (fun (A : Ambient Δ) (b : Bd Δ) =>
      Eq_bd A (A.boundaryOf (Subst.instantiate σ g)) b)
    (dTel.concatenate_nil Ξ)
    (congrArg (fun B => Bd.instantiate σ (dTel.boundaryOf B g)) hnil)) ?_
  refine boundaryOf_subst (Ψ := .nil) ?hΞ hσ ?h
  case hΞ => exact Eq.mp (congrArg Ambient.Wf hnil.symm) hΞ
  case h => exact Eq.mp (congrArg (fun A => Wf_e A g) hnil.symm) h

/-- 8(4): filling a telescope is stable under filling a block. -/
theorem Wf_s.subst (hσ : Wf_s Ξ Θ σ) {Χ : C.Arity} {X : dTel ((Δ ⋈ Ω) ⋈ Φ) Χ}
    {τ : Subst Χ ((Δ ⋈ Ω) ⋈ Φ)} (h : Ξ ⋈ Θ ⋈ Ψ ⊢ τ : X) :
    Ξ ⋈ σ ⋆ Ψ ⊢ σ ⋆ τ : σ ⋆ X := by
  have hfill : σ ⋆ τ = (hσ.fillBefore Ψ).fill ⋆ τ := by
    funext Λ i
    exact (Subst.act_lift_copair σ Φ Λ (τ i)).symm
  rw [hfill]
  exact (substitutionAt Ω).filling (hσ.fillBefore Ψ) h

end

/-! ## Congruence -/

/-- 8(6): an application is equal to itself with its fillers replaced by equal
ones. -/
theorem Eq_e.ap {Δ α : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ)
    (x : Δ ∋ α) (args args' : Subst α Δ)
    (h : Ξ ⊢ Expr.ap x args) (h' : Ξ ⊢ Expr.ap x args')
    (agree : Ξ ⊢ args ≈ args' : Ξ.binding x) :
    Ξ ⊢ Expr.ap x args ≈ Expr.ap x args' := by
  cases h with
  | ap _ _ head fill =>
      cases h' with
      | ap _ _ _ fill' =>
          refine Eq.mp (congrArg₂ (Eq_e Ξ)
            (ap_eq_act_η x args).symm (ap_eq_act_η x args').symm) ?_
          exact Eq_e.congr (Ξ := Ξ) (Θ := Ξ.binding x) args args'
            (Wf_t.binding hΞ x) fill fill' agree
            (Eq_e.refl (Wf_e.eta Ξ x (Wf_t.binding hΞ x) head))

/-! ## Presuppositions -/

mutual

/-- 8(7): the left side of an equality is well formed. -/
theorem Eq_e.wf_left {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {e e' : Expr Δ}, Ξ ⊢ e ≈ e' → Ξ ⊢ e
  | _, _, .refl h => h
  | _, _, .symm h => Eq_e.wf_right h
  | _, _, .trans h _ => Eq_e.wf_left h
  | _, _, .hyp q l r args _ hl _ fill => Wf_e.instantiate fill hl
  | _, _, .congr σ _ _ hσ _ _ h => Wf_e.instantiate hσ (Eq_e.wf_left h)

/-- 8(7): the right side of an equality is well formed. -/
theorem Eq_e.wf_right {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {e e' : Expr Δ}, Ξ ⊢ e ≈ e' → Ξ ⊢ e'
  | _, _, .refl h => h
  | _, _, .symm h => Eq_e.wf_left h
  | _, _, .trans _ h' => Eq_e.wf_right h'
  | _, _, .hyp q l r args _ _ hr fill => Wf_e.instantiate fill hr
  | _, _, .congr _ θ _ _ hθ _ h => Wf_e.instantiate hθ (Eq_e.wf_right h)

end

/-- 8(7): equal expressions have equal computed boundaries. -/
theorem Eq_e.boundaryOf : ∀ {Δ : C.Arity} {Ξ : Ambient Δ}, Ambient.Wf Ξ →
    ∀ {e e' : Expr Δ}, Ξ ⊢ e ≈ e' → Ξ ⊢ Ξ.boundaryOf e ≈ Ξ.boundaryOf e'
  | _, _, hΞ, _, _, .refl h => boundaryOf_refl hΞ h
  | _, _, hΞ, _, _, .symm h => (Eq_e.boundaryOf hΞ h).symm
  | _, _, hΞ, _, _, .trans h h' =>
      (Eq_e.boundaryOf hΞ h).trans (Eq_e.boundaryOf hΞ h')
  | _, Ξ, hΞ, _, _, .hyp q l r args decl hl hr fill => by
      have hb : Wf_t Ξ (Ξ.binding q) := Wf_t.binding hΞ q
      have hΞ' : Ambient.Wf (Ξ ⋈ Ξ.binding q) := Wf_t.concatenate hΞ hb
      have hdecl := Wf_bd.eq_boundary (Eq.mp
        (congrArg (Wf_bd Ξ (Ξ.binding q)) decl) (Wf_t.declaration hΞ q))
      refine Eq_bd.trans (boundaryOf_instantiate hΞ' fill hl) ?_
      refine Eq_bd.trans ?_ (boundaryOf_instantiate hΞ' fill hr).symm
      exact Eq_bd.congr args args hb fill fill fill.refl hdecl
  | _, Ξ, hΞ, _, _, .congr (Θ := Θ) σ θ hΘ hσ hθ agree h => by
      have hΞ' : Ambient.Wf (Ξ ⋈ Θ) := Wf_t.concatenate hΞ hΘ
      refine Eq_bd.trans (boundaryOf_instantiate hΞ' hσ (Eq_e.wf_left h)) ?_
      refine Eq_bd.trans ?_
        (boundaryOf_instantiate hΞ' hθ (Eq_e.wf_right h)).symm
      exact Eq_bd.congr σ θ hΘ hσ hθ agree (Eq_e.boundaryOf hΞ' h)

/-! ## Telescope equality -/

/-- 8(9): equality of telescopes is stable under a filling. -/
theorem Eq_t.filling {Γ Γ' Ω : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (F : Ambient.Filling A A' Ω) :
    ∀ {Λ : C.Arity} {T T' : dTel Γ Λ}, Eq_t A T T' →
      Eq_t A' (F.fill ⋆ T) (F.fill ⋆ T')
  | _, .nil, _, h => by
      obtain rfl := Eq_t.nil_inv h
      exact Eq_t.nil
  | _, .cons bind boundary rest, _, h => by
      obtain ⟨_, boundary', _, rfl, hbind, hboundary, hrest⟩ := Eq_t.cons_inv h
      refine Eq_t.cons (Eq_t.filling F hbind) ?_
        (Eq_t.filling (F.extend (dTel.cons bind boundary .nil)) hrest)
      refine Eq.mp (congrArg₂ (fun a b => Eq_bd (A' ⋈ F.fill ⋆ bind) a b)
        (Bd.act_lift_depth F.fill boundary)
        (Bd.act_lift_depth F.fill boundary')) ?_
      exact (substitutionAt Ω).boundaryEquality (F.extend bind) hboundary

/-- 8(9): equality of telescopes over two ambients is stable under a filling of
each by one substitution. -/
theorem Eq_t.Both.filling {Γ Γ' Ω : C.Arity} {A A₁ : Ambient Γ}
    {A' A₁' : Ambient Γ'} (F : Ambient.Filling A A' Ω)
    (F₁ : Ambient.Filling A₁ A₁' Ω) (hfill : F₁.fill = F.fill) :
    ∀ {Λ : C.Arity} {T T' : dTel Γ Λ}, Eq_t.Both A A₁ T T' →
      Eq_t.Both A' A₁' (F.fill ⋆ T) (F.fill ⋆ T')
  | _, .nil, _, h => by
      obtain rfl := Eq_t.Both.nil_inv h
      exact Eq_t.Both.nil
  | _, .cons (α := α) bind boundary rest, _, h => by
      obtain ⟨bind', boundary', rest', rfl, hbind, hboundary, hboundary', hrest⟩ :=
        Eq_t.Both.cons_inv h
      refine Eq_t.Both.cons (Eq_t.Both.filling F F₁ hfill hbind) ?first ?second ?rest
      case first =>
        refine Eq.mp (congrArg₂ (fun a b => Eq_bd ((A' ⋈ F.fill ⋆ bind)) a b)
          (Bd.act_lift_depth F.fill boundary)
          (Bd.act_lift_depth F.fill boundary')) ?_
        exact (substitutionAt Ω).boundaryEquality (F.extend bind) hboundary
      case second =>
        refine Eq.mp (congrArg (fun (s : Subst Γ Γ') =>
          Eq_bd ((A₁' ⋈ dTel.actBase s bind'))
            (Bd.act (Γ := 1) s α boundary) (Bd.act (Γ := 1) s α boundary')) hfill) ?_
        refine Eq.mp (congrArg₂ (fun a b => Eq_bd ((A₁' ⋈ F₁.fill ⋆ bind')) a b)
          (Bd.act_lift_depth F₁.fill boundary)
          (Bd.act_lift_depth F₁.fill boundary')) ?_
        exact (substitutionAt Ω).boundaryEquality (F₁.extend bind') hboundary'
      case rest =>
        refine Eq.mp (congrArg (fun (s : Subst Γ Γ') => Eq_t.Both
          ((A' ⋈ F.fill ⋆ dTel.cons bind boundary .nil))
          ((A₁' ⋈ dTel.actBase s (dTel.cons bind' boundary' .nil)))
          (dTel.actBase (Subst.lift F.fill (C.single α)) rest)
          (dTel.actBase (Subst.lift F.fill (C.single α)) rest')) hfill) ?_
        exact Eq_t.Both.filling (F.extend (dTel.cons bind boundary .nil))
          (F₁.extend (dTel.cons bind' boundary' .nil))
          (congrArg (fun s => Subst.lift s (C.single α)) hfill) hrest

/-- 8(9): equality of telescopes is stable under filling a block. -/
theorem Eq_t.subst {Δ Ω Φ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω}
    {σ : Subst Ω Δ} {Ψ : dTel (Δ ⋈ Ω) Φ} (hσ : Wf_s Ξ Θ σ) {Χ : C.Arity}
    {X X' : dTel ((Δ ⋈ Ω) ⋈ Φ) Χ} (h : Eq_t (Ξ ⋈ Θ ⋈ Ψ) X X') :
    Eq_t (Ξ ⋈ σ ⋆ Ψ) (σ ⋆ X) (σ ⋆ X') :=
  Eq_t.filling (hσ.fillBefore Ψ) h

/-! ## Substitutions between ambients -/

/-- 6.8: a substitution between ambients is well formed when at every slot it
gives a filler for that slot's declared boundary, over the target ambient
extended by the entries the slot binds. -/
def Wf_sub {Γ Γ' : C.Arity} (A : Ambient Γ) (A' : Ambient Γ') (σ : Subst Γ Γ') :
    Prop :=
  ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α),
    (∀ l r : Expr (Γ' ⋈ α), Bd.applyAt σ α (A.declaration x) = .eq l r →
        Eq_e (A' ⋈ σ ⋆ A.binding x) l r) ∧
    (¬ (Bd.applyAt σ α (A.declaration x)).isEq →
        Wf_e (A' ⋈ σ ⋆ A.binding x) (σ x)) ∧
    (¬ (Bd.applyAt σ α (A.declaration x)).isEq →
        Eq_bd (A' ⋈ σ ⋆ A.binding x)
          ((A' ⋈ σ ⋆ A.binding x).boundaryOf (σ x)) (Bd.applyAt σ α (A.declaration x)))

/-- Two substitutions between ambients agree at every non-equational slot. -/
def Eq_sub {Γ Γ' : C.Arity} (A : Ambient Γ) (A' : Ambient Γ') (σ θ : Subst Γ Γ') :
    Prop :=
  ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α), ¬ (Bd.applyAt σ α (A.declaration x)).isEq →
    Eq_e (A' ⋈ σ ⋆ A.binding x) (σ x) (θ x)

/-- The slots of an ambient weakened into another. -/
theorem Ambient.weaken_declaration {Γ Γ' α : C.Arity} (A : Ambient Γ)
    (A' : Ambient Γ') (x : Γ ∋ α) :
    (dTel.rename (Renaming.fromUnit Γ') A).declaration x
      = Bd.rename (Renaming.inr Γ' Γ ⇑ʳ α) (A.declaration x) :=
  (dTel.declaration_rename (Renaming.fromUnit Γ') A x).trans
    (congrArg (fun ρ => Bd.rename (ρ ⇑ʳ α) (A.declaration x))
      (Renaming.fromUnit_extend Γ' Γ))

/-- The entries bound by a slot of an ambient weakened into another. -/
theorem Ambient.weaken_binding {Γ Γ' α : C.Arity} (A : Ambient Γ)
    (A' : Ambient Γ') (x : Γ ∋ α) :
    (dTel.rename (Renaming.fromUnit Γ') A).binding x
      = dTel.rename (Renaming.inr Γ' Γ) (A.binding x) :=
  (dTel.binding_rename (Renaming.fromUnit Γ') A x).trans
    (congrArg (fun ρ => dTel.rename ρ (A.binding x)) (Renaming.fromUnit_extend Γ' Γ))

/-- The boundary declared at a slot of the weakened source. -/
theorem Wf_sub.declaration_weaken {Γ Γ' : C.Arity} {A : Ambient Γ}
    {A' : Ambient Γ'} (σ : Subst Γ Γ') ⦃α : C.Arity⦄ (x : Γ ∋ α) :
    Bd.fill σ ((dTel.rename (Renaming.fromUnit Γ') A).declaration x)
      = Bd.applyAt σ α (A.declaration x) :=
  (congrArg (Bd.fill σ) (Ambient.weaken_declaration A A' x)).trans
    (Bd.act_weaken σ (A.declaration x))

/-- The entries bound at a slot of the weakened source. -/
theorem Wf_sub.binding_weaken {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (σ : Subst Γ Γ') ⦃α : C.Arity⦄ (x : Γ ∋ α) :
    dTel.instantiate σ ((dTel.rename (Renaming.fromUnit Γ') A).binding x)
      = dTel.actBase σ (A.binding x) :=
  (congrArg (dTel.instantiate σ) (Ambient.weaken_binding A A' x)).trans
    (dTel.instantiate_weaken σ (A.binding x))

/-- A well-formed substitution between ambients fills the weakened source. -/
theorem Wf_sub.toFilling {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    {σ : Subst Γ Γ'} (hσ : Wf_sub A A' σ) :
    Wf_s A' (dTel.rename (Renaming.fromUnit Γ') A) σ := by
  refine Wf_s.slotwise ?equation ?filler ?declared
  case equation =>
    intro Λ z l r hlr
    refine Eq.mp (congrArg (fun T => Eq_e (A' ⋈ T) l r)
      (Wf_sub.binding_weaken (A := A) (A' := A') σ z).symm) ?_
    exact (hσ z).1 l r
      ((Wf_sub.declaration_weaken (A := A) (A' := A') σ z).symm.trans hlr)
  case filler =>
    intro Λ z hne
    refine Eq.mp (congrArg (fun T => Wf_e (A' ⋈ T) (σ z))
      (Wf_sub.binding_weaken (A := A) (A' := A') σ z).symm) ?_
    refine (hσ z).2.1 (fun hEq => hne ?_)
    exact Eq.mp (congrArg Bd.isEq
      (Wf_sub.declaration_weaken (A := A) (A' := A') σ z)).symm hEq
  case declared =>
    intro Λ z hne
    refine Eq.mp (congrArg₂ (fun (T : dTel Γ' Λ) (b : Bd (Γ' ⋈ Λ)) =>
        Eq_bd (A' ⋈ T) ((A' ⋈ T).boundaryOf (σ z)) b)
      (Wf_sub.binding_weaken (A := A) (A' := A') σ z).symm
      (Wf_sub.declaration_weaken (A := A) (A' := A') σ z).symm) ?_
    refine (hσ z).2.2 (fun hEq => hne ?_)
    exact Eq.mp (congrArg Bd.isEq
      (Wf_sub.declaration_weaken (A := A) (A' := A') σ z)).symm hEq

/-- Agreeing substitutions between ambients agree as fillings of the weakened
source. -/
theorem Eq_sub.toAgreement {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    {σ θ : Subst Γ Γ'} (hst : Eq_sub A A' σ θ) :
    Eq_s A' (dTel.rename (Renaming.fromUnit Γ') A) σ θ := by
  refine Eq_s.slotwise ?_
  intro Λ z hne
  refine Eq.mp (congrArg (fun T => Eq_e (A' ⋈ T) (σ z) (θ z))
    (Wf_sub.binding_weaken (A := A) (A' := A') σ z).symm) ?_
  refine hst z (fun hEq => hne ?_)
  exact Eq.mp (congrArg Bd.isEq
    (Wf_sub.declaration_weaken (A := A) (A' := A') σ z)).symm hEq

/-- A weakened ambient is unchanged by substitution of the base. -/
theorem Ambient.actBase_weaken {Γ Δ Ω : C.Arity} (A : Ambient Γ) (σ : Subst Δ Ω) :
    dTel.actBase σ (dTel.rename (Renaming.fromUnit Δ) A)
      = dTel.rename (Renaming.fromUnit Ω) A := by
  refine Eq.trans (dTel.actBase_square (Renaming.fromUnit Δ) (Renaming.fromUnit Ω)
    σ (Subst.id 1) (fun ⦃_⦄ x => (C.unit_is_empty x).elim) A) ?_
  exact congrArg (dTel.rename (Renaming.fromUnit Ω)) (dTel.actBase_id A)

/-- A filling of the weakened source is a substitution between ambients. -/
theorem Wf_s.toWf_sub {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    {σ : Subst Γ Γ'} (hσ : Wf_s A' (dTel.rename (Renaming.fromUnit Γ') A) σ) :
    Wf_sub A A' σ := by
  intro α x
  refine ⟨?equation, ?filler, ?declared⟩
  case equation =>
    intro l r hlr
    refine Eq.mp (congrArg (fun T => Eq_e (A' ⋈ T) l r)
      (Wf_sub.binding_weaken (A := A) (A' := A') σ x)) ?_
    exact hσ.equation x l r
      ((Wf_sub.declaration_weaken (A := A) (A' := A') σ x).trans hlr)
  case filler =>
    intro hne
    refine Eq.mp (congrArg (fun T => Wf_e (A' ⋈ T) (σ x))
      (Wf_sub.binding_weaken (A := A) (A' := A') σ x)) ?_
    refine hσ.filler x (fun hEq => hne ?_)
    exact Eq.mp (congrArg Bd.isEq
      (Wf_sub.declaration_weaken (A := A) (A' := A') σ x)) hEq
  case declared =>
    intro hne
    refine Eq.mp (congrArg₂ (fun (T : dTel Γ' α) (b : Bd (Γ' ⋈ α)) =>
        Eq_bd (A' ⋈ T) ((A' ⋈ T).boundaryOf (σ x)) b)
      (Wf_sub.binding_weaken (A := A) (A' := A') σ x)
      (Wf_sub.declaration_weaken (A := A) (A' := A') σ x)) ?_
    refine hσ.declared x (fun hEq => hne ?_)
    exact Eq.mp (congrArg Bd.isEq
      (Wf_sub.declaration_weaken (A := A) (A' := A') σ x)) hEq

/-- Fillings of the weakened source that agree agree as substitutions between
ambients. -/
theorem Eq_s.toEq_sub {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    {σ θ : Subst Γ Γ'} (hst : Eq_s A' (dTel.rename (Renaming.fromUnit Γ') A) σ θ) :
    Eq_sub A A' σ θ := by
  intro α x hne
  refine Eq.mp (congrArg (fun T => Eq_e (A' ⋈ T) (σ x) (θ x))
    (Wf_sub.binding_weaken (A := A) (A' := A') σ x)) ?_
  refine hst.slot x (fun hEq => hne ?_)
  exact Eq.mp (congrArg Bd.isEq
    (Wf_sub.declaration_weaken (A := A) (A' := A') σ x)) hEq

/-- 8(5): the identity substitution between ambients is well formed. -/
theorem Wf_sub.id {Δ : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ) :
    Wf_sub Ξ Ξ (Subst.id Δ) := by
  intro α x
  have hd : Bd.applyAt (Subst.id Δ) α (Ξ.declaration x) = Ξ.declaration x :=
    Bd.act_id Δ α (Ξ.declaration x)
  have hb : dTel.actBase (Subst.id Δ) (Ξ.binding x) = Ξ.binding x :=
    dTel.actBase_id (Ξ.binding x)
  have hcancel : ∀ e : Expr (Δ ⋈ α),
      Subst.act (Γ := Δ ⋈ α) (Δ := α) (Ξ := 1) (Subst.instId Δ α) 1
          (⟦ Renaming.inl Δ α ⇑ʳ α ⟧ʳ e) = e := by
    intro e
    refine Eq.trans (congrArg (fun ρ =>
      Subst.act (Γ := Δ ⋈ α) (Δ := α) (Ξ := 1) (Subst.instId Δ α) 1
        (Renaming.act ρ e)) (Renaming.extend_unit (Renaming.inl Δ α ⇑ʳ α)).symm) ?_
    exact act_instId_weaken Δ α (Φ := 1) e
  refine ⟨?equation, ?filler, ?declared⟩
  case equation =>
    intro l r hlr
    replace hlr := hd.symm.trans hlr
    have hbd : Wf_bd Ξ (Ξ.binding x) (Bd.eq l r) :=
      Eq.mp (congrArg (Wf_bd Ξ (Ξ.binding x)) hlr) (Wf_t.declaration hΞ x)
    have hbx : ((Ξ ⋈ Ξ.binding x)).binding (C.inl x)
        = dTel.rename (Renaming.inl Δ α) (Ξ.binding x) :=
      dTel.binding_concatenate_inl Ξ (Ξ.binding x) x
    refine Eq.mp (congrArg (fun T => Eq_e ((Ξ ⋈ T)) l r) hb.symm) ?_
    refine Eq.mp (congrArg₂ (Eq_e ((Ξ ⋈ Ξ.binding x))) (hcancel l) (hcancel r)) ?_
    refine Eq_e.hyp (Ξ := (Ξ ⋈ Ξ.binding x)) (C.inl x)
      (⟦ Renaming.inl Δ α ⇑ʳ α ⟧ʳ l) (⟦ Renaming.inl Δ α ⇑ʳ α ⟧ʳ r)
      (Subst.instId Δ α) ?decl ?hl ?hr ?fill
    case decl =>
      refine Eq.trans (dTel.declaration_concatenate_inl Ξ (Ξ.binding x) x) ?_
      exact congrArg (Bd.rename (Renaming.inl Δ α ⇑ʳ α)) hlr
    case hl =>
      refine Eq.mp (congrArg (fun T => Wf_e ((((Ξ ⋈ Ξ.binding x)) ⋈ T))
        (⟦ Renaming.inl Δ α ⇑ʳ α ⟧ʳ l)) hbx.symm) ?_
      exact Wf_e.weaken
        ((Ambient.Renaming.weaken Ξ (Ξ.binding x)).extend (Ξ.binding x))
        hbd.eq_left
    case hr =>
      refine Eq.mp (congrArg (fun T => Wf_e ((((Ξ ⋈ Ξ.binding x)) ⋈ T))
        (⟦ Renaming.inl Δ α ⇑ʳ α ⟧ʳ r)) hbx.symm) ?_
      exact Wf_e.weaken
        ((Ambient.Renaming.weaken Ξ (Ξ.binding x)).extend (Ξ.binding x))
        hbd.eq_right
    case fill =>
      exact Eq.mp (congrArg (fun T => Wf_s ((Ξ ⋈ Ξ.binding x)) T
        (Subst.instId Δ α)) hbx.symm) (Wf_s.eta Ξ (Ξ.binding x)
          (Wf_t.binding hΞ x))
  case filler =>
    intro hne
    refine Eq.mp (congrArg (fun T => Wf_e ((Ξ ⋈ T)) (Subst.id Δ x)) hb.symm) ?_
    exact Wf_e.eta Ξ x (Wf_t.binding hΞ x)
      (fun hEq => hne (Eq.mp (congrArg Bd.isEq hd.symm) hEq))
  case declared =>
    intro hne
    refine Eq.mp (congrArg₂ (fun (T : dTel Δ α) (b : Bd (Δ ⋈ α)) =>
      Eq_bd ((Ξ ⋈ T)) (((Ξ ⋈ T)).boundaryOf (Subst.id Δ x)) b) hb.symm hd.symm) ?_
    refine Eq.mp (congrArg (fun b => Eq_bd ((Ξ ⋈ Ξ.binding x)) b
      (Ξ.declaration x)) (dTel.boundaryOf_eta Ξ x).symm) ?_
    exact Wf_bd.refl (Wf_t.declaration hΞ x)

/-- A filling of a telescope is a well-formed substitution out of the ambient it
extends. -/
theorem Wf_s.toSub {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω} {σ : Subst Ω Δ}
    (hΞ : Ambient.Wf Ξ) (h : Wf_s Ξ Θ σ) :
    Wf_sub ((Ξ ⋈ Θ)) Ξ (Subst.copair (Subst.id Δ) σ) := by
  intro α x
  rcases C.cover Δ Ω x with ⟨w, rfl⟩ | ⟨z, rfl⟩
  · have hd : Bd.applyAt (Subst.copair (Subst.id Δ) σ) α
        ((Ξ ⋈ Θ).declaration (C.inl w)) = Ξ.declaration w := by
      refine Eq.trans (congrArg (Bd.applyAt (Subst.copair (Subst.id Δ) σ) α)
        (dTel.declaration_concatenate_inl Ξ Θ w)) ?_
      refine Eq.trans (Bd.act_rename_cancel (Renaming.inl Δ Ω) (𝟙ʳ Δ)
        (Subst.copair (Subst.id Δ) σ) (fun ⦃_⦄ u => Subst.copair_inl _ _ u) α
        (Ξ.declaration w)) ?_
      exact (congrArg (fun ρ => Bd.rename ρ (Ξ.declaration w))
        (Renaming.extend_id Δ α)).trans (Bd.rename_id _)
    have hb : dTel.actBase (Subst.copair (Subst.id Δ) σ)
        ((Ξ ⋈ Θ).binding (C.inl w)) = Ξ.binding w := by
      refine Eq.trans (congrArg (dTel.actBase (Subst.copair (Subst.id Δ) σ))
        (dTel.binding_concatenate_inl Ξ Θ w)) ?_
      refine Eq.trans (dTel.actBase_rename_cancel (Renaming.inl Δ Ω) (𝟙ʳ Δ)
        (Subst.copair (Subst.id Δ) σ) (fun ⦃_⦄ u => Subst.copair_inl _ _ u)
        (Ξ.binding w)) ?_
      exact dTel.rename_id _
    have hdid : Bd.applyAt (Subst.id Δ) α (Ξ.declaration w) = Ξ.declaration w :=
      Bd.act_id Δ α _
    have hbid : dTel.actBase (Subst.id Δ) (Ξ.binding w) = Ξ.binding w :=
      dTel.actBase_id _
    obtain ⟨heq, hwf, hbd⟩ := Wf_sub.id hΞ w
    refine ⟨?_, ?_, ?_⟩
    · intro l r hlr
      refine Eq.mp (congrArg (fun T => Eq_e ((Ξ ⋈ T)) l r) hb.symm) ?_
      refine Eq.mp (congrArg (fun T => Eq_e ((Ξ ⋈ T)) l r) hbid) ?_
      exact heq l r (hdid.trans (hd.symm.trans hlr))
    · intro hne
      refine Eq.mp (congrArg₂ (fun (T : dTel Δ α) (e : Expr (Δ ⋈ α)) =>
        Wf_e ((Ξ ⋈ T)) e) hb.symm (Subst.copair_inl (Subst.id Δ) σ w).symm) ?_
      refine Eq.mp (congrArg (fun T => Wf_e ((Ξ ⋈ T)) (Subst.id Δ w)) hbid) ?_
      exact hwf (fun hEq => hne (Eq.mp (congrArg Bd.isEq
        (hdid.trans hd.symm)) hEq))
    · intro hne
      refine Eq.mp (congrArg₂ (fun (T : dTel Δ α) (e : Expr (Δ ⋈ α)) =>
        Eq_bd ((Ξ ⋈ T)) (((Ξ ⋈ T)).boundaryOf e)
          (Bd.applyAt (Subst.copair (Subst.id Δ) σ) α
            ((Ξ ⋈ Θ).declaration (C.inl w))))
        hb.symm (Subst.copair_inl (Subst.id Δ) σ w).symm) ?_
      refine Eq.mp (congrArg₂ (fun (T : dTel Δ α) (b : Bd (Δ ⋈ α)) =>
        Eq_bd ((Ξ ⋈ T)) (((Ξ ⋈ T)).boundaryOf (Subst.id Δ w)) b) hbid
        (hdid.trans hd.symm)) ?_
      exact hbd (fun hEq => hne (Eq.mp (congrArg Bd.isEq (hdid.trans hd.symm)) hEq))
  · have hd : Bd.applyAt (Subst.copair (Subst.id Δ) σ) α
        ((Ξ ⋈ Θ).declaration (C.inr z)) = σ ⋆ Θ.declaration z := by
      refine Eq.trans (congrArg (Bd.applyAt (Subst.copair (Subst.id Δ) σ) α)
        (dTel.declaration_concatenate_inr Ξ Θ z)) ?_
      exact Bd.act_copair_prefix σ α (Θ.declaration z)
    have hb : dTel.actBase (Subst.copair (Subst.id Δ) σ)
        ((Ξ ⋈ Θ).binding (C.inr z)) = σ ⋆ Θ.binding z :=
      congrArg (dTel.actBase (Subst.copair (Subst.id Δ) σ))
        (dTel.binding_concatenate_inr Ξ Θ z)
    refine ⟨?_, ?_, ?_⟩
    · intro l r hlr
      refine Eq.mp (congrArg (fun T => Eq_e ((Ξ ⋈ T)) l r) hb.symm) ?_
      exact h.equation z l r (hd.symm.trans hlr)
    · intro hne
      refine Eq.mp (congrArg₂ (fun (T : dTel Δ α) (e : Expr (Δ ⋈ α)) =>
        Wf_e ((Ξ ⋈ T)) e) hb.symm (Subst.copair_inr (Subst.id Δ) σ z).symm) ?_
      exact h.filler z (fun hEq => hne (Eq.mp (congrArg Bd.isEq hd).symm hEq))
    · intro hne
      refine Eq.mp (congrArg₂ (fun (T : dTel Δ α) (e : Expr (Δ ⋈ α)) =>
        Eq_bd ((Ξ ⋈ T)) (((Ξ ⋈ T)).boundaryOf e)
          (Bd.applyAt (Subst.copair (Subst.id Δ) σ) α
            ((Ξ ⋈ Θ).declaration (C.inr z))))
        hb.symm (Subst.copair_inr (Subst.id Δ) σ z).symm) ?_
      refine Eq.mp (congrArg (fun b => Eq_bd ((Ξ ⋈ σ ⋆ Θ.binding z))
        (((Ξ ⋈ σ ⋆ Θ.binding z)).boundaryOf (σ z)) b) hd.symm) ?_
      exact h.declared z (fun hEq => hne (Eq.mp (congrArg Bd.isEq hd).symm hEq))

/-- Agreeing fillings of a telescope agree as substitutions out of the ambient it
extends. -/
theorem Eq_s.toSub {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω}
    {σ θ : Subst Ω Δ} (hΞ : Ambient.Wf Ξ) (h : Eq_s Ξ Θ σ θ) :
    Eq_sub ((Ξ ⋈ Θ)) Ξ (Subst.copair (Subst.id Δ) σ)
      (Subst.copair (Subst.id Δ) θ) := by
  intro α x
  rcases C.cover Δ Ω x with ⟨w, rfl⟩ | ⟨z, rfl⟩
  · have hd : Bd.applyAt (Subst.copair (Subst.id Δ) σ) α
        ((Ξ ⋈ Θ).declaration (C.inl w)) = Ξ.declaration w := by
      refine Eq.trans (congrArg (Bd.applyAt (Subst.copair (Subst.id Δ) σ) α)
        (dTel.declaration_concatenate_inl Ξ Θ w)) ?_
      refine Eq.trans (Bd.act_rename_cancel (Renaming.inl Δ Ω) (𝟙ʳ Δ)
        (Subst.copair (Subst.id Δ) σ) (fun ⦃_⦄ u => Subst.copair_inl _ _ u) α
        (Ξ.declaration w)) ?_
      exact (congrArg (fun ρ => Bd.rename ρ (Ξ.declaration w))
        (Renaming.extend_id Δ α)).trans (Bd.rename_id _)
    have hb : dTel.actBase (Subst.copair (Subst.id Δ) σ)
        ((Ξ ⋈ Θ).binding (C.inl w)) = Ξ.binding w := by
      refine Eq.trans (congrArg (dTel.actBase (Subst.copair (Subst.id Δ) σ))
        (dTel.binding_concatenate_inl Ξ Θ w)) ?_
      refine Eq.trans (dTel.actBase_rename_cancel (Renaming.inl Δ Ω) (𝟙ʳ Δ)
        (Subst.copair (Subst.id Δ) σ) (fun ⦃_⦄ u => Subst.copair_inl _ _ u)
        (Ξ.binding w)) ?_
      exact dTel.rename_id _
    intro hne
    refine Eq.mp (congrArg (fun (e : Expr (Δ ⋈ α)) =>
      Eq_e ((Ξ ⋈ Subst.copair (Subst.id Δ) σ ⋆ (Ξ ⋈ Θ).binding (C.inl w)))
        (Subst.copair (Subst.id Δ) σ (C.inl w)) e)
      (Subst.copair_inl (Subst.id Δ) θ w).symm) ?_
    refine Eq.mp (congrArg₂ (fun (T : dTel Δ α) (e : Expr (Δ ⋈ α)) =>
      Eq_e ((Ξ ⋈ T)) e (Subst.id Δ w)) hb.symm
      (Subst.copair_inl (Subst.id Δ) σ w).symm) ?_
    exact Eq_e.refl (Wf_e.eta Ξ w (Wf_t.binding hΞ w)
      (fun hEq => hne (Eq.mp (congrArg Bd.isEq hd).symm hEq)))
  · have hd : Bd.applyAt (Subst.copair (Subst.id Δ) σ) α
        ((Ξ ⋈ Θ).declaration (C.inr z)) = σ ⋆ Θ.declaration z := by
      refine Eq.trans (congrArg (Bd.applyAt (Subst.copair (Subst.id Δ) σ) α)
        (dTel.declaration_concatenate_inr Ξ Θ z)) ?_
      exact Bd.act_copair_prefix σ α (Θ.declaration z)
    have hb : dTel.actBase (Subst.copair (Subst.id Δ) σ)
        ((Ξ ⋈ Θ).binding (C.inr z)) = σ ⋆ Θ.binding z :=
      congrArg (dTel.actBase (Subst.copair (Subst.id Δ) σ))
        (dTel.binding_concatenate_inr Ξ Θ z)
    intro hne
    refine Eq.mp (congrArg₂ (fun (T : dTel Δ α) (e : Expr (Δ ⋈ α)) =>
      Eq_e ((Ξ ⋈ T)) e (Subst.copair (Subst.id Δ) θ (C.inr z)))
      hb.symm (Subst.copair_inr (Subst.id Δ) σ z).symm) ?_
    refine Eq.mp (congrArg (fun e => Eq_e ((Ξ ⋈ σ ⋆ Θ.binding z)) (σ z) e)
      (Subst.copair_inr (Subst.id Δ) θ z).symm) ?_
    exact h.slot z (fun hEq => hne (Eq.mp (congrArg Bd.isEq hd).symm hEq))

/-- 8(9): agreeing substitutions send a well-formed expression to equal
expressions. -/
theorem Eq_e.agree {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    {σ θ : Subst Γ Γ'} (hA : Ambient.Wf A) (hσ : Wf_sub A A' σ)
    (hθ : Wf_sub A A' θ) (hst : Eq_sub A A' σ θ) {e : Expr Γ} (h : A ⊢ e) :
    A' ⊢ σ ⋆ e ≈ θ ⋆ e := by
  have hbridge : ∀ s : Subst Γ Γ',
      Subst.instantiate s (⟦ Renaming.inr Γ' Γ ⟧ʳ e) = Subst.apply s e := by
    intro s
    refine Eq.trans (act_copair_prefix s 1 (⟦ Renaming.inr Γ' Γ ⟧ʳ e)).symm ?_
    refine Eq.trans (congrArg (fun ρ =>
      Subst.act (Γ := 1) (Δ := Γ' ⋈ Γ) (Ξ := Γ') (Subst.copair (Subst.id Γ') s) 1
        (Renaming.act ρ e)) (Renaming.extend_unit (Renaming.inr Γ' Γ)).symm) ?_
    exact act_copair_inr s 1 e
  refine Eq.mp (congrArg₂ (Eq_e A') (hbridge σ) (hbridge θ)) ?_
  exact Eq_e.congr (Ξ := A') (Θ := dTel.rename (Renaming.fromUnit Γ') A) σ θ
    (Ambient.Wf.weaken hA A') hσ.toFilling hθ.toFilling hst.toAgreement
    (Eq_e.refl (Wf_e.weaken (Ambient.Renaming.weakenInto A A') h))

/-- 8(3) for a substitution between ambients. -/
theorem Wf_e.subst_ambient {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    {σ : Subst Γ Γ'} (hσ : Wf_sub A A' σ) {e : Expr Γ} (h : A ⊢ e) : A' ⊢ σ ⋆ e := by
  refine Eq.mp (congrArg (Wf_e A')
    ((act_copair_prefix σ 1 (⟦ Renaming.inr Γ' Γ ⟧ʳ e)).trans
      (Subst.instantiate_weaken σ e))) ?_
  exact (substitutionAt Γ).expr (Wf_s.filling hσ.toFilling)
    (Wf_e.weaken (Ambient.Renaming.weakenInto A A') h)

/-- 8(9) for a substitution between ambients. -/
theorem Wf_t.subst_ambient {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    {σ : Subst Γ Γ'} (hσ : Wf_sub A A' σ) {Χ : C.Arity} {T : dTel Γ Χ}
    (hT : Wf_t A T) : Wf_t A' (σ ⋆ T) := by
  refine Eq.mp (congrArg (Wf_t A') (dTel.instantiate_weaken σ T)) ?_
  exact (substitutionAt Γ).telescope (Wf_s.filling hσ.toFilling)
    (Wf_t.weaken (Ambient.Renaming.weakenInto A A') hT)

/-- 8(4) for a substitution between ambients. -/
theorem Wf_s.subst_ambient {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    {σ : Subst Γ Γ'} (hσ : Wf_sub A A' σ) {Χ : C.Arity} {X : dTel Γ Χ}
    {τ : Subst Χ Γ} (h : Wf_s A X τ) : Wf_s A' (σ ⋆ X) (σ ⋆ τ) := by
  have hτ : (fun ⦃Λ : C.Arity⦄ (i : Χ ∋ Λ) =>
      Subst.act (Γ := 1) (Subst.copair (Subst.id Γ') σ) Λ
        (⟦ Renaming.inr Γ' Γ ⇑ʳ Λ ⟧ʳ (τ i))) = Subst.applyEach σ τ := by
    funext Λ i
    exact act_copair_inr σ Λ (τ i)
  refine Eq.mp (congrArg₂ (fun (T : dTel Γ' Χ) (s : Subst Χ Γ') => Wf_s A' T s)
    (dTel.instantiate_weaken σ X) hτ) ?_
  exact (substitutionAt Γ).filling (Wf_s.filling hσ.toFilling)
    (Wf_s.weaken (Ambient.Renaming.weakenInto A A') h)

/-- 8(4): substitutions between ambients compose. -/
theorem Wf_sub.comp {Γ Δ Ω : C.Arity} {A : Ambient Γ} {B : Ambient Δ}
    {D : Ambient Ω} {τ : Subst Γ Δ} {σ : Subst Δ Ω}
    (hτ : Wf_sub A B τ) (hσ : Wf_sub B D σ) :
    Wf_sub A D (Subst.comp (Γ := 1) τ σ) := by
  refine Wf_s.toWf_sub (Eq.mp (congrArg
    (fun T => Wf_s D T (Subst.applyEach σ τ)) (Ambient.actBase_weaken A σ)) ?_)
  exact Wf_s.subst_ambient hσ hτ.toFilling

/-- 8(9) for a substitution between ambients. -/
theorem Eq_s.subst_ambient {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    {σ : Subst Γ Γ'} (hσ : Wf_sub A A' σ) {Χ : C.Arity} {X : dTel Γ Χ}
    {τ θ : Subst Χ Γ} (h : Eq_s A X τ θ) : Eq_s A' (σ ⋆ X) (σ ⋆ τ) (σ ⋆ θ) := by
  have hcomp : ∀ κ : Subst Χ Γ, (fun ⦃Λ : C.Arity⦄ (i : Χ ∋ Λ) =>
      Subst.act (Γ := 1) (Subst.copair (Subst.id Γ') σ) Λ
        (⟦ Renaming.inr Γ' Γ ⇑ʳ Λ ⟧ʳ (κ i))) = Subst.applyEach σ κ := by
    intro κ
    funext Λ i
    exact act_copair_inr σ Λ (κ i)
  rw [← dTel.instantiate_weaken σ X, ← hcomp τ, ← hcomp θ]
  exact Eq_s.subst_step (fun ⦃_⦄ _ => substitutionAt _) (Wf_s.filling hσ.toFilling)
    (Eq_s.weaken (Ambient.Renaming.weakenInto A A') h)

/-- A well-formed substitution between ambients agrees with itself. -/
theorem Eq_sub.refl {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    {σ : Subst Γ Γ'} (hσ : Wf_sub A A' σ) : Eq_sub A A' σ σ :=
  Eq_s.toEq_sub (Eq_s.refl hσ.toFilling)

/-- The source of a lifted substitution splits into the two ambients. -/
theorem Ambient.weaken_concatenate {Γ Γ' Χ : C.Arity} (A : Ambient Γ) (T : dTel Γ Χ) :
    dTel.rename (Renaming.fromUnit (Γ' ⋈ Χ)) (A ⋈ T)
      = dTel.rename (Renaming.inl Γ' Χ) (dTel.rename (Renaming.fromUnit Γ') A)
        ⋈ dTel.rename (Renaming.fromUnit (Γ' ⋈ Χ) ⇑ʳ Γ) T := by
  refine Eq.trans (dTel.rename_concatenate (Renaming.fromUnit (Γ' ⋈ Χ)) A T) ?_
  refine congrArg (fun U => dTel.concatenate U
    (dTel.rename (Renaming.fromUnit (Γ' ⋈ Χ) ⇑ʳ Γ) T)) ?_
  refine Eq.trans (congrArg (fun ρ => dTel.rename ρ A)
    (Renaming.eq_fromUnit (Renaming.inl Γ' Χ ∘ʳ Renaming.fromUnit Γ')).symm) ?_
  exact dTel.rename_comp (Renaming.fromUnit Γ') (Renaming.inl Γ' Χ) A

/-- A well-formed substitution between ambients extends past a telescope. -/
theorem Wf_sub.lift {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    {σ : Subst Γ Γ'} (hσ : Wf_sub A A' σ) {Χ : C.Arity} {T : dTel Γ Χ}
    (hT : Wf_t A T) : Wf_sub (A ⋈ T) (A' ⋈ σ ⋆ T) (Subst.lift σ Χ) := by
  intro α x
  rcases C.cover Γ Χ x with ⟨w, rfl⟩ | ⟨i, rfl⟩
  · have hd : Bd.applyAt (Subst.lift σ Χ) α ((A ⋈ T).declaration (C.inl w))
        = Bd.rename (Renaming.inl Γ' Χ ⇑ʳ α) (Bd.applyAt σ α (A.declaration w)) := by
      refine Eq.trans (congrArg (Bd.applyAt (Subst.lift σ Χ) α)
        (dTel.declaration_concatenate_inl A T w)) ?_
      exact Bd.act_square (Renaming.inl Γ Χ) (Renaming.inl Γ' Χ)
        (Subst.lift σ Χ) σ (fun ⦃_⦄ u => Subst.lift_inl σ u) α (A.declaration w)
    have hb : dTel.actBase (Subst.lift σ Χ) ((A ⋈ T).binding (C.inl w))
        = dTel.rename (Renaming.inl Γ' Χ) (dTel.actBase σ (A.binding w)) := by
      refine Eq.trans (congrArg (dTel.actBase (Subst.lift σ Χ))
        (dTel.binding_concatenate_inl A T w)) ?_
      exact dTel.actBase_square (Renaming.inl Γ Χ) (Renaming.inl Γ' Χ)
        (Subst.lift σ Χ) σ (fun ⦃_⦄ u => Subst.lift_inl σ u) (A.binding w)
    have hne : ¬ (Bd.applyAt (Subst.lift σ Χ) α ((A ⋈ T).declaration (C.inl w))).isEq →
        ¬ (Bd.applyAt σ α (A.declaration w)).isEq := by
      refine fun h hEq => h ?_
      exact Eq.mp (congrArg Bd.isEq hd).symm
        ((Bd.isEq_rename (Renaming.inl Γ' Χ ⇑ʳ α) _).mpr hEq)
    refine ⟨?_, ?_, ?_⟩
    · intro l r hlr
      replace hlr := hd.symm.trans hlr
      cases hc : Bd.applyAt σ α (A.declaration w) with
      | sort =>
          rw [hc] at hlr
          cases (Bd.rename_sort _).symm.trans hlr
      | of S =>
          rw [hc] at hlr
          cases (Bd.rename_of _ _).symm.trans hlr
      | eq l₀ r₀ =>
          rw [hc] at hlr
          replace hlr := (Bd.rename_eq _ _ _).symm.trans hlr
          injection hlr with hl hr
          subst hl
          subst hr
          refine Eq.mp (congrArg (fun U => Eq_e (A' ⋈ dTel.actBase σ T ⋈ U)
            (⟦ Renaming.inl Γ' Χ ⇑ʳ α ⟧ʳ l₀)
            (⟦ Renaming.inl Γ' Χ ⇑ʳ α ⟧ʳ r₀)) hb.symm) ?_
          exact Eq_e.weaken ((Ambient.Renaming.weaken A' (dTel.actBase σ T)).extend
            (dTel.actBase σ (A.binding w))) ((hσ w).1 l₀ r₀ hc)
    · intro h
      refine Eq.mp (congrArg (fun U => Wf_e (A' ⋈ dTel.actBase σ T ⋈ U)
        (Subst.lift σ Χ (C.inl w))) hb.symm) ?_
      refine Eq.mp (congrArg (fun e => Wf_e (A' ⋈ dTel.actBase σ T ⋈
        dTel.rename (Renaming.inl Γ' Χ) (dTel.actBase σ (A.binding w))) e)
        (Subst.lift_inl σ w).symm) ?_
      exact Wf_e.weaken ((Ambient.Renaming.weaken A' (dTel.actBase σ T)).extend
        (dTel.actBase σ (A.binding w))) ((hσ w).2.1 (hne h))
    · intro h
      refine Eq.mp (congrArg₂ (fun (U : dTel (Γ' ⋈ Χ) α) (b : Bd ((Γ' ⋈ Χ) ⋈ α)) =>
          Eq_bd (A' ⋈ dTel.actBase σ T ⋈ U)
            ((A' ⋈ dTel.actBase σ T ⋈ U).boundaryOf (Subst.lift σ Χ (C.inl w))) b)
        hb.symm hd.symm) ?_
      refine Eq.mp (congrArg (fun e =>
        Eq_bd (A' ⋈ dTel.actBase σ T ⋈
            dTel.rename (Renaming.inl Γ' Χ) (dTel.actBase σ (A.binding w)))
          ((A' ⋈ dTel.actBase σ T ⋈
            dTel.rename (Renaming.inl Γ' Χ)
              (dTel.actBase σ (A.binding w))).boundaryOf e)
          (Bd.rename (Renaming.inl Γ' Χ ⇑ʳ α) (Bd.applyAt σ α (A.declaration w))))
        (Subst.lift_inl σ w).symm) ?_
      refine Eq.mp (congrArg (fun b =>
        Eq_bd (A' ⋈ dTel.actBase σ T ⋈
            dTel.rename (Renaming.inl Γ' Χ) (dTel.actBase σ (A.binding w))) b
          (Bd.rename (Renaming.inl Γ' Χ ⇑ʳ α) (Bd.applyAt σ α (A.declaration w))))
        (Ambient.Renaming.boundaryOf
          ((Ambient.Renaming.weaken A' (dTel.actBase σ T)).extend
            (dTel.actBase σ (A.binding w))) (σ w)).symm) ?_
      exact Eq_bd.weaken ((Ambient.Renaming.weaken A' (dTel.actBase σ T)).extend
        (dTel.actBase σ (A.binding w))) ((hσ w).2.2 (hne h))
  · have hd : Bd.applyAt (Subst.lift σ Χ) α ((A ⋈ T).declaration (C.inr i))
        = (dTel.actBase σ T).declaration i :=
      (congrArg (Bd.applyAt (Subst.lift σ Χ) α)
        (dTel.declaration_concatenate_inr A T i)).trans
        (dTel.declaration_actBase σ T i).symm
    have hb : dTel.actBase (Subst.lift σ Χ) ((A ⋈ T).binding (C.inr i))
        = (dTel.actBase σ T).binding i :=
      (congrArg (dTel.actBase (Subst.lift σ Χ))
        (dTel.binding_concatenate_inr A T i)).trans
        (dTel.binding_actBase σ T i).symm
    have hT := Wf_s.eta A' (dTel.actBase σ T)
      (Wf_t.subst_ambient hσ hT)
    have hde := dTel.act_declaration_instId (dTel.actBase σ T) i
    have hbe := dTel.instantiate_binding_instId (dTel.actBase σ T) i
    have hamb := hbe.trans hb.symm
    have hbd := hde.trans hd.symm
    have hne : ¬ (Bd.applyAt (Subst.lift σ Χ) α ((A ⋈ T).declaration (C.inr i))).isEq →
        ¬ (Subst.instId Γ' Χ ⋆ (dTel.rename (Renaming.inl Γ' Χ)
            (dTel.actBase σ T)).declaration i).isEq :=
      fun h hEq => h (Eq.mp (congrArg Bd.isEq hbd) hEq)
    refine ⟨?_, ?_, ?_⟩
    · intro l r hlr
      refine Eq.mp (congrArg (fun U =>
        Eq_e (A' ⋈ dTel.actBase σ T ⋈ U) l r) hamb) ?_
      exact hT.equation i l r (hbd.trans hlr)
    · intro h
      refine Eq.mp (congrArg (fun U =>
        Wf_e (A' ⋈ dTel.actBase σ T ⋈ U) (Subst.lift σ Χ (C.inr i))) hamb) ?_
      refine Eq.mp (congrArg (fun e =>
        Wf_e (A' ⋈ dTel.actBase σ T ⋈ Subst.instId Γ' Χ ⋆
          (dTel.rename (Renaming.inl Γ' Χ) (dTel.actBase σ T)).binding i) e)
        (Subst.lift_inr σ i).symm) ?_
      exact hT.filler i (hne h)
    · intro h
      refine Eq.mp (congrArg₂ (fun (U : dTel (Γ' ⋈ Χ) α) (b : Bd ((Γ' ⋈ Χ) ⋈ α)) =>
          Eq_bd (A' ⋈ dTel.actBase σ T ⋈ U)
            ((A' ⋈ dTel.actBase σ T ⋈ U).boundaryOf (Subst.lift σ Χ (C.inr i))) b)
        hamb hbd) ?_
      refine Eq.mp (congrArg (fun e =>
        Eq_bd (A' ⋈ dTel.actBase σ T ⋈ Subst.instId Γ' Χ ⋆
            (dTel.rename (Renaming.inl Γ' Χ) (dTel.actBase σ T)).binding i)
          ((A' ⋈ dTel.actBase σ T ⋈ Subst.instId Γ' Χ ⋆
            (dTel.rename (Renaming.inl Γ' Χ) (dTel.actBase σ T)).binding i).boundaryOf e)
          (Subst.instId Γ' Χ ⋆ (dTel.rename (Renaming.inl Γ' Χ)
            (dTel.actBase σ T)).declaration i)) (Subst.lift_inr σ i).symm) ?_
      exact hT.declared i (hne h)

/-- Agreement extends past a telescope. -/
theorem Eq_sub.lift {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    {σ θ : Subst Γ Γ'} (hσ : Wf_sub A A' σ) {Χ : C.Arity} {T : dTel Γ Χ}
    (hT : Wf_t A T) (hst : Eq_sub A A' σ θ) :
    Eq_sub (A ⋈ T) (A' ⋈ σ ⋆ T) (Subst.lift σ Χ) (Subst.lift θ Χ) := by
  intro α x
  rcases C.cover Γ Χ x with ⟨w, rfl⟩ | ⟨i, rfl⟩
  · have hd : Bd.applyAt (Subst.lift σ Χ) α ((A ⋈ T).declaration (C.inl w))
        = Bd.rename (Renaming.inl Γ' Χ ⇑ʳ α) (Bd.applyAt σ α (A.declaration w)) := by
      refine Eq.trans (congrArg (Bd.applyAt (Subst.lift σ Χ) α)
        (dTel.declaration_concatenate_inl A T w)) ?_
      exact Bd.act_square (Renaming.inl Γ Χ) (Renaming.inl Γ' Χ)
        (Subst.lift σ Χ) σ (fun ⦃_⦄ u => Subst.lift_inl σ u) α (A.declaration w)
    have hb : dTel.actBase (Subst.lift σ Χ) ((A ⋈ T).binding (C.inl w))
        = dTel.rename (Renaming.inl Γ' Χ) (dTel.actBase σ (A.binding w)) := by
      refine Eq.trans (congrArg (dTel.actBase (Subst.lift σ Χ))
        (dTel.binding_concatenate_inl A T w)) ?_
      exact dTel.actBase_square (Renaming.inl Γ Χ) (Renaming.inl Γ' Χ)
        (Subst.lift σ Χ) σ (fun ⦃_⦄ u => Subst.lift_inl σ u) (A.binding w)
    intro h
    refine Eq.mp (congrArg (fun U => Eq_e (A' ⋈ dTel.actBase σ T ⋈ U)
      (Subst.lift σ Χ (C.inl w)) (Subst.lift θ Χ (C.inl w))) hb.symm) ?_
    refine Eq.mp (congrArg₂ (fun (a b : Expr ((Γ' ⋈ Χ) ⋈ α)) =>
        Eq_e (A' ⋈ dTel.actBase σ T ⋈
          dTel.rename (Renaming.inl Γ' Χ) (dTel.actBase σ (A.binding w))) a b)
      (Subst.lift_inl σ w).symm (Subst.lift_inl θ w).symm) ?_
    refine Eq_e.weaken ((Ambient.Renaming.weaken A' (dTel.actBase σ T)).extend
      (dTel.actBase σ (A.binding w))) (hst w (fun hEq => h ?_))
    exact Eq.mp (congrArg Bd.isEq hd).symm
      ((Bd.isEq_rename (Renaming.inl Γ' Χ ⇑ʳ α) _).mpr hEq)
  · have hb : dTel.actBase (Subst.lift σ Χ) ((A ⋈ T).binding (C.inr i))
        = (dTel.actBase σ T).binding i :=
      (congrArg (dTel.actBase (Subst.lift σ Χ))
        (dTel.binding_concatenate_inr A T i)).trans
        (dTel.binding_actBase σ T i).symm
    have hd : Bd.applyAt (Subst.lift σ Χ) α ((A ⋈ T).declaration (C.inr i))
        = (dTel.actBase σ T).declaration i :=
      (congrArg (Bd.applyAt (Subst.lift σ Χ) α)
        (dTel.declaration_concatenate_inr A T i)).trans
        (dTel.declaration_actBase σ T i).symm
    have hT := Wf_s.eta A' (dTel.actBase σ T)
      (Wf_t.subst_ambient hσ hT)
    have hde := dTel.act_declaration_instId (dTel.actBase σ T) i
    have hbe := dTel.instantiate_binding_instId (dTel.actBase σ T) i
    intro h
    refine Eq.mp (congrArg (fun U => Eq_e (A' ⋈ dTel.actBase σ T ⋈ U)
      (Subst.lift σ Χ (C.inr i)) (Subst.lift θ Χ (C.inr i))) (hbe.trans hb.symm)) ?_
    refine Eq.mp (congrArg₂ (fun (a b : Expr ((Γ' ⋈ Χ) ⋈ α)) =>
        Eq_e (A' ⋈ dTel.actBase σ T ⋈ Subst.instId Γ' Χ ⋆
          (dTel.rename (Renaming.inl Γ' Χ) (dTel.actBase σ T)).binding i) a b)
      (Subst.lift_inr σ i).symm (Subst.lift_inr θ i).symm) ?_
    exact Eq_e.refl (hT.filler i (fun hEq => h
      (Eq.mp (congrArg Bd.isEq (hde.trans hd.symm)) hEq)))

/-- 8(9): agreeing substitutions send a boundary equal to itself to equal
boundaries. -/
theorem Eq_bd.agree {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    {σ θ : Subst Γ Γ'} (hA : Ambient.Wf A) (hσ : Wf_sub A A' σ)
    (hθ : Wf_sub A A' θ) (hst : Eq_sub A A' σ θ) :
    ∀ {β : Bd Γ}, A ⊢ β ≈ β → A' ⊢ σ ⋆ β ≈ θ ⋆ β
  | _, .sort => .sort
  | _, .of h => .of (Eq_e.agree hA hσ hθ hst h.wf_left)
  | _, .eq hl hr =>
      .eq (Eq_e.agree hA hσ hθ hst hl.wf_left) (Eq_e.agree hA hσ hθ hst hr.wf_left)
