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
    · obtain ⟨equation, filler, declared⟩ := h
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
      have hd : ∀ ⦃Λ : C.Arity⦄ (z : Ω₀ ∋ Λ),
          Bd.act (Γ := Γ') (Δ := Ω₀) (Ξ := 1)
              (F.fill ⋆ s) Λ
              ((dTel.actBase F.fill Θ₀).declaration z)
            = Bd.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ
                (Bd.act (Γ := Γ) (Δ := Ω₀) (Ξ := 1) s Λ (Θ₀.declaration z)) := by
        intro Λ z
        refine Eq.trans (congrArg (Bd.act (Γ := Γ') (Δ := Ω₀) (Ξ := 1)
          (F.fill ⋆ s) Λ)
          (dTel.declaration_actBase F.fill Θ₀ z)) ?_
        exact Bd.act_lift_fillers F.fill s (Θ₀.declaration z)
      have hb : ∀ ⦃Λ : C.Arity⦄ (z : Ω₀ ∋ Λ),
          dTel.instantiate
              (F.fill ⋆ s)
              ((dTel.actBase F.fill Θ₀).binding z)
            = dTel.actBase F.fill (dTel.instantiate s (Θ₀.binding z)) := by
        intro Λ z
        refine Eq.trans (congrArg (dTel.instantiate
          (F.fill ⋆ s))
          (dTel.binding_actBase F.fill Θ₀ z)) ?_
        exact (dTel.actBase_instantiate F.fill s (Θ₀.binding z)).symm
      refine Eq.mp (congrArg₂ (fun a b => Eq_e A' a b)
        (Subst.act_lift_fillers (Χ := Ω₀) (Λ := 1) F.fill s e₀)
        (Subst.act_lift_fillers (Χ := Ω₀) (Λ := 1) F.fill t e₀')) ?_
      refine Eq_e.congr (Ξ := A') (Θ := dTel.actBase F.fill Θ₀)
        (F.fill ⋆ s)
        (F.fill ⋆ t)
        (Wf_t.subst_step ih F hΘ₀) (Wf_s.subst_step ih F hs) (Wf_s.subst_step ih F ht)
        ?agree
        (Eq_e.subst_step ih (F.extend Θ₀) h)
      case agree =>
        intro Λ z hne
        refine Eq.mp ?_ (Eq_e.subst_step ih (F.extend (dTel.instantiate s (Θ₀.binding z)))
          (agree z (fun hEq => hne (Eq.mp (congrArg Bd.isEq (hd z)).symm
            ((Bd.isEq_act (Γ := 1) F.fill Λ _).mpr hEq)))))
        refine Eq.trans (congrArg₂ (fun a b =>
            Eq_e (A' ⋈ F.fill ⋆ dTel.instantiate s (Θ₀.binding z)) a b)
          (Subst.act_lift_depth F.fill (s z)) (Subst.act_lift_depth F.fill (t z))) ?_
        exact congrArg (fun S => Eq_e ((A' ⋈ S))
            (Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ (s z))
            (Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ (t z))) (hb z).symm

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
  | Χ, X, τ, .mk equation filler declared => by
      have hd : ∀ ⦃Λ : C.Arity⦄ (z : Χ ∋ Λ),
          Bd.act (Γ := Γ') (Δ := Χ) (Ξ := 1)
              (F.fill ⋆ τ) Λ
              ((dTel.actBase F.fill X).declaration z)
            = Bd.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ
                (Bd.act (Γ := Γ) (Δ := Χ) (Ξ := 1) τ Λ (X.declaration z)) := by
        intro Λ z
        refine Eq.trans (congrArg (Bd.act (Γ := Γ') (Δ := Χ) (Ξ := 1)
          (F.fill ⋆ τ) Λ)
          (dTel.declaration_actBase F.fill X z)) ?_
        exact Bd.act_lift_fillers F.fill τ (X.declaration z)
      have hb : ∀ ⦃Λ : C.Arity⦄ (z : Χ ∋ Λ),
          dTel.instantiate
              (F.fill ⋆ τ)
              ((dTel.actBase F.fill X).binding z)
            = dTel.actBase F.fill (dTel.instantiate τ (X.binding z)) := by
        intro Λ z
        refine Eq.trans (congrArg (dTel.instantiate
          (F.fill ⋆ τ))
          (dTel.binding_actBase F.fill X z)) ?_
        exact (dTel.actBase_instantiate F.fill τ (X.binding z)).symm
      have hne : ∀ ⦃Λ : C.Arity⦄ (z : Χ ∋ Λ),
          ¬ (Bd.act (Γ := Γ') (Δ := Χ) (Ξ := 1)
              (F.fill ⋆ τ) Λ
              ((dTel.actBase F.fill X).declaration z)).isEq →
          ¬ (Bd.act (Γ := Γ) (Δ := Χ) (Ξ := 1) τ Λ (X.declaration z)).isEq := by
        intro Λ z h hEq
        exact h ((hd z) ▸ (Bd.isEq_act (Γ := 1) F.fill Λ _).mpr hEq)
      refine Wf_s.mk ?equation ?filler ?declared
      case equation =>
        intro Λ z l r hlr
        replace hlr := (hd z).symm.trans hlr
        cases hc : Bd.act (Γ := Γ) (Δ := Χ) (Ξ := 1) τ Λ (X.declaration z) with
        | sort =>
            rw [hc] at hlr
            cases (Bd.act_sort _ _).symm.trans hlr
        | of S =>
            rw [hc] at hlr
            cases (Bd.act_of _ _ _).symm.trans hlr
        | eq l₀ r₀ =>
            rw [hc] at hlr
            replace hlr := (Bd.act_eq _ _ _ _).symm.trans hlr
            injection hlr with hl hr
            subst hl
            subst hr
            refine Eq.mp ?_ (Eq_e.subst_step ih
              (F.extend (dTel.instantiate τ (X.binding z))) (equation z l₀ r₀ hc))
            refine Eq.trans (congrArg₂ (fun a b =>
                Eq_e (A' ⋈ F.fill ⋆ dTel.instantiate τ (X.binding z)) a b)
              (Subst.act_lift_depth F.fill l₀) (Subst.act_lift_depth F.fill r₀)) ?_
            exact congrArg (fun S => Eq_e ((A' ⋈ S))
                (Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ l₀)
                (Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ r₀)) (hb z).symm
      case filler =>
        intro Λ z h
        refine Eq.mp ?_ (Wf_e.subst_step ih
          (F.extend (dTel.instantiate τ (X.binding z))) (filler z (hne z h)))
        refine Eq.trans (congrArg (fun e =>
            Wf_e (A' ⋈ F.fill ⋆ dTel.instantiate τ (X.binding z)) e)
          (Subst.act_lift_depth F.fill (τ z))) ?_
        exact congrArg (fun S => Wf_e ((A' ⋈ S))
          (Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ (τ z))) (hb z).symm
      case declared =>
        intro Λ z h
        refine Eq.mp ?_ (Eq_bd.trans
          (boundaryOf_subst_step ih (F.extend (dTel.instantiate τ (X.binding z)))
            (filler z (hne z h))
            (Eq_bd.trans
              (Eq_bd.subst_step ih (F.extend (dTel.instantiate τ (X.binding z)))
                (declared z (hne z h)))
              (Eq_bd.subst_step ih (F.extend (dTel.instantiate τ (X.binding z)))
                (declared z (hne z h))).symm))
          (Eq_bd.subst_step ih (F.extend (dTel.instantiate τ (X.binding z)))
            (declared z (hne z h))))
        refine Eq.trans (congrArg (fun e =>
            Eq_bd (A' ⋈ F.fill ⋆ dTel.instantiate τ (X.binding z))
              ((A' ⋈ F.fill ⋆ dTel.instantiate τ (X.binding z)).boundaryOf e)
              (Bd.act (Γ := 1) (Δ := Γ ⋈ Λ) (Ξ := Γ' ⋈ Λ) (Subst.lift F.fill Λ) 1
                (Bd.act (Γ := Γ) (Δ := Χ) (Ξ := 1) τ Λ (X.declaration z))))
          (Subst.act_lift_depth F.fill (τ z))) ?_
        refine Eq.trans (congrArg (fun b =>
            Eq_bd (A' ⋈ F.fill ⋆ dTel.instantiate τ (X.binding z))
              ((A' ⋈ F.fill ⋆ dTel.instantiate τ (X.binding z)).boundaryOf
                (Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ (τ z))) b)
          ((Bd.act_lift_depth F.fill
              (Bd.act (Γ := Γ) (Δ := Χ) (Ξ := 1) τ Λ (X.declaration z))).trans
            (hd z).symm)) ?_
        exact congrArg (fun S => Eq_bd ((A' ⋈ S))
            (((A' ⋈ S)).boundaryOf
              (Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') F.fill Λ (τ z)))
            (Bd.act (Γ := Γ') (Δ := Χ) (Ξ := 1)
              (F.fill ⋆ τ) Λ
              ((dTel.actBase F.fill X).declaration z))) (hb z).symm

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
    (agree : ∀ ⦃Λ : C.Arity⦄ (z : α ∋ Λ),
        ¬ (args ⋆ (Ξ.binding x).declaration z).isEq →
        Ξ ⋈ args ⋆ (Ξ.binding x).binding z ⊢ args z ≈ args' z) :
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
      exact Eq_bd.congr args args hb fill fill fill.agree hdecl
  | _, Ξ, hΞ, _, _, .congr (Θ := Θ) σ θ hΘ hσ hθ agree h => by
      have hΞ' : Ambient.Wf (Ξ ⋈ Θ) := Wf_t.concatenate hΞ hΘ
      refine Eq_bd.trans (boundaryOf_instantiate hΞ' hσ (Eq_e.wf_left h)) ?_
      refine Eq_bd.trans ?_
        (boundaryOf_instantiate hΞ' hθ (Eq_e.wf_right h)).symm
      exact Eq_bd.congr σ θ hΘ hσ hθ agree (Eq_e.boundaryOf hΞ' h)
