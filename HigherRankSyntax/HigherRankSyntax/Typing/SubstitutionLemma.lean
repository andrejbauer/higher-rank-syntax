import HigherRankSyntax.Typing.Eta

/-!
# Substitution

The judgements are stable under fillings of ambients (`substitutionAt`), hence
under filling a block `Θ` of the ambient by a filling of `Θ`, and under
well-formed substitutions between ambients. Also here: the two sides of an
equality of expressions are well formed and, over a well-formed ambient, have
equal computed boundaries.
-/

/-! ## Fillings of ambients -/

/-- A filling of `A` by `A'` at `Ω`: a substitution `fill` such that at every slot
`x` of `A`, writing `β` for the declaration of `x` under `fill`, either `fill x` is
the η-expansion of a slot of `A'` with declaration `β` and with bound entries those
of `x` under `fill`, or `Ω` has a slot of the arity of `x` and, over `A'` extended
by the entries `x` binds under `fill`, the two sides of `β` are equal if `β` is an
equation, and otherwise `fill x` is well formed with computed boundary equal to
`β`. -/
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

/-- A filling `F` of `A` by `A'` at `Ω` extends to a filling of `A ⋈ T` by
`A' ⋈ F.fill ⋆ T` at `Ω`, with substitution `F.fill` lifted past `T`. -/
def Ambient.Filling.extend {Γ Γ' Ω Χ : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (F : Ambient.Filling A A' Ω) (T : dTel Γ Χ) :
    Ambient.Filling (A ⋈ T) (A' ⋈ F.fill ⋆ T) Ω where
  fill := Subst.lift F.fill Χ
  slot := by
    intro α x
    rcases C.cover Γ Χ x with ⟨w, rfl⟩ | ⟨i, rfl⟩
    · rcases F.slot w with ⟨y, hη, hdecl, hbind⟩ | ⟨hsub, heq, hwf, hbd⟩
      · left
        use C.inl y
        and_intros
        · rw [Subst.lift_inl, hη, Renaming.act_eta]
          rfl
        · rw [dTel.declaration_concatenate_inl, hdecl, dTel.declaration_concatenate_inl]
          symm
          apply Bd.act_square
          apply Subst.lift_inl
        · rw [dTel.binding_concatenate_inl, hbind, dTel.binding_concatenate_inl]
          symm
          apply dTel.actBase_square
          apply Subst.lift_inl
      · have hd : Bd.applyAt (Subst.lift F.fill Χ) α ((A ⋈ T).declaration (C.inl w))
            = Bd.rename (Renaming.inl Γ' Χ ⇑ʳ α) (Bd.applyAt F.fill α (A.declaration w)) := by
          rw [dTel.declaration_concatenate_inl]
          apply Bd.act_square
          apply Subst.lift_inl
        have hb : dTel.actBase (Subst.lift F.fill Χ) ((A ⋈ T).binding (C.inl w))
            = dTel.rename (Renaming.inl Γ' Χ) (F.fill ⋆ A.binding w) := by
          rw [dTel.binding_concatenate_inl]
          apply dTel.actBase_square
          apply Subst.lift_inl
        let ι := (Ambient.Renaming.weaken A' (F.fill ⋆ T)).extend (F.fill ⋆ A.binding w)
        right
        use hsub
        and_intros
        · intro l r hlr
          rw [hd] at hlr
          obtain ⟨l₀, r₀, hlr₀, rfl, rfl⟩ := Bd.rename_eq_inv _ hlr
          convert Eq_e.weaken ι (heq l₀ r₀ hlr₀) using 2
        · intro hne
          convert Wf_e.weaken ι (hwf ?_) using 2
          · apply Subst.lift_inl
          · rwa [hd, Bd.isEq_rename] at hne
        · intro hne
          convert Eq_bd.weaken ι (hbd ?_) using 2
          · convert ι.boundaryOf (F.fill w) using 3
            apply Subst.lift_inl
          · rwa [hd, Bd.isEq_rename] at hne
    · left
      use C.inr i
      and_intros
      · apply Subst.lift_inr
      · rw [dTel.declaration_concatenate_inr, dTel.declaration_actBase,
          dTel.declaration_concatenate_inr]
        rfl
      · rw [dTel.binding_concatenate_inr, dTel.binding_actBase, dTel.binding_concatenate_inr]
        rfl

/-- A filling `τ` of `T` over `A` gives a filling of `A ⋈ T` by `A` at `Ω`, with
substitution the identity on `A` paired with `τ` on `T`. -/
def Wf_s.filling {Γ Ω : C.Arity} {A : Ambient Γ} {T : dTel Γ Ω} {τ : Subst Ω Γ}
    (h : Wf_s A T τ) : Ambient.Filling (A ⋈ T) A Ω where
  fill := Subst.copair (Subst.id Γ) τ
  slot := by
    intro α x
    rcases C.cover Γ Ω x with ⟨w, rfl⟩ | ⟨z, rfl⟩
    · left
      use w
      and_intros
      · apply Subst.copair_inl
      · rw [dTel.declaration_concatenate_inl]
        symm
        apply Eq.trans (Bd.act_rename_cancel (Renaming.inl Γ Ω) (𝟙ʳ Γ) _ ?_ α (A.declaration w))
        · rw [Renaming.extend_id, Bd.rename_id]
        · intro _ u
          apply Subst.copair_inl
      · rw [dTel.binding_concatenate_inl]
        symm
        apply Eq.trans (dTel.actBase_rename_cancel (Renaming.inl Γ Ω) (𝟙ʳ Γ) _ ?_ (A.binding w))
        · apply dTel.rename_id
        · intro _ u
          apply Subst.copair_inl
    · have hd : Bd.applyAt (Subst.copair (Subst.id Γ) τ) α ((A ⋈ T).declaration (C.inr z))
          = τ ⋆ T.declaration z := by
        rw [dTel.declaration_concatenate_inr]
        apply Bd.act_copair_prefix
      have hb := dTel.binding_concatenate_inr A T z
      right
      use ⟨z⟩
      and_intros
      · intro l r hlr
        convert h.equation z l r ?_ using 3
        rwa [← hd]
      · intro hne
        convert h.filler z ?_ using 3
        · apply Subst.copair_inr
        · rwa [← hd]
      · intro hne
        convert h.declared z ?_ using 4
        · apply Subst.copair_inr
        · rwa [← hd]

/-! ## The substitution lemma -/

/-- The judgements are stable under every filling of ambients at `Ω`. -/
structure SubstitutionAt (Ω : C.Arity) : Prop where
  /-- Well-formed expressions go to well-formed expressions. -/
  expr : ∀ {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (F : Ambient.Filling A A' Ω) {g : Expr Γ},
      Wf_e A g → Wf_e A' (F.fill ⋆ g)
  /-- The computed boundary of a filled well-formed expression is equal to its
  filled computed boundary, provided the latter is equal to itself. -/
  boundary : ∀ {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (F : Ambient.Filling A A' Ω) {g : Expr Γ},
      Wf_e A g →
      Eq_bd A' (F.fill ⋆ A.boundaryOf g) (F.fill ⋆ A.boundaryOf g) →
      Eq_bd A' (A'.boundaryOf (F.fill ⋆ g)) (F.fill ⋆ A.boundaryOf g)
  /-- Equal boundaries go to equal boundaries. -/
  boundaryEquality : ∀ {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (F : Ambient.Filling A A' Ω) {β β' : Bd Γ}, Eq_bd A β β' →
      Eq_bd A' (F.fill ⋆ β) (F.fill ⋆ β')
  /-- Equal expressions go to equal expressions. -/
  equality : ∀ {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (F : Ambient.Filling A A' Ω) {l r : Expr Γ}, Eq_e A l r →
      Eq_e A' (F.fill ⋆ l) (F.fill ⋆ r)
  /-- A declaration well formed over `A` with bound entries `T` goes to a
  declaration well formed over `A'` with bound entries `F.fill ⋆ T`. -/
  declaration : ∀ {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (F : Ambient.Filling A A' Ω) {Λ : C.Arity} {T : dTel Γ Λ} {β : Bd (Γ ⋈ Λ)},
      Wf_bd A T β → Wf_bd A' (F.fill ⋆ T) (Bd.applyAt F.fill Λ β)
  /-- Well-formed telescopes go to well-formed telescopes. -/
  telescope : ∀ {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (F : Ambient.Filling A A' Ω) {Λ : C.Arity} {T : dTel Γ Λ},
      Wf_t A T → Wf_t A' (F.fill ⋆ T)
  /-- A filling of a telescope goes to a filling of the filled telescope. -/
  filling : ∀ {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (F : Ambient.Filling A A' Ω) {Χ : C.Arity} {X : dTel Γ Χ} {τ : Subst Χ Γ},
      Wf_s A X τ →
        Wf_s A' (F.fill ⋆ X) (F.fill ⋆ τ)

mutual

/-- Given `SubstitutionAt` at the arities of the slots of `Ω`, a filling of
ambients at `Ω` carries well-formed expressions to well-formed expressions. -/
theorem Wf_e.subst_step
    {Γ Γ' Ω : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ih : ∀ ⦃α : C.Arity⦄, Carrier.Sub α Ω → SubstitutionAt α)
    (F : Ambient.Filling A A' Ω) :
  ∀ {g : Expr Γ}, Wf_e A g → Wf_e A' (F.fill ⋆ g)
  | _, .ap (α := α) x args head fill => by
      rcases F.slot x with ⟨y, hη, hdecl, hbind⟩ | ⟨hsub, _, hwf, _⟩
      · convert Wf_e.ap y (F.fill ⋆ args) ?_ ?_ using 1
        · apply act_ap_eta F.fill x y hη args
        · rwa [hdecl, Bd.isEq_act]
        · rw [hbind]
          apply Wf_s.subst_step ih F fill
      · convert (ih hsub).expr (Wf_s.filling (Wf_s.subst_step ih F fill)) (hwf ?_) using 1
        · apply Eq.trans (act_ap F.fill x args)
          symm
          apply act_copair_prefix
        · rwa [← Bd.isEq_act (Γ := 1) F.fill α] at head

/-- Given `SubstitutionAt` at the arities of the slots of `Ω`, under a filling of
ambients at `Ω` the computed boundary of a filled well-formed expression is equal
to its filled computed boundary, provided the latter is equal to itself. -/
theorem boundaryOf_subst_step
    {Γ Γ' Ω : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ih : ∀ ⦃α : C.Arity⦄, Carrier.Sub α Ω → SubstitutionAt α)
    (F : Ambient.Filling A A' Ω) :
  ∀ {g : Expr Γ}, Wf_e A g →
    Eq_bd A' (F.fill ⋆ A.boundaryOf g) (F.fill ⋆ A.boundaryOf g) →
    Eq_bd A' (A'.boundaryOf (F.fill ⋆ g)) (F.fill ⋆ A.boundaryOf g)
  | _, .ap (α := α) x args head fill, refl => by
      rcases F.slot x with ⟨y, hη, hdecl, _⟩ | ⟨hsub, _, hwf, hbd⟩
      · convert refl using 2
        apply Eq.trans (congrArg A'.boundaryOf (act_ap_eta F.fill x y hη args))
        rw [dTel.boundaryOf_ap, hdecl]
        apply Eq.trans _ (Bd.act_lift_fillers (Χ := α) (Λ := 1) F.fill args (A.declaration x))
        rw [Bd.act_lift_depth]
        rfl
      · have hne : ¬ (Bd.applyAt F.fill α (A.declaration x)).isEq := by
          rwa [← Bd.isEq_act (Γ := 1) F.fill α] at head
        let G := Wf_s.filling (Wf_s.subst_step ih F fill)
        have hmove := (ih hsub).boundaryEquality G (hbd hne)
        have hfilled := (ih hsub).boundary G (hwf hne) (Eq_bd.trans hmove hmove.symm)
        convert Eq_bd.trans hfilled hmove using 1
        · congr 1
          apply Eq.trans (act_ap F.fill x args)
          symm
          apply act_copair_prefix
        · symm
          apply Eq.trans (Bd.act_copair_prefix (F.fill ⋆ args) 1 _)
          apply Eq.trans _ (Bd.act_lift_fillers (Χ := α) (Λ := 1) F.fill args (A.declaration x))
          rw [Bd.act_lift_depth]

/-- Given `SubstitutionAt` at the arities of the slots of `Ω`, a filling of
ambients at `Ω` carries equal expressions to equal expressions. -/
theorem Eq_e.subst_step
    {Γ Γ' Ω : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ih : ∀ ⦃α : C.Arity⦄, Carrier.Sub α Ω → SubstitutionAt α)
    (F : Ambient.Filling A A' Ω) :
  ∀ {l r : Expr Γ}, Eq_e A l r → Eq_e A' (F.fill ⋆ l) (F.fill ⋆ r)
  | _, _, .refl h => .refl (Wf_e.subst_step ih F h)
  | _, _, .symm h => .symm (Eq_e.subst_step ih F h)
  | _, _, .trans h h' => .trans (Eq_e.subst_step ih F h) (Eq_e.subst_step ih F h')
  | _, _, .hyp (Λ := Λ₀) q l r args decl hl hr fill => by
      have hmove : ∀ e : Expr (Γ ⋈ Λ₀),
          F.fill ⋆ (args ⋆ e) = (F.fill ⋆ args) ⋆ Subst.act (Γ := 1) F.fill Λ₀ e := by
        intro e
        symm
        rw [← Subst.act_lift_depth]
        apply Subst.act_lift_fillers
      have hslot := F.slot q
      rw [decl] at hslot
      rcases hslot with ⟨y, _, hdecl, hbind⟩ | ⟨hsub, heq, _, _⟩
      · convert Eq_e.hyp y _ _ (F.fill ⋆ args) hdecl ?_ ?_ ?_ using 1
        · apply hmove
        · apply hmove
        · rw [hbind]
          convert Wf_e.subst_step ih (F.extend (A.binding q)) hl using 1
          symm
          apply Subst.act_lift_depth
        · rw [hbind]
          convert Wf_e.subst_step ih (F.extend (A.binding q)) hr using 1
          symm
          apply Subst.act_lift_depth
        · rw [hbind]
          apply Wf_s.subst_step ih F fill
      · convert (ih hsub).equality (Wf_s.filling (Wf_s.subst_step ih F fill)) (heq _ _ rfl)
          using 1
        · rw [hmove]
          symm
          apply act_copair_prefix
        · rw [hmove]
          symm
          apply act_copair_prefix
  | _, _, .congr (Θ := Θ₀) s t hΘ₀ hs ht agree h => by
      convert Eq_e.congr (F.fill ⋆ s) (F.fill ⋆ t) (Wf_t.subst_step ih F hΘ₀)
        (Wf_s.subst_step ih F hs) (Wf_s.subst_step ih F ht) (Eq_s.subst_step ih F agree)
        (Eq_e.subst_step ih (F.extend Θ₀) h) using 1
      · symm
        apply Subst.act_lift_fillers
      · symm
        apply Subst.act_lift_fillers

/-- Given `SubstitutionAt` at the arities of the slots of `Ω`, a filling of
ambients at `Ω` carries substitutions agreeing as fillings of a telescope to
substitutions agreeing as fillings of the filled telescope. -/
theorem Eq_s.subst_step
    {Γ Γ' Ω : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ih : ∀ ⦃α : C.Arity⦄, Carrier.Sub α Ω → SubstitutionAt α)
    (F : Ambient.Filling A A' Ω) :
  ∀ {Χ : C.Arity} {X : dTel Γ Χ} {σ θ : Subst Χ Γ}, Eq_s A X σ θ →
    Eq_s A' (F.fill ⋆ X) (F.fill ⋆ σ) (F.fill ⋆ θ)
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons (α := α) (bind := bind) (boundary := boundary) slot hrest => by
      apply Eq_s.cons
      · intro hne
        convert Eq_e.subst_step ih (F.extend bind) (slot ?_) using 1
        · symm
          apply Subst.act_lift_depth
        · symm
          apply Subst.act_lift_depth
        · apply mt (Bd.isEq_act (Γ := 1) F.fill α boundary).mpr hne
      · convert Eq_s.subst_step ih F hrest using 2
        symm
        apply dTel.actBase_instantiate

/-- Given `SubstitutionAt` at the arities of the slots of `Ω`, a filling of
ambients at `Ω` carries equal boundaries to equal boundaries. -/
theorem Eq_bd.subst_step
    {Γ Γ' Ω : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ih : ∀ ⦃α : C.Arity⦄, Carrier.Sub α Ω → SubstitutionAt α)
    (F : Ambient.Filling A A' Ω) :
  ∀ {β β' : Bd Γ}, Eq_bd A β β' → Eq_bd A' (F.fill ⋆ β) (F.fill ⋆ β')
  | _, _, .sort => .sort
  | _, _, .of h => .of (Eq_e.subst_step ih F h)
  | _, _, .eq hl hr => .eq (Eq_e.subst_step ih F hl) (Eq_e.subst_step ih F hr)

/-- Given `SubstitutionAt` at the arities of the slots of `Ω`, a filling of
ambients at `Ω` carries a filling of a telescope to a filling of the filled
telescope. -/
theorem Wf_s.subst_step
    {Γ Γ' Ω : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ih : ∀ ⦃α : C.Arity⦄, Carrier.Sub α Ω → SubstitutionAt α)
    (F : Ambient.Filling A A' Ω) :
  ∀ {Χ : C.Arity} {X : dTel Γ Χ} {τ : Subst Χ Γ}, Wf_s A X τ →
    Wf_s A' (F.fill ⋆ X) (F.fill ⋆ τ)
  | _, _, _, .nil => .nil
  | _, _, _, .cons (α := α) (bind := bind) (boundary := boundary)
      equation filler declared hrest => by
      apply Wf_s.cons
      · intro l r h
        obtain ⟨l₀, r₀, hβ, rfl, rfl⟩ := Bd.act_eq_inv (Γ := 1) F.fill α h
        convert Eq_e.subst_step ih (F.extend bind) (equation l₀ r₀ hβ) using 1
        · symm
          apply Subst.act_lift_depth
        · symm
          apply Subst.act_lift_depth
      · intro hne
        convert Wf_e.subst_step ih (F.extend bind) (filler ?_) using 1
        · symm
          apply Subst.act_lift_depth
        · apply mt (Bd.isEq_act (Γ := 1) F.fill α boundary).mpr hne
      · intro hne
        have h₀ := mt (Bd.isEq_act (Γ := 1) F.fill α boundary).mpr hne
        have hmove := Eq_bd.subst_step ih (F.extend bind) (declared h₀)
        have hfilled := boundaryOf_subst_step ih (F.extend bind) (filler h₀)
          (Eq_bd.trans hmove hmove.symm)
        convert Eq_bd.trans hfilled hmove using 2
        · symm
          apply Subst.act_lift_depth
        · symm
          apply Bd.act_lift_depth
      · convert Wf_s.subst_step ih F hrest using 2
        symm
        apply dTel.actBase_instantiate

/-- Given `SubstitutionAt` at the arities of the slots of `Ω`, a filling `F` of
`A` by `A'` at `Ω` carries a declaration well formed over `A` with bound entries
`T` to a declaration well formed over `A'` with bound entries `F.fill ⋆ T`. -/
theorem Wf_bd.subst_step
    {Γ Γ' Ω : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ih : ∀ ⦃α : C.Arity⦄, Carrier.Sub α Ω → SubstitutionAt α)
    (F : Ambient.Filling A A' Ω) :
  ∀ {Λ : C.Arity} {T : dTel Γ Λ} {β : Bd (Γ ⋈ Λ)}, Wf_bd A T β →
    Wf_bd A' (F.fill ⋆ T) (Bd.applyAt F.fill Λ β)
  | _, _, _, .sort => .sort
  | _, T, _, .of hS hsort => by
      have hmove := Eq_bd.subst_step ih (F.extend T) hsort
      apply Wf_bd.of
      · convert Wf_e.subst_step ih (F.extend T) hS using 1
        symm
        apply Subst.act_lift_depth
      · have hfilled := boundaryOf_subst_step ih (F.extend T) hS (Eq_bd.trans hmove hmove.symm)
        convert Eq_bd.trans hfilled hmove using 3
        symm
        apply Subst.act_lift_depth
  | _, T, _, .eq hl hr heq => by
      have hmove := Eq_bd.subst_step ih (F.extend T) heq
      apply Wf_bd.eq
      · convert Wf_e.subst_step ih (F.extend T) hl using 1
        symm
        apply Subst.act_lift_depth
      · convert Wf_e.subst_step ih (F.extend T) hr using 1
        symm
        apply Subst.act_lift_depth
      · have hl' := boundaryOf_subst_step ih (F.extend T) hl (Eq_bd.trans hmove hmove.symm)
        have hr' := boundaryOf_subst_step ih (F.extend T) hr (Eq_bd.trans hmove.symm hmove)
        convert Eq_bd.trans (Eq_bd.trans hl' hmove) hr'.symm using 3
        · symm
          apply Subst.act_lift_depth
        · symm
          apply Subst.act_lift_depth

/-- Given `SubstitutionAt` at the arities of the slots of `Ω`, a filling of
ambients at `Ω` carries well-formed telescopes to well-formed telescopes. -/
theorem Wf_t.subst_step
    {Γ Γ' Ω : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ih : ∀ ⦃α : C.Arity⦄, Carrier.Sub α Ω → SubstitutionAt α)
    (F : Ambient.Filling A A' Ω) :
  ∀ {Λ : C.Arity} {T : dTel Γ Λ}, Wf_t A T → Wf_t A' (F.fill ⋆ T)
  | _, _, .nil => .nil
  | _, _, .cons (bind := bind) (boundary := boundary) hbind hboundary hrest =>
      .cons (Wf_t.subst_step ih F hbind) (Wf_bd.subst_step ih F hboundary)
        (Wf_t.subst_step ih (F.extend (dTel.cons bind boundary .nil)) hrest)

end

/-- `SubstitutionAt Ω` holds for every arity `Ω`. -/
theorem substitutionAt : ∀ Ω : C.Arity, SubstitutionAt Ω
  | Ω =>
      have ih : ∀ ⦃α : C.Arity⦄, Carrier.Sub α Ω → SubstitutionAt α :=
        fun _ _ => substitutionAt _
      { expr := Wf_e.subst_step ih
        boundary := boundaryOf_subst_step ih
        boundaryEquality := Eq_bd.subst_step ih
        equality := Eq_e.subst_step ih
        filling := Wf_s.subst_step ih
        declaration := Wf_bd.subst_step ih
        telescope := Wf_t.subst_step ih }
termination_by Ω => Ω
decreasing_by all_goals assumption

/-! ## Filling a block -/

section

variable {Δ Ω Φ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω} {σ : Subst Ω Δ}
  {Ψ : dTel (Δ ⋈ Ω) Φ}

/-- A filling `σ` of `Θ` over `Ξ` gives a filling of `Ξ ⋈ Θ ⋈ Ψ` by
`Ξ ⋈ σ ⋆ Ψ` at `Ω`. -/
def Wf_s.fillBefore (hσ : Wf_s Ξ Θ σ) (Ψ : dTel (Δ ⋈ Ω) Φ) :
    Ambient.Filling (Ξ ⋈ Θ ⋈ Ψ) (Ξ ⋈ σ ⋆ Ψ) Ω :=
  (Wf_s.filling hσ).extend Ψ

/-- Applying the substitution of `hσ.fillBefore Ψ` to an expression over
`Δ ⋈ Ω ⋈ Φ` fills its block `Ω` by `σ`. -/
theorem Wf_s.fillBefore_act
    (hσ : Wf_s Ξ Θ σ) (Ψ : dTel (Δ ⋈ Ω) Φ) (g : Expr ((Δ ⋈ Ω) ⋈ Φ)) :
  (hσ.fillBefore Ψ).fill ⋆ g = σ ⋆ g
  := by
  apply Eq.trans (Subst.act_lift_depth _ g)
  apply act_copair_prefix

/-- Applying the substitution of `hσ.fillBefore Ψ` to a boundary over
`Δ ⋈ Ω ⋈ Φ` fills its block `Ω` by `σ`. -/
theorem Wf_s.fillBefore_act_boundary
    (hσ : Wf_s Ξ Θ σ) (Ψ : dTel (Δ ⋈ Ω) Φ) (β : Bd ((Δ ⋈ Ω) ⋈ Φ)) :
  (hσ.fillBefore Ψ).fill ⋆ β = σ ⋆ β
  := by
  apply Eq.trans (Bd.act_lift_depth _ β)
  apply Bd.act_copair_prefix

/-- Filling the block `Θ` of the ambient `Ξ ⋈ Θ ⋈ Ψ` by a filling `σ` of `Θ`
preserves well-formedness of expressions. -/
theorem Wf_e.subst
    (hσ : Wf_s Ξ Θ σ) {g : Expr ((Δ ⋈ Ω) ⋈ Φ)} (h : Ξ ⋈ Θ ⋈ Ψ ⊢ g) :
  Ξ ⋈ σ ⋆ Ψ ⊢ σ ⋆ g
  := by
  rw [← hσ.fillBefore_act Ψ g]
  apply (substitutionAt Ω).expr (hσ.fillBefore Ψ) h

/-- Filling the block `Θ` of the ambient `Ξ ⋈ Θ ⋈ Ψ` by a filling `σ` of `Θ`
preserves equality of expressions. -/
theorem Eq_e.subst
    (hσ : Wf_s Ξ Θ σ) {l r : Expr ((Δ ⋈ Ω) ⋈ Φ)} (h : Ξ ⋈ Θ ⋈ Ψ ⊢ l ≈ r) :
  Ξ ⋈ σ ⋆ Ψ ⊢ σ ⋆ l ≈ σ ⋆ r
  := by
  rw [← hσ.fillBefore_act Ψ l, ← hσ.fillBefore_act Ψ r]
  apply (substitutionAt Ω).equality (hσ.fillBefore Ψ) h

/-- Filling the block `Θ` of the ambient `Ξ ⋈ Θ ⋈ Ψ` by a filling `σ` of `Θ`
preserves equality of boundaries. -/
theorem Eq_bd.subst
    (hσ : Wf_s Ξ Θ σ) {β β' : Bd ((Δ ⋈ Ω) ⋈ Φ)} (h : Ξ ⋈ Θ ⋈ Ψ ⊢ β ≈ β') :
  Ξ ⋈ σ ⋆ Ψ ⊢ σ ⋆ β ≈ σ ⋆ β'
  := by
  rw [← hσ.fillBefore_act_boundary Ψ β, ← hσ.fillBefore_act_boundary Ψ β']
  apply (substitutionAt Ω).boundaryEquality (hσ.fillBefore Ψ) h

/-- Filling the block `Θ` of the ambient `Ξ ⋈ Θ ⋈ Ψ` by a filling `σ` of `Θ`
preserves well-formedness of telescopes. -/
theorem Wf_t.subst
    (hσ : Wf_s Ξ Θ σ) {Λ : C.Arity} {T : dTel ((Δ ⋈ Ω) ⋈ Φ) Λ} (h : Wf_t (Ξ ⋈ Θ ⋈ Ψ) T) :
  Wf_t (Ξ ⋈ σ ⋆ Ψ) (σ ⋆ T)
  := (substitutionAt Ω).telescope (hσ.fillBefore Ψ) h

/-- Instantiating the block `Θ` of the ambient `Ξ ⋈ Θ` by a filling `σ` of `Θ`
preserves well-formedness of expressions. -/
theorem Wf_e.instantiate (hσ : Wf_s Ξ Θ σ) {g : Expr (Δ ⋈ Ω)} (h : Ξ ⋈ Θ ⊢ g) :
  Ξ ⊢ σ ⋆ g
  := by
  rw [← dTel.concatenate_nil Ξ]
  apply Wf_e.subst (Ψ := .nil) hσ
  convert h using 1
  apply dTel.concatenate_nil

/-- Instantiating the block `Θ` of the ambient `Ξ ⋈ Θ` by a filling `σ` of `Θ`
preserves equality of expressions. -/
theorem Eq_e.instantiate (hσ : Wf_s Ξ Θ σ) {l r : Expr (Δ ⋈ Ω)} (h : Ξ ⋈ Θ ⊢ l ≈ r) :
  Ξ ⊢ σ ⋆ l ≈ σ ⋆ r
  := by
  rw [← dTel.concatenate_nil Ξ]
  apply Eq_e.subst (Ψ := .nil) hσ
  convert h using 1
  apply dTel.concatenate_nil

/-- Instantiating the block `Θ` of the ambient `Ξ ⋈ Θ` by a filling `σ` of `Θ`
preserves equality of boundaries. -/
theorem Eq_bd.instantiate (hσ : Wf_s Ξ Θ σ) {β β' : Bd (Δ ⋈ Ω)} (h : Ξ ⋈ Θ ⊢ β ≈ β') :
  Ξ ⊢ σ ⋆ β ≈ σ ⋆ β'
  := by
  rw [← dTel.concatenate_nil Ξ]
  apply Eq_bd.subst (Ψ := .nil) hσ
  convert h using 1
  apply dTel.concatenate_nil

/-- Instantiating the block `Θ` of the ambient `Ξ ⋈ Θ` by a filling `σ` of `Θ`
preserves well-formedness of telescopes. -/
theorem Wf_t.instantiate (hσ : Wf_s Ξ Θ σ) {Λ : C.Arity} {T : dTel (Δ ⋈ Ω) Λ}
    (h : Wf_t (Ξ ⋈ Θ) T) :
  Wf_t Ξ (σ ⋆ T)
  := by
  rw [← dTel.concatenate_nil Ξ]
  convert Wf_t.subst (Ψ := .nil) (T := T) hσ ?_ using 2
  · rw [dTel.fill, Subst.lift_one]
    rfl
  · convert h using 1
    apply dTel.concatenate_nil

/-- The computed boundary of a well-formed expression over a well-formed ambient
is equal to itself. -/
theorem boundaryOf_refl {Δ : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ) :
  ∀ {e : Expr Δ}, Ξ ⊢ e → Ξ ⊢ Ξ.boundaryOf e ≈ Ξ.boundaryOf e
  | _, .ap x _ _ fill => Eq_bd.instantiate fill (Wf_bd.refl (Wf_t.declaration hΞ x))

/-- Over a well-formed ambient `Ξ ⋈ Θ ⋈ Ψ`, filling the block `Θ` by a filling
`σ` of `Θ` in a well-formed expression gives an expression whose computed boundary
is equal to the filled computed boundary of the original. -/
theorem boundaryOf_subst
    (hΞ : Ambient.Wf (Ξ ⋈ Θ ⋈ Ψ)) (hσ : Wf_s Ξ Θ σ)
    {g : Expr ((Δ ⋈ Ω) ⋈ Φ)} (h : Ξ ⋈ Θ ⋈ Ψ ⊢ g) :
  Ξ ⋈ σ ⋆ Ψ ⊢ (Ξ ⋈ σ ⋆ Ψ).boundaryOf (σ ⋆ g) ≈ σ ⋆ (Ξ ⋈ Θ ⋈ Ψ).boundaryOf g
  := by
  rw [← hσ.fillBefore_act Ψ g, ← hσ.fillBefore_act_boundary Ψ ((Ξ ⋈ Θ ⋈ Ψ).boundaryOf g)]
  apply (substitutionAt Ω).boundary (hσ.fillBefore Ψ) h
  rw [hσ.fillBefore_act_boundary Ψ]
  apply Eq_bd.subst hσ (boundaryOf_refl hΞ h)

/-- Over a well-formed ambient `Ξ ⋈ Θ`, instantiating the block `Θ` by a filling
`σ` of `Θ` in a well-formed expression gives an expression whose computed boundary
is equal to the instantiated computed boundary of the original. -/
theorem boundaryOf_instantiate
    (hΞ : Ambient.Wf (Ξ ⋈ Θ)) (hσ : Wf_s Ξ Θ σ) {g : Expr (Δ ⋈ Ω)} (h : Ξ ⋈ Θ ⊢ g) :
  Ξ ⊢ Ξ.boundaryOf (σ ⋆ g) ≈ σ ⋆ (Ξ ⋈ Θ).boundaryOf g
  := by
  convert boundaryOf_subst (Ψ := .nil) (g := g) ?_ hσ ?_ using 2
  · symm
    apply dTel.concatenate_nil
  · symm
    apply dTel.concatenate_nil
  · congr 2
    symm
    apply dTel.concatenate_nil
  · convert hΞ using 1
    apply dTel.concatenate_nil
  · convert h using 1
    apply dTel.concatenate_nil

end

/-! ## Presuppositions -/

mutual

/-- The left side of an equality of expressions is well formed. -/
theorem Eq_e.wf_left {Δ : C.Arity} {Ξ : Ambient Δ} :
  ∀ {e e' : Expr Δ}, Ξ ⊢ e ≈ e' → Ξ ⊢ e
  | _, _, .refl h => h
  | _, _, .symm h => Eq_e.wf_right h
  | _, _, .trans h _ => Eq_e.wf_left h
  | _, _, .hyp _ _ _ _ _ hl _ fill => Wf_e.instantiate fill hl
  | _, _, .congr _ _ _ hσ _ _ h => Wf_e.instantiate hσ (Eq_e.wf_left h)

/-- The right side of an equality of expressions is well formed. -/
theorem Eq_e.wf_right {Δ : C.Arity} {Ξ : Ambient Δ} :
  ∀ {e e' : Expr Δ}, Ξ ⊢ e ≈ e' → Ξ ⊢ e'
  | _, _, .refl h => h
  | _, _, .symm h => Eq_e.wf_left h
  | _, _, .trans _ h' => Eq_e.wf_right h'
  | _, _, .hyp _ _ _ _ _ _ hr fill => Wf_e.instantiate fill hr
  | _, _, .congr _ _ _ _ hθ _ h => Wf_e.instantiate hθ (Eq_e.wf_right h)

end

/-- Over a well-formed ambient, equal expressions have equal computed
boundaries. -/
theorem Eq_e.boundaryOf :
  ∀ {Δ : C.Arity} {Ξ : Ambient Δ}, Ambient.Wf Ξ →
    ∀ {e e' : Expr Δ}, Ξ ⊢ e ≈ e' → Ξ ⊢ Ξ.boundaryOf e ≈ Ξ.boundaryOf e'
  | _, _, hΞ, _, _, .refl h => boundaryOf_refl hΞ h
  | _, _, hΞ, _, _, .symm h => Eq_bd.symm (Eq_e.boundaryOf hΞ h)
  | _, _, hΞ, _, _, .trans h h' => Eq_bd.trans (Eq_e.boundaryOf hΞ h) (Eq_e.boundaryOf hΞ h')
  | _, _, hΞ, _, _, .hyp q _ _ args decl hl hr fill => by
      have hbind := Wf_t.binding hΞ q
      have hΞ' := Wf_t.concatenate hΞ hbind
      have hdecl := Wf_t.declaration hΞ q
      rw [decl] at hdecl
      apply Eq_bd.trans (boundaryOf_instantiate hΞ' fill hl)
      apply Eq_bd.trans _ (Eq_bd.symm (boundaryOf_instantiate hΞ' fill hr))
      apply Eq_bd.congr args args hbind fill fill fill.refl hdecl.eq_boundary
  | _, _, hΞ, _, _, .congr σ θ hΘ hσ hθ agree h => by
      have hΞ' := Wf_t.concatenate hΞ hΘ
      apply Eq_bd.trans (boundaryOf_instantiate hΞ' hσ (Eq_e.wf_left h))
      apply Eq_bd.trans _ (Eq_bd.symm (boundaryOf_instantiate hΞ' hθ (Eq_e.wf_right h)))
      apply Eq_bd.congr σ θ hΘ hσ hθ agree (Eq_e.boundaryOf hΞ' h)

/-! ## Telescope equality -/

/-- A filling of `A` by `A'` carries telescopes equal over `A` to telescopes equal
over `A'`. -/
theorem Eq_t.filling
    {Γ Γ' Ω : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'} (F : Ambient.Filling A A' Ω) :
  ∀ {Λ : C.Arity} {T T' : dTel Γ Λ}, Eq_t A T T' → Eq_t A' (F.fill ⋆ T) (F.fill ⋆ T')
  | _, .nil, _, h => by
      obtain rfl := Eq_t.nil_inv h
      apply Eq_t.nil
  | _, .cons bind boundary _, _, h => by
      obtain ⟨_, boundary', _, rfl, hbind, hboundary, hrest⟩ := Eq_t.cons_inv h
      apply Eq_t.cons (Eq_t.filling F hbind)
      · convert (substitutionAt Ω).boundaryEquality (F.extend bind) hboundary using 1
        · symm
          apply Bd.act_lift_depth
        · symm
          apply Bd.act_lift_depth
      · apply Eq_t.filling (F.extend (dTel.cons bind boundary .nil)) hrest

/-- Fillings `F` of `A` by `A'` and `F₁` of `A₁` by `A₁'` with the same
substitution carry telescopes equal over `A` and `A₁` to telescopes equal over
`A'` and `A₁'`. -/
theorem Eq_t.Both.filling
    {Γ Γ' Ω : C.Arity} {A A₁ : Ambient Γ} {A' A₁' : Ambient Γ'}
    (F : Ambient.Filling A A' Ω) (F₁ : Ambient.Filling A₁ A₁' Ω) (hfill : F₁.fill = F.fill) :
  ∀ {Λ : C.Arity} {T T' : dTel Γ Λ}, Eq_t.Both A A₁ T T' →
    Eq_t.Both A' A₁' (F.fill ⋆ T) (F.fill ⋆ T')
  | _, .nil, _, h => by
      obtain rfl := Eq_t.Both.nil_inv h
      apply Eq_t.Both.nil
  | _, .cons (α := α) bind boundary _, _, h => by
      obtain ⟨bind', boundary', _, rfl, hbind, hboundary, hboundary', hrest⟩ :=
        Eq_t.Both.cons_inv h
      apply Eq_t.Both.cons (Eq_t.Both.filling F F₁ hfill hbind)
      · convert (substitutionAt Ω).boundaryEquality (F.extend bind) hboundary using 1
        · symm
          apply Bd.act_lift_depth
        · symm
          apply Bd.act_lift_depth
      · rw [← hfill]
        convert (substitutionAt Ω).boundaryEquality (F₁.extend bind') hboundary' using 1
        · symm
          apply Bd.act_lift_depth
        · symm
          apply Bd.act_lift_depth
      · convert Eq_t.Both.filling (F.extend (dTel.cons bind boundary .nil))
          (F₁.extend (dTel.cons bind' boundary' .nil))
          (congrArg (Subst.lift · (C.single α)) hfill) hrest using 2
        rw [hfill]
        rfl

/-! ## Substitutions between ambients -/

/-- A substitution `σ` from `A` to `A'` is well formed when at every slot `x` of
`A`, writing `β` for the declaration of `x` under `σ`, over `A'` extended by the
entries `x` binds under `σ` the two sides of `β` are equal if `β` is an equation,
and otherwise `σ x` is well formed with computed boundary equal to `β`. -/
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

/-- Substitutions `σ` and `θ` from `A` to `A'` agree when at every slot `x` of `A`
whose declaration under `σ` is not an equation, `σ x` and `θ x` are equal over
`A'` extended by the entries `x` binds under `σ`. -/
def Eq_sub {Γ Γ' : C.Arity} (A : Ambient Γ) (A' : Ambient Γ') (σ θ : Subst Γ Γ') :
    Prop :=
  ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α), ¬ (Bd.applyAt σ α (A.declaration x)).isEq →
    Eq_e (A' ⋈ σ ⋆ A.binding x) (σ x) (θ x)

/-- The declaration of `x` in `A` reindexed over `Γ'` is the declaration of `x` in
`A` renamed along `Renaming.inr Γ' Γ ⇑ʳ α`. -/
theorem Ambient.weaken_declaration {Γ Γ' α : C.Arity} (A : Ambient Γ) (x : Γ ∋ α) :
  (dTel.rename (Renaming.fromUnit Γ') A).declaration x
    = Bd.rename (Renaming.inr Γ' Γ ⇑ʳ α) (A.declaration x)
  := by
  rw [dTel.declaration_rename, Renaming.fromUnit_extend]
  rfl

/-- The entries `x` binds in `A` reindexed over `Γ'` are the entries `x` binds in
`A` renamed along `Renaming.inr Γ' Γ`. -/
theorem Ambient.weaken_binding {Γ Γ' α : C.Arity} (A : Ambient Γ) (x : Γ ∋ α) :
  (dTel.rename (Renaming.fromUnit Γ') A).binding x
    = dTel.rename (Renaming.inr Γ' Γ) (A.binding x)
  := by
  rw [dTel.binding_rename, Renaming.fromUnit_extend]
  rfl

/-- Filling by `σ` the declaration of `x` in `A` reindexed over `Γ'` gives the
declaration of `x` in `A` under `σ`. -/
theorem Wf_sub.declaration_weaken
    {Γ Γ' : C.Arity} {A : Ambient Γ}
    (σ : Subst Γ Γ') ⦃α : C.Arity⦄ (x : Γ ∋ α) :
  Bd.fill σ ((dTel.rename (Renaming.fromUnit Γ') A).declaration x)
    = Bd.applyAt σ α (A.declaration x)
  := by
  rw [Ambient.weaken_declaration]
  apply Bd.act_weaken

/-- Instantiating by `σ` the entries `x` binds in `A` reindexed over `Γ'` gives
the entries `x` binds in `A` under `σ`. -/
theorem Wf_sub.binding_weaken
    {Γ Γ' : C.Arity} {A : Ambient Γ}
    (σ : Subst Γ Γ') ⦃α : C.Arity⦄ (x : Γ ∋ α) :
  dTel.instantiate σ ((dTel.rename (Renaming.fromUnit Γ') A).binding x)
    = dTel.actBase σ (A.binding x)
  := by
  rw [Ambient.weaken_binding]
  apply dTel.instantiate_weaken

/-- A well-formed substitution `σ` from `A` to `A'` fills, over `A'`, the ambient
`A` reindexed over `Γ'`. -/
theorem Wf_sub.toFilling
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'} {σ : Subst Γ Γ'}
    (hσ : Wf_sub A A' σ) :
  Wf_s A' (dTel.rename (Renaming.fromUnit Γ') A) σ
  := by
  apply Wf_s.slotwise
  · intro Λ z l r hlr
    rw [Wf_sub.declaration_weaken] at hlr
    convert (hσ z).1 l r hlr using 2
    apply Wf_sub.binding_weaken
  · intro Λ z hne
    rw [Wf_sub.declaration_weaken] at hne
    convert (hσ z).2.1 hne using 2
    apply Wf_sub.binding_weaken
  · intro Λ z hne
    rw [Wf_sub.declaration_weaken] at hne
    convert (hσ z).2.2 hne using 3
    · apply Wf_sub.binding_weaken
    · apply Wf_sub.binding_weaken
    · apply Wf_sub.declaration_weaken

/-- Agreeing substitutions `σ` and `θ` from `A` to `A'` agree, over `A'`, as
fillings of the ambient `A` reindexed over `Γ'`. -/
theorem Eq_sub.toAgreement
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'} {σ θ : Subst Γ Γ'}
    (hst : Eq_sub A A' σ θ) :
  Eq_s A' (dTel.rename (Renaming.fromUnit Γ') A) σ θ
  := by
  apply Eq_s.slotwise
  intro Λ z hne
  rw [Wf_sub.declaration_weaken] at hne
  convert hst z hne using 2
  apply Wf_sub.binding_weaken

/-- Applying `σ : Subst Δ Ω` to the ambient `A` reindexed over `Δ` gives `A`
reindexed over `Ω`. -/
theorem Ambient.actBase_weaken {Γ Δ Ω : C.Arity} (A : Ambient Γ) (σ : Subst Δ Ω) :
  dTel.actBase σ (dTel.rename (Renaming.fromUnit Δ) A) = dTel.rename (Renaming.fromUnit Ω) A
  := by
  rw [dTel.actBase_square (Renaming.fromUnit Δ) (Renaming.fromUnit Ω) σ (Subst.id 1),
    dTel.actBase_id]
  intro _ x
  exact (C.unit_is_empty x).elim

/-- A filling `σ`, over `A'`, of the ambient `A` reindexed over `Γ'` is a
well-formed substitution from `A` to `A'`. -/
theorem Wf_s.toWf_sub
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'} {σ : Subst Γ Γ'}
    (hσ : Wf_s A' (dTel.rename (Renaming.fromUnit Γ') A) σ) :
  Wf_sub A A' σ
  := by
  intro α x
  and_intros
  · intro l r hlr
    convert hσ.equation x l r ?_ using 2
    · symm
      apply Wf_sub.binding_weaken
    · rwa [Wf_sub.declaration_weaken]
  · intro hne
    convert hσ.filler x ?_ using 2
    · symm
      apply Wf_sub.binding_weaken
    · rwa [Wf_sub.declaration_weaken]
  · intro hne
    convert hσ.declared x ?_ using 3
    · symm
      apply Wf_sub.binding_weaken
    · symm
      apply Wf_sub.binding_weaken
    · symm
      apply Wf_sub.declaration_weaken
    · rwa [Wf_sub.declaration_weaken]

/-- Substitutions `σ` and `θ` agreeing, over `A'`, as fillings of the ambient `A`
reindexed over `Γ'` are agreeing substitutions from `A` to `A'`. -/
theorem Eq_s.toEq_sub
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'} {σ θ : Subst Γ Γ'}
    (hst : Eq_s A' (dTel.rename (Renaming.fromUnit Γ') A) σ θ) :
  Eq_sub A A' σ θ
  := by
  intro α x hne
  convert hst.slot x ?_ using 2
  · symm
    apply Wf_sub.binding_weaken
  · rwa [Wf_sub.declaration_weaken]

/-- The identity is a well-formed substitution from a well-formed ambient to
itself. -/
theorem Wf_sub.id {Δ : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ) :
  Wf_sub Ξ Ξ (Subst.id Δ)
  := by
  intro α x
  have hd : Bd.applyAt (Subst.id Δ) α (Ξ.declaration x) = Ξ.declaration x :=
    Bd.act_id Δ α _
  have hb : dTel.actBase (Subst.id Δ) (Ξ.binding x) = Ξ.binding x := dTel.actBase_id _
  rw [hd]
  and_intros
  · intro l r hlr
    have hbd := Wf_t.declaration hΞ x
    rw [hlr] at hbd
    let ι := (Ambient.Renaming.weaken Ξ (Ξ.binding x)).extend (Ξ.binding x)
    convert Eq_e.hyp (Ξ := Ξ ⋈ Ξ.binding x) (C.inl x) (⟦ ι.slot ⟧ʳ l) (⟦ ι.slot ⟧ʳ r)
      (Subst.instId Δ α) ?_ ?_ ?_ ?_ using 2
    · rw [← Renaming.extend_unit ι.slot]
      symm
      apply act_instId_weaken
    · rw [← Renaming.extend_unit ι.slot]
      symm
      apply act_instId_weaken
    · rw [dTel.declaration_concatenate_inl, hlr]
      rfl
    · convert Wf_e.weaken ι hbd.eq_left using 2
      apply dTel.binding_concatenate_inl
    · convert Wf_e.weaken ι hbd.eq_right using 2
      apply dTel.binding_concatenate_inl
    · convert Wf_s.eta Ξ (Ξ.binding x) (Wf_t.binding hΞ x) using 2
      apply dTel.binding_concatenate_inl
  · intro hne
    convert Wf_e.eta Ξ x (Wf_t.binding hΞ x) hne using 2
  · intro _
    convert Wf_bd.refl (Wf_t.declaration hΞ x) using 2
    convert dTel.boundaryOf_eta Ξ x using 3

/-- Over a well-formed ambient `Ξ`, a filling `σ` of `Θ` gives a well-formed
substitution from `Ξ ⋈ Θ` to `Ξ`: the identity on `Ξ` paired with `σ` on `Θ`. -/
theorem Wf_s.toSub
    {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω} {σ : Subst Ω Δ}
    (hΞ : Ambient.Wf Ξ) (h : Wf_s Ξ Θ σ) :
  Wf_sub (Ξ ⋈ Θ) Ξ (Subst.copair (Subst.id Δ) σ)
  := by
  intro α x
  rcases (Wf_s.filling h).slot x with ⟨y, hη, hdecl, hbind⟩ | ⟨_, heq, hwf, hbd⟩
  · obtain ⟨heq, hwf, hbd⟩ := Wf_sub.id hΞ y
    have hd : Bd.applyAt (Subst.id Δ) α (Ξ.declaration y) = Ξ.declaration y :=
      Bd.act_id Δ α _
    have hb : (Wf_s.filling h).fill ⋆ (Ξ ⋈ Θ).binding x
        = dTel.actBase (Subst.id Δ) (Ξ.binding y) := by
      rw [dTel.actBase_id, hbind]
    rw [hd, hdecl] at heq hwf hbd
    and_intros
    · intro l r hlr
      convert heq l r hlr using 2
    · intro hne
      convert hwf hne using 2
    · intro hne
      convert hbd hne using 2
      apply congrArg (Ξ ⋈ ·) hb
  · exact ⟨heq, hwf, hbd⟩

/-- Over a well-formed ambient `Ξ`, substitutions `σ` and `θ` agreeing as fillings
of `Θ` give agreeing substitutions from `Ξ ⋈ Θ` to `Ξ`: the identity on `Ξ`
paired with `σ`, respectively `θ`, on `Θ`. -/
theorem Eq_s.toSub
    {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω} {σ θ : Subst Ω Δ}
    (hΞ : Ambient.Wf Ξ) (h : Eq_s Ξ Θ σ θ) :
  Eq_sub (Ξ ⋈ Θ) Ξ (Subst.copair (Subst.id Δ) σ) (Subst.copair (Subst.id Δ) θ)
  := by
  intro α x hne
  rcases C.cover Δ Ω x with ⟨w, rfl⟩ | ⟨z, rfl⟩
  · have hd : Bd.applyAt (Subst.copair (Subst.id Δ) σ) α ((Ξ ⋈ Θ).declaration (C.inl w))
        = Ξ.declaration w := by
      rw [dTel.declaration_concatenate_inl]
      apply Eq.trans (Bd.act_rename_cancel (Renaming.inl Δ Ω) (𝟙ʳ Δ) _ ?_ α (Ξ.declaration w))
      · rw [Renaming.extend_id, Bd.rename_id]
      · intro _ u
        apply Subst.copair_inl
    have hb : dTel.actBase (Subst.copair (Subst.id Δ) σ) ((Ξ ⋈ Θ).binding (C.inl w))
        = Ξ.binding w := by
      rw [dTel.binding_concatenate_inl]
      apply Eq.trans (dTel.actBase_rename_cancel (Renaming.inl Δ Ω) (𝟙ʳ Δ) _ ?_ (Ξ.binding w))
      · apply dTel.rename_id
      · intro _ u
        apply Subst.copair_inl
    rw [hd] at hne
    rw [Subst.copair_inl, Subst.copair_inl]
    convert Eq_e.refl (Wf_e.eta Ξ w (Wf_t.binding hΞ w) hne) using 2
  · have hd : Bd.applyAt (Subst.copair (Subst.id Δ) σ) α ((Ξ ⋈ Θ).declaration (C.inr z))
        = σ ⋆ Θ.declaration z := by
      rw [dTel.declaration_concatenate_inr]
      apply Bd.act_copair_prefix
    have hb := dTel.binding_concatenate_inr Ξ Θ z
    rw [hd] at hne
    rw [Subst.copair_inr, Subst.copair_inr]
    convert h.slot z hne using 3

/-- Agreeing well-formed substitutions from a well-formed ambient `A` to `A'`
send a well-formed expression over `A` to equal expressions over `A'`. -/
theorem Eq_e.agree
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'} {σ θ : Subst Γ Γ'}
    (hA : Ambient.Wf A) (hσ : Wf_sub A A' σ) (hθ : Wf_sub A A' θ) (hst : Eq_sub A A' σ θ)
    {e : Expr Γ} (h : A ⊢ e) :
  A' ⊢ σ ⋆ e ≈ θ ⋆ e
  := by
  convert Eq_e.congr σ θ (Ambient.Wf.weaken hA A') hσ.toFilling hθ.toFilling hst.toAgreement
    (Eq_e.refl (Wf_e.weaken (Ambient.Renaming.weakenInto A A') h)) using 1
  · rw [← Renaming.extend_unit (Ambient.Renaming.weakenInto A A').slot]
    symm
    apply Subst.act_weaken
  · rw [← Renaming.extend_unit (Ambient.Renaming.weakenInto A A').slot]
    symm
    apply Subst.act_weaken

/-- A well-formed substitution from `A` to `A'` carries well-formed telescopes over
`A` to well-formed telescopes over `A'`. -/
theorem Wf_t.subst_ambient
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'} {σ : Subst Γ Γ'}
    (hσ : Wf_sub A A' σ) {Χ : C.Arity} {T : dTel Γ Χ} (hT : Wf_t A T) :
  Wf_t A' (σ ⋆ T)
  := by
  rw [← dTel.instantiate_weaken]
  apply (substitutionAt Γ).telescope (Wf_s.filling hσ.toFilling)
    (Wf_t.weaken (Ambient.Renaming.weakenInto A A') hT)

/-- A well-formed substitution from `A` to `A'` carries equal telescopes over `A`
to equal telescopes over `A'`. -/
theorem Eq_t.subst_ambient
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'} {σ : Subst Γ Γ'}
    (hσ : Wf_sub A A' σ) {Χ : C.Arity} {T T' : dTel Γ Χ} (h : Eq_t A T T') :
  Eq_t A' (σ ⋆ T) (σ ⋆ T')
  := by
  rw [← dTel.instantiate_weaken σ T, ← dTel.instantiate_weaken σ T']
  apply Eq_t.filling (Wf_s.filling hσ.toFilling)
    (Eq_t.weaken (Ambient.Renaming.weakenInto A A') h)

/-- A well-formed substitution `σ` from `A` to `A'` carries a filling `τ` of a
telescope `X` over `A` to the filling `σ ⋆ τ` of `σ ⋆ X` over `A'`. -/
theorem Wf_s.subst_ambient
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'} {σ : Subst Γ Γ'}
    (hσ : Wf_sub A A' σ) {Χ : C.Arity} {X : dTel Γ Χ} {τ : Subst Χ Γ} (h : Wf_s A X τ) :
  Wf_s A' (σ ⋆ X) (σ ⋆ τ)
  := by
  convert (substitutionAt Γ).filling (Wf_s.filling hσ.toFilling)
    (Wf_s.weaken (Ambient.Renaming.weakenInto A A') h) using 1
  · symm
    apply dTel.instantiate_weaken
  · funext Λ i
    symm
    apply act_copair_inr

/-- If `τ` is a well-formed substitution from `A` to `B` and `σ` one from `B` to
`D`, then `Subst.comp τ σ`, sending `x` to `σ` applied to `τ x`, is a well-formed
substitution from `A` to `D`. -/
theorem Wf_sub.comp
    {Γ Δ Ω : C.Arity} {A : Ambient Γ} {B : Ambient Δ} {D : Ambient Ω}
    {τ : Subst Γ Δ} {σ : Subst Δ Ω} (hτ : Wf_sub A B τ) (hσ : Wf_sub B D σ) :
  Wf_sub A D (Subst.comp (Γ := 1) τ σ)
  := by
  apply Wf_s.toWf_sub
  rw [← Ambient.actBase_weaken A σ]
  apply Wf_s.subst_ambient hσ hτ.toFilling

/-- A well-formed substitution `σ` from `A` to `A'` carries substitutions agreeing
as fillings of a telescope `X` over `A` to substitutions agreeing as fillings of
`σ ⋆ X` over `A'`. -/
theorem Eq_s.subst_ambient
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'} {σ : Subst Γ Γ'}
    (hσ : Wf_sub A A' σ) {Χ : C.Arity} {X : dTel Γ Χ} {τ θ : Subst Χ Γ}
    (h : Eq_s A X τ θ) :
  Eq_s A' (σ ⋆ X) (σ ⋆ τ) (σ ⋆ θ)
  := by
  convert Eq_s.subst_step (fun ⦃_⦄ _ => substitutionAt _) (Wf_s.filling hσ.toFilling)
    (Eq_s.weaken (Ambient.Renaming.weakenInto A A') h) using 1
  · symm
    apply dTel.instantiate_weaken
  · funext Λ i
    symm
    apply act_copair_inr
  · funext Λ i
    symm
    apply act_copair_inr

/-- A well-formed substitution `σ` from `A` to `A'` lifts past a well-formed
telescope `T` over `A` to a well-formed substitution from `A ⋈ T` to
`A' ⋈ σ ⋆ T`. -/
theorem Wf_sub.lift
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'} {σ : Subst Γ Γ'}
    (hσ : Wf_sub A A' σ) {Χ : C.Arity} {T : dTel Γ Χ} (hT : Wf_t A T) :
  Wf_sub (A ⋈ T) (A' ⋈ σ ⋆ T) (Subst.lift σ Χ)
  := by
  intro α x
  rcases C.cover Γ Χ x with ⟨w, rfl⟩ | ⟨i, rfl⟩
  · have hd : Bd.applyAt (Subst.lift σ Χ) α ((A ⋈ T).declaration (C.inl w))
        = Bd.rename (Renaming.inl Γ' Χ ⇑ʳ α) (Bd.applyAt σ α (A.declaration w)) := by
      rw [dTel.declaration_concatenate_inl]
      apply Bd.act_square
      apply Subst.lift_inl
    have hb : dTel.actBase (Subst.lift σ Χ) ((A ⋈ T).binding (C.inl w))
        = dTel.rename (Renaming.inl Γ' Χ) (σ ⋆ A.binding w) := by
      rw [dTel.binding_concatenate_inl]
      apply dTel.actBase_square
      apply Subst.lift_inl
    let ι := (Ambient.Renaming.weaken A' (σ ⋆ T)).extend (σ ⋆ A.binding w)
    obtain ⟨heq, hwf, hbd⟩ := hσ w
    and_intros
    · intro l r hlr
      rw [hd] at hlr
      obtain ⟨l₀, r₀, hlr₀, rfl, rfl⟩ := Bd.rename_eq_inv _ hlr
      convert Eq_e.weaken ι (heq l₀ r₀ hlr₀) using 2
    · intro hne
      convert Wf_e.weaken ι (hwf ?_) using 2
      · apply Subst.lift_inl
      · rwa [hd, Bd.isEq_rename] at hne
    · intro hne
      convert Eq_bd.weaken ι (hbd ?_) using 2
      · convert ι.boundaryOf (σ w) using 3
        apply Subst.lift_inl
      · rwa [hd, Bd.isEq_rename] at hne
  · have hη := Wf_s.eta A' (σ ⋆ T) (Wf_t.subst_ambient hσ hT)
    have hd : Bd.applyAt (Subst.lift σ Χ) α ((A ⋈ T).declaration (C.inr i))
        = Subst.instId Γ' Χ ⋆ (dTel.rename (Renaming.inl Γ' Χ) (σ ⋆ T)).declaration i := by
      symm
      apply Eq.trans (dTel.act_declaration_instId (σ ⋆ T) i)
      rw [dTel.declaration_actBase, dTel.declaration_concatenate_inr]
      rfl
    have hb : dTel.actBase (Subst.lift σ Χ) ((A ⋈ T).binding (C.inr i))
        = Subst.instId Γ' Χ ⋆ (dTel.rename (Renaming.inl Γ' Χ) (σ ⋆ T)).binding i := by
      symm
      apply Eq.trans (dTel.instantiate_binding_instId (σ ⋆ T) i)
      rw [dTel.binding_actBase, dTel.binding_concatenate_inr]
      rfl
    rw [hd]
    and_intros
    · intro l r hlr
      convert hη.equation i l r hlr using 2
    · intro hne
      convert hη.filler i hne using 2
      apply Subst.lift_inr
    · intro hne
      convert hη.declared i hne using 3
      apply Subst.lift_inr

/-- Agreeing substitutions `σ` and `θ` from `A` to `A'`, with `σ` well formed,
lift past a well-formed telescope `T` over `A` to agreeing substitutions from
`A ⋈ T` to `A' ⋈ σ ⋆ T`. -/
theorem Eq_sub.lift
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'} {σ θ : Subst Γ Γ'}
    (hσ : Wf_sub A A' σ) {Χ : C.Arity} {T : dTel Γ Χ} (hT : Wf_t A T)
    (hst : Eq_sub A A' σ θ) :
  Eq_sub (A ⋈ T) (A' ⋈ σ ⋆ T) (Subst.lift σ Χ) (Subst.lift θ Χ)
  := by
  intro α x hne
  rcases C.cover Γ Χ x with ⟨w, rfl⟩ | ⟨i, rfl⟩
  · have hd : Bd.applyAt (Subst.lift σ Χ) α ((A ⋈ T).declaration (C.inl w))
        = Bd.rename (Renaming.inl Γ' Χ ⇑ʳ α) (Bd.applyAt σ α (A.declaration w)) := by
      rw [dTel.declaration_concatenate_inl]
      apply Bd.act_square
      apply Subst.lift_inl
    have hb : dTel.actBase (Subst.lift σ Χ) ((A ⋈ T).binding (C.inl w))
        = dTel.rename (Renaming.inl Γ' Χ) (σ ⋆ A.binding w) := by
      rw [dTel.binding_concatenate_inl]
      apply dTel.actBase_square
      apply Subst.lift_inl
    rw [hd, Bd.isEq_rename] at hne
    rw [Subst.lift_inl, Subst.lift_inl]
    convert Eq_e.weaken ((Ambient.Renaming.weaken A' (σ ⋆ T)).extend (σ ⋆ A.binding w))
      (hst w hne) using 2
  · have hη := Wf_s.eta A' (σ ⋆ T) (Wf_t.subst_ambient hσ hT)
    have hd : Bd.applyAt (Subst.lift σ Χ) α ((A ⋈ T).declaration (C.inr i))
        = Subst.instId Γ' Χ ⋆ (dTel.rename (Renaming.inl Γ' Χ) (σ ⋆ T)).declaration i := by
      symm
      apply Eq.trans (dTel.act_declaration_instId (σ ⋆ T) i)
      rw [dTel.declaration_actBase, dTel.declaration_concatenate_inr]
      rfl
    have hb : dTel.actBase (Subst.lift σ Χ) ((A ⋈ T).binding (C.inr i))
        = Subst.instId Γ' Χ ⋆ (dTel.rename (Renaming.inl Γ' Χ) (σ ⋆ T)).binding i := by
      symm
      apply Eq.trans (dTel.instantiate_binding_instId (σ ⋆ T) i)
      rw [dTel.binding_actBase, dTel.binding_concatenate_inr]
      rfl
    rw [hd] at hne
    rw [Subst.lift_inr, Subst.lift_inr]
    convert Eq_e.refl (hη.filler i hne) using 2

/-- Agreeing well-formed substitutions from a well-formed ambient `A` to `A'` send
a boundary equal to itself over `A` to equal boundaries over `A'`. -/
theorem Eq_bd.agree
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'} {σ θ : Subst Γ Γ'}
    (hA : Ambient.Wf A) (hσ : Wf_sub A A' σ) (hθ : Wf_sub A A' θ) (hst : Eq_sub A A' σ θ) :
  ∀ {β : Bd Γ}, A ⊢ β ≈ β → A' ⊢ σ ⋆ β ≈ θ ⋆ β
  | _, .sort => .sort
  | _, .of h => .of (Eq_e.agree hA hσ hθ hst h.wf_left)
  | _, .eq hl hr =>
      .eq (Eq_e.agree hA hσ hθ hst hl.wf_left) (Eq_e.agree hA hσ hθ hst hr.wf_left)
