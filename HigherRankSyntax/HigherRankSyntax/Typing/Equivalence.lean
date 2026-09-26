import HigherRankSyntax.Typing.Invariance

/-!
# Equivalence

Over a well-formed ambient, equality of telescopes is an equivalence relation on
well-formed telescopes, and agreement is an equivalence relation on the fillings
of a well-formed telescope; reflexivity is `Wf_t.refl` and `Wf_s.refl`.
Well-formed declarations, telescopes and fillings stay well formed, and
agreements of fillings stay agreements, at equal boundaries and telescopes.
Agreeing fillings of a well-formed telescope `Θ` send a well-formed telescope
over the ambient extended by `Θ` to equal telescopes, and agreeing substitutions
between well-formed ambients send a filling to agreeing fillings.  Agreement of
substitutions between well-formed ambients is transitive and respected by
composition.
-/

/-- Over a well-formed ambient, equality of telescopes is symmetric. -/
theorem Eq_t.symm
    {Δ Ω : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ)
    {Θ Θ' : dTel Δ Ω} (h : Eq_t Ξ Θ Θ') :
  Eq_t Ξ Θ' Θ
  := by
  apply Eq_t.Both.toEq_t
  apply Eq_t.Both.symm
  apply Eq_t.toBoth (Eq_t.Both.refl Eq_t.Both.nil hΞ) h

/-- If `Ξ ⋈ Θ` is well formed, a declaration well formed over `Ξ` with bound
entries `Θ` stays well formed at every boundary equal to it over `Ξ ⋈ Θ`. -/
theorem Wf_bd.ofEq_bd
    {Δ Λ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Λ} (hΞ : Ambient.Wf (Ξ ⋈ Θ)) :
  ∀ {β β' : Bd (Δ ⋈ Λ)}, Wf_bd Ξ Θ β → Eq_bd (Ξ ⋈ Θ) β β' → Wf_bd Ξ Θ β'
  | _, _, .sort, .sort => .sort
  | _, _, .of _ hsort, .of hSS' => by
      apply Wf_bd.of (Eq_e.wf_right hSS')
      apply Eq_bd.trans (Eq_bd.symm (Eq_e.boundaryOf hΞ hSS')) hsort
  | _, _, .eq _ _ heq, .eq hll' hrr' => by
      apply Wf_bd.eq (Eq_e.wf_right hll') (Eq_e.wf_right hrr')
      apply Eq_bd.trans (Eq_bd.symm (Eq_e.boundaryOf hΞ hll'))
      apply Eq_bd.trans heq (Eq_e.boundaryOf hΞ hrr')

/-- If `Ξ` is well formed and `Θ` and `Θ'` are equal over `Ξ`, a declaration
well formed over `Ξ` with bound entries `Θ` is well formed with bound entries
`Θ'`. -/
theorem Wf_bd.ofEq_t
    {Δ Λ : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ)
    {Θ Θ' : dTel Δ Λ} (h : Eq_t Ξ Θ Θ') :
  ∀ {β : Bd (Δ ⋈ Λ)}, Wf_bd Ξ Θ β → Wf_bd Ξ Θ' β
  | _, .sort => .sort
  | _, .of hS hsort => by
      have hamb := Eq_t.concatenate (Wf_t.refl hΞ) h
      apply Wf_bd.of (Wf_e.ofEq hamb hS)
      apply Eq_bd.trans (boundaryOf_ofEq hamb hS) (Eq_bd.ofEq hamb hsort)
  | _, .eq hl hr heq => by
      have hamb := Eq_t.concatenate (Wf_t.refl hΞ) h
      apply Wf_bd.eq (Wf_e.ofEq hamb hl) (Wf_e.ofEq hamb hr)
      apply Eq_bd.trans (boundaryOf_ofEq hamb hl)
      apply Eq_bd.trans (Eq_bd.ofEq hamb heq) (Eq_bd.symm (boundaryOf_ofEq hamb hr))

/-- Over a well-formed ambient, a telescope equal to a well-formed telescope is
well formed. -/
theorem Wf_t.ofEq_t {Δ : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ) :
  ∀ {Ω : C.Arity} {Θ Θ' : dTel Δ Ω}, Wf_t Ξ Θ → Eq_t Ξ Θ Θ' → Wf_t Ξ Θ'
  | _, _, _, .nil, h => by
      obtain rfl := Eq_t.nil_inv h
      apply Wf_t.nil
  | _, _, _, .cons hbind hboundary hrest, h => by
      obtain ⟨_, _, _, rfl, hbind', hboundary', hrest'⟩ := Eq_t.cons_inv h
      apply Wf_t.cons (Wf_t.ofEq_t hΞ hbind hbind')
      · apply Wf_bd.ofEq_t hΞ hbind'
        apply Wf_bd.ofEq_bd (Wf_t.concatenate hΞ hbind) hboundary hboundary'
      · apply Wf_t.ofEq (Eq_t.concatenate (Wf_t.refl hΞ) (Eq_t.cons hbind' hboundary' Eq_t.nil))
        apply Wf_t.ofEq_t (Wf_t.concatenate hΞ (Wf_t.cons hbind hboundary .nil)) hrest hrest'

/-- A filling of a telescope over a well-formed ambient is a filling of every
equal telescope. -/
theorem Wf_s.ofEq_t
    {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ Θ' : dTel Δ Ω} {σ : Subst Ω Δ}
    (hΞ : Ambient.Wf Ξ) (hσ : Wf_s Ξ Θ σ) (h : Eq_t Ξ Θ Θ') :
  Wf_s Ξ Θ' σ
  := Wf_s.ofEq (Wf_t.refl hΞ) hσ h

/-- Over a well-formed ambient, if `σ` fills `Θ`, then `σ` and `θ` agreeing as
fillings of `Θ` agree as fillings of every telescope equal to `Θ`. -/
theorem Eq_s.ofEq_t
    {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ Θ' : dTel Δ Ω} {σ θ : Subst Ω Δ}
    (hΞ : Ambient.Wf Ξ) (hst : Eq_s Ξ Θ σ θ) (hσ : Wf_s Ξ Θ σ) (h : Eq_t Ξ Θ Θ') :
  Eq_s Ξ Θ' σ θ
  := by
  have hbase := Eq_t.Both.refl Eq_t.Both.nil hΞ
  apply Eq_s.ofBoth hbase hst (Eq_t.toBoth hbase h) hσ (Wf_s.ofEq_t hΞ hσ h)

/-- Over a well-formed ambient, equality of telescopes is transitive, provided
the first telescope is well formed. -/
theorem Eq_t.trans {Δ : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ) :
  ∀ {Ω : C.Arity} {Θ Θ' Θ'' : dTel Δ Ω}, Wf_t Ξ Θ →
    Eq_t Ξ Θ Θ' → Eq_t Ξ Θ' Θ'' → Eq_t Ξ Θ Θ''
  | _, _, _, _, .nil, h, h' => by
      obtain rfl := Eq_t.nil_inv h
      obtain rfl := Eq_t.nil_inv h'
      apply Eq_t.nil
  | _, _, _, _, .cons hbind hboundary hrest, h, h' => by
      obtain ⟨_, _, _, rfl, hbind', hboundary', hrest'⟩ := Eq_t.cons_inv h
      obtain ⟨_, _, _, rfl, hbind'', hboundary'', hrest''⟩ := Eq_t.cons_inv h'
      have hhead := Wf_t.cons hbind hboundary .nil
      have hambhead := Eq_t.concatenate (Wf_t.refl hΞ) (Eq_t.cons hbind' hboundary' Eq_t.nil)
      apply Eq_t.cons (Eq_t.trans hΞ hbind hbind' hbind'')
      · apply Eq_bd.trans hboundary'
        apply Eq_bd.ofEq (Eq_t.concatenate (Wf_t.refl hΞ) (Eq_t.symm hΞ hbind')) hboundary''
      · apply Eq_t.trans (Wf_t.concatenate hΞ hhead) hrest hrest'
        apply Eq_t.ofEq (Eq_t.symm Wf_t.nil hambhead) _ hrest''
        apply Wf_t.ofEq hambhead (Wf_t.ofEq_t (Wf_t.concatenate hΞ hhead) hrest hrest')

/-- Over a well-formed ambient `Ξ`, agreeing fillings `σ` and `θ` of a
well-formed telescope `Θ` send every telescope `X` well formed over `Ξ ⋈ Θ` to
telescopes `σ ⋆ X` and `θ ⋆ X` equal over `Ξ`. -/
theorem Eq_t.agree_fill
    {Δ Ω Χ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω} {σ θ : Subst Ω Δ}
    (hΞ : Ambient.Wf Ξ) (hΘ : Wf_t Ξ Θ) (hσ : Wf_s Ξ Θ σ) (hθ : Wf_s Ξ Θ θ)
    (hst : Eq_s Ξ Θ σ θ) {X : dTel (Δ ⋈ Ω) Χ} (hX : Wf_t (Ξ ⋈ Θ) X) :
  Eq_t Ξ (σ ⋆ X) (θ ⋆ X)
  := Eq_t.agree (Wf_t.concatenate hΞ hΘ) hΞ (hσ.toSub hΞ) (hθ.toSub hΞ) (hst.toSub hΞ) hX

/-- Over a well-formed ambient, agreement of fillings of a well-formed telescope
is symmetric. -/
theorem Eq_s.symm {Δ : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ) :
  ∀ {Ω : C.Arity} {Θ : dTel Δ Ω} {σ θ : Subst Ω Δ}, Eq_s Ξ Θ σ θ →
    Wf_t Ξ Θ → Wf_s Ξ Θ σ → Wf_s Ξ Θ θ → Eq_s Ξ Θ θ σ
  | _, _, _, _, .nil, _, _, _ => .nil
  | _, _, _, _, .cons slot hrest, hΘ, hσ, hθ => by
      obtain ⟨hbind, hboundary, hrestwf⟩ := Wf_t.cons_inv hΘ
      have htail := Eq_t.agree_fill hΞ (Wf_t.cons hbind hboundary .nil) hσ.head hθ.head
        (Eq_s.cons slot Eq_s.nil) hrestwf
      have hθtail := Wf_s.ofEq_t hΞ hθ.tail (Eq_t.symm hΞ htail)
      apply Eq_s.cons
      · intro hne
        apply Eq_e.symm (slot hne)
      · apply Eq_s.ofEq_t hΞ _ hθtail htail
        apply Eq_s.symm hΞ hrest (Wf_t.instantiate hσ.head hrestwf) hσ.tail hθtail

/-- Over a well-formed ambient, agreement of fillings of a well-formed telescope
is transitive. -/
theorem Eq_s.trans {Δ : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ) :
  ∀ {Ω : C.Arity} {Θ : dTel Δ Ω} {σ θ κ : Subst Ω Δ}, Eq_s Ξ Θ σ θ →
    Eq_s Ξ Θ θ κ → Wf_t Ξ Θ → Wf_s Ξ Θ σ → Wf_s Ξ Θ θ → Eq_s Ξ Θ σ κ
  | _, _, _, _, _, .nil, _, _, _, _ => .nil
  | _, _, _, _, _, .cons (α := α) slot hrest, h', hΘ, hσ, hθ => by
      obtain ⟨hbind, hboundary, hrestwf⟩ := Wf_t.cons_inv hΘ
      have htail := Eq_t.agree_fill hΞ (Wf_t.cons hbind hboundary .nil) hσ.head hθ.head
        (Eq_s.cons slot Eq_s.nil) hrestwf
      have hθtail := Wf_s.ofEq_t hΞ hθ.tail (Eq_t.symm hΞ htail)
      apply Eq_s.cons
      · intro hne
        have hhead := h'.slot (C.inl (C.singleSlot α))
        rw [dTel.declaration_head_instantiate] at hhead
        apply Eq_e.trans (slot hne)
        convert hhead hne using 2
        symm
        apply dTel.binding_head_instantiate
      · apply Eq_s.trans hΞ hrest _ (Wf_t.instantiate hσ.head hrestwf) hσ.tail hθtail
        apply Eq_s.ofEq_t hΞ h'.tail hθ.tail (Eq_t.symm hΞ htail)

/-- Agreement of well-formed substitutions between well-formed ambients is
transitive. -/
theorem Eq_sub.trans
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'} {σ θ κ : Subst Γ Γ'}
    (hA : Ambient.Wf A) (hA' : Ambient.Wf A')
    (hst : Eq_sub A A' σ θ) (htk : Eq_sub A A' θ κ)
    (hσ : Wf_sub A A' σ) (hθ : Wf_sub A A' θ) :
  Eq_sub A A' σ κ
  := by
  apply Eq_s.toEq_sub
  apply Eq_s.trans hA' hst.toAgreement htk.toAgreement (hA.weaken A') hσ.toFilling
    hθ.toFilling

/-- Composition of well-formed substitutions between well-formed ambients
respects agreement. -/
theorem Eq_sub.comp
    {Γ Δ Ω : C.Arity} {A : Ambient Γ} {B : Ambient Δ} {D : Ambient Ω}
    {τ τ' : Subst Γ Δ} {σ σ' : Subst Δ Ω}
    (hA : Ambient.Wf A) (hB : Ambient.Wf B) (hD : Ambient.Wf D)
    (hτ : Wf_sub A B τ) (hτ' : Wf_sub A B τ')
    (hσ : Wf_sub B D σ) (hσ' : Wf_sub B D σ')
    (htt : Eq_sub A B τ τ') (hss : Eq_sub B D σ σ') :
  Eq_sub A D (Subst.comp (Γ := 1) τ σ) (Subst.comp (Γ := 1) τ' σ')
  := by
  apply Eq_sub.trans hA hD _ _ (hτ.comp hσ) (hτ'.comp hσ)
  · apply Eq_s.toEq_sub
    rw [← Ambient.actBase_weaken A σ]
    apply Eq_s.subst_ambient hσ htt.toAgreement
  · intro α x hne
    have hT := Wf_t.subst_ambient hτ' (Wf_t.binding hA x)
    have hbase := Eq_t.Both.refl Eq_t.Both.nil hD
    have hamb := Eq_t.Both.concatenate hbase
      (Eq_t.toBoth hbase (Eq_t.agree hB hD hσ hσ' hss hT))
    have hσ'lift := Wf_sub.ofBoth (Wf_t.concatenate hB hT) hamb.symm (Wf_sub.lift hσ' hT)
    have hne' : ¬ (Bd.applyAt τ' α (A.declaration x)).isEq := by
      intro hEq
      apply hne
      apply (Bd.isEq_act _ _ _).mpr
      apply (Bd.isEq_act _ _ _).mp hEq
    obtain ⟨_, hfiller, _⟩ := hτ' x
    convert Eq_e.agree (Wf_t.concatenate hB hT) (Wf_sub.lift hσ hT) hσ'lift
      (Eq_sub.lift hσ hT hss) (hfiller hne') using 2
    · apply dTel.actBase_comp
    · symm
      apply Subst.act_lift_depth
    · symm
      apply Subst.act_lift_depth

/-- If `σ` and `θ` are well-formed agreeing substitutions from a well-formed `A`
to a well-formed `A'` and `τ` fills a telescope `X` well formed over `A`, then
`σ ⋆ τ` and `θ ⋆ τ` agree as fillings of `σ ⋆ X` over `A'`. -/
theorem Eq_s.agree
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'} {σ θ : Subst Γ Γ'}
    (hA : Ambient.Wf A) (hA' : Ambient.Wf A')
    (hσ : Wf_sub A A' σ) (hθ : Wf_sub A A' θ) (hst : Eq_sub A A' σ θ)
    {Χ : C.Arity} {X : dTel Γ Χ} {τ : Subst Χ Γ} (hX : Wf_t A X) (hτ : Wf_s A X τ) :
  Eq_s A' (σ ⋆ X) (σ ⋆ τ) (θ ⋆ τ)
  := by
  apply Eq_s.slotwise_actBase
  intro Λ z hne
  have hT := Wf_t.instantiate hτ (Wf_t.binding hX z)
  have hne' : ¬ (τ ⋆ X.declaration z).isEq := by
    intro hEq
    apply hne
    rw [dTel.declaration_actBase]
    apply (Bd.isEq_act _ _ _).mpr
    apply (Bd.isEq_act _ _ _).mpr
    apply (Bd.isEq_act _ _ _).mp hEq
  have hbase := Eq_t.Both.refl Eq_t.Both.nil hA'
  have hamb := Eq_t.Both.concatenate hbase
    (Eq_t.toBoth hbase (Eq_t.agree hA hA' hσ hθ hst hT))
  have hθlift := Wf_sub.ofBoth (Wf_t.concatenate hA hT) hamb.symm (Wf_sub.lift hθ hT)
  convert Eq_e.agree (Wf_t.concatenate hA hT) (Wf_sub.lift hσ hT) hθlift
    (Eq_sub.lift hσ hT hst) (Wf_s.filler hτ z hne') using 2
  · rw [dTel.binding_actBase, dTel.actBase_instantiate]
    rfl
  · symm
    apply Subst.act_lift_depth
  · symm
    apply Subst.act_lift_depth
