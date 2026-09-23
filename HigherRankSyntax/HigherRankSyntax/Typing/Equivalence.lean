import HigherRankSyntax.Typing.Invariance

/-!
# Equivalence

8(11): equality of telescopes and agreement of fillings are equivalence
relations.  Reflexivity is `Wf_t.refl` and `Wf_s.refl`.  Symmetry and
transitivity both compare over an ambient built from the telescope on one side,
so each step moves a comparison across an equal ambient.
-/

/-- 8(11): equality of telescopes is symmetric. -/
theorem Eq_t.symm {Δ Ω : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ)
    {Θ Θ' : dTel Δ Ω} (h : Eq_t Ξ Θ Θ') : Eq_t Ξ Θ' Θ :=
  (Eq_t.Both.symm (Eq_t.toBoth (Eq_t.Both.refl Eq_t.Both.nil hΞ) h)).toEq_t

/-- A well-formed declaration stays well formed at an equal boundary. -/
theorem Wf_bd.ofEq_bd {Δ Λ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Λ}
    (hΞ : Ambient.Wf (Ξ ⋈ Θ)) :
    ∀ {β β' : Bd (Δ ⋈ Λ)}, Wf_bd Ξ Θ β → Eq_bd (Ξ ⋈ Θ) β β' → Wf_bd Ξ Θ β'
  | _, _, .sort, h => by cases h; exact .sort
  | _, _, .of _ hsort, h => by
      cases h with
      | of hSS' =>
          refine Wf_bd.of (Eq_e.wf_right hSS') ?_
          exact (Eq_e.boundaryOf hΞ hSS').symm.trans hsort
  | _, _, .eq _ _ heq, h => by
      cases h with
      | eq hll' hrr' =>
          refine Wf_bd.eq (Eq_e.wf_right hll') (Eq_e.wf_right hrr') ?_
          refine Eq_bd.trans (Eq_e.boundaryOf hΞ hll').symm ?_
          exact heq.trans (Eq_e.boundaryOf hΞ hrr')

/-- A well-formed declaration stays well formed over equal bound entries. -/
theorem Wf_bd.ofEq_t {Δ Λ : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ)
    {Θ Θ' : dTel Δ Λ} (h : Eq_t Ξ Θ Θ') :
    ∀ {β : Bd (Δ ⋈ Λ)}, Wf_bd Ξ Θ β → Wf_bd Ξ Θ' β
  | _, .sort => .sort
  | _, .of hS hsort => by
      have hamb : Eq_t (.nil : Ambient 1) (Ξ ⋈ Θ) (Ξ ⋈ Θ') :=
        Eq_t.concatenate (Wf_t.refl hΞ) h
      refine Wf_bd.of (Wf_e.ofEq hamb hS) ?_
      exact Eq_bd.trans (boundaryOf_ofEq hamb hS) (Eq_bd.ofEq hamb hsort)
  | _, .eq hl hr heq => by
      have hamb : Eq_t (.nil : Ambient 1) (Ξ ⋈ Θ) (Ξ ⋈ Θ') :=
        Eq_t.concatenate (Wf_t.refl hΞ) h
      refine Wf_bd.eq (Wf_e.ofEq hamb hl) (Wf_e.ofEq hamb hr) ?_
      refine Eq_bd.trans (boundaryOf_ofEq hamb hl) ?_
      exact Eq_bd.trans (Eq_bd.ofEq hamb heq) (boundaryOf_ofEq hamb hr).symm

/-- A well-formed telescope stays well formed at an equal one. -/
theorem Wf_t.ofEq_t {Δ : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ) :
    ∀ {Ω : C.Arity} {Θ Θ' : dTel Δ Ω}, Wf_t Ξ Θ → Eq_t Ξ Θ Θ' → Wf_t Ξ Θ'
  | _, _, _, .nil, h => by
      obtain rfl := Eq_t.nil_inv h
      exact .nil
  | _, _, _, .cons (bind := bind) (boundary := boundary) hbindw hboundaryw hrestw,
      h => by
      obtain ⟨bind', boundary', rest', rfl, hbind, hboundary, hrest⟩ :=
        Eq_t.cons_inv h
      have hbindw' : Wf_t Ξ bind' := Wf_t.ofEq_t hΞ hbindw hbind
      have hboundaryw' : Wf_bd Ξ bind' boundary' :=
        Wf_bd.ofEq_t hΞ hbind
          (Wf_bd.ofEq_bd (Wf_t.concatenate hΞ hbindw) hboundaryw hboundary)
      have hhead : Eq_t (.nil : Ambient 1)
          (Ξ ⋈ dTel.cons bind boundary .nil)
          (Ξ ⋈ dTel.cons bind' boundary' .nil) :=
        Eq_t.concatenate (Wf_t.refl hΞ) (Eq_t.cons hbind hboundary Eq_t.nil)
      refine .cons hbindw' hboundaryw' ?_
      refine Wf_t.ofEq hhead ?_
      exact Wf_t.ofEq_t (Wf_t.concatenate hΞ (.cons hbindw hboundaryw .nil))
        hrestw hrest

/-- 8(11): equality of telescopes is transitive. -/
theorem Eq_t.trans {Δ : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ) :
    ∀ {Ω : C.Arity} {Θ Θ' Θ'' : dTel Δ Ω}, Wf_t Ξ Θ →
      Eq_t Ξ Θ Θ' → Eq_t Ξ Θ' Θ'' → Eq_t Ξ Θ Θ''
  | _, _, _, _, .nil, h, h' => by
      obtain rfl := Eq_t.nil_inv h
      obtain rfl := Eq_t.nil_inv h'
      exact Eq_t.nil
  | _, _, _, _, .cons (bind := bind) (boundary := boundary) hbindw hboundaryw
      hrestw, h, h' => by
      obtain ⟨bind', boundary', rest', rfl, hbind, hboundary, hrest⟩ :=
        Eq_t.cons_inv h
      obtain ⟨_, _, _, rfl, hbind', hboundary', hrest'⟩ := Eq_t.cons_inv h'
      have hheadw : Wf_t Ξ (dTel.cons bind boundary .nil) :=
        .cons hbindw hboundaryw .nil
      have hambbind : Eq_t (.nil : Ambient 1) (Ξ ⋈ bind') (Ξ ⋈ bind) :=
        Eq_t.concatenate (Wf_t.refl hΞ) (Eq_t.symm hΞ hbind)
      have hambhead : Eq_t (.nil : Ambient 1)
          (Ξ ⋈ dTel.cons bind boundary .nil)
          (Ξ ⋈ dTel.cons bind' boundary' .nil) :=
        Eq_t.concatenate (Wf_t.refl hΞ) (Eq_t.cons hbind hboundary Eq_t.nil)
      have hrestw' : Wf_t (Ξ ⋈ dTel.cons bind' boundary' .nil) rest' :=
        Wf_t.ofEq hambhead
          (Wf_t.ofEq_t (Wf_t.concatenate hΞ hheadw) hrestw hrest)
      refine Eq_t.cons (Eq_t.trans hΞ hbindw hbind hbind')
        (hboundary.trans (Eq_bd.ofEq hambbind hboundary')) ?_
      exact Eq_t.trans (Wf_t.concatenate hΞ hheadw) hrestw hrest
        (Eq_t.ofEq (Eq_t.symm (Wf_t.nil : Ambient.Wf (.nil : Ambient 1)) hambhead)
          hrestw' hrest')

/-- 8(9): agreeing fillings of a telescope send a well-formed telescope over the
extension to equal telescopes. -/
theorem Eq_t.agree_fill {Δ Ω Χ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω}
    {σ θ : Subst Ω Δ} (hΞ : Ambient.Wf Ξ) (hΘ : Wf_t Ξ Θ) (hσ : Wf_s Ξ Θ σ)
    (hθ : Wf_s Ξ Θ θ) (hst : Eq_s Ξ Θ σ θ) {X : dTel (Δ ⋈ Ω) Χ}
    (hX : Wf_t ((Ξ ⋈ Θ)) X) : Eq_t Ξ (σ ⋆ X) (θ ⋆ X) :=
  Eq_t.agree (Wf_t.concatenate hΞ hΘ) hΞ (hσ.toSub hΞ) (hθ.toSub hΞ)
    (hst.toSub hΞ) hX

/-- 8(11): agreement of fillings is symmetric. -/
theorem Eq_s.symm {Δ : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ) :
    ∀ {Ω : C.Arity} {Θ : dTel Δ Ω} {σ θ : Subst Ω Δ}, Eq_s Ξ Θ σ θ →
      Wf_t Ξ Θ → Wf_s Ξ Θ σ → Wf_s Ξ Θ θ → Eq_s Ξ Θ θ σ
  | _, _, _, _, .nil, _, _, _ => .nil
  | _, _, _, _, .cons (α := α) (σ := σ) (θ := θ) (bind := bind)
      (boundary := boundary) (rest := rest) slot hrest, hΘ, hσ, hθ => by
      obtain ⟨hbindw, hboundaryw, hrestw⟩ := Wf_t.cons_inv hΘ
      have hheadw : Wf_t Ξ (dTel.cons bind boundary .nil) :=
        .cons hbindw hboundaryw .nil
      have hTT' := Eq_t.agree_fill hΞ hheadw hσ.head hθ.head
        (Eq_s.cons slot Eq_s.nil) hrestw
      have hbase := Eq_t.Both.refl Eq_t.Both.nil hΞ
      have hθT : Wf_s Ξ
          (dTel.instantiate (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) rest)
          (fun ⦃β⦄ (j : _ ∋ β) => θ (C.inr j)) :=
        Wf_s.ofEq (Wf_t.refl hΞ) hθ.tail (Eq_t.symm hΞ hTT')
      refine .cons (fun hne => (slot hne).symm) ?_
      exact Eq_s.ofBoth hbase
        (Eq_s.symm hΞ hrest (Wf_t.instantiate hσ.head hrestw) hσ.tail hθT)
        (Eq_t.toBoth hbase hTT') hθT hθ.tail

/-- 8(11): agreement of fillings is transitive. -/
theorem Eq_s.trans {Δ : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ) :
    ∀ {Ω : C.Arity} {Θ : dTel Δ Ω} {σ θ κ : Subst Ω Δ}, Eq_s Ξ Θ σ θ →
      Eq_s Ξ Θ θ κ → Wf_t Ξ Θ → Wf_s Ξ Θ σ → Wf_s Ξ Θ θ → Eq_s Ξ Θ σ κ
  | _, _, _, _, _, .nil, _, _, _, _ => .nil
  | _, _, _, _, _, .cons (α := α) (σ := σ) (θ := θ) (bind := bind)
      (boundary := boundary) (rest := rest) slot hrest, h', hΘ, hσ, hθ => by
      obtain ⟨hbindw, hboundaryw, hrestw⟩ := Wf_t.cons_inv hΘ
      have hheadw : Wf_t Ξ (dTel.cons bind boundary .nil) :=
        .cons hbindw hboundaryw .nil
      have hTT' := Eq_t.agree_fill hΞ hheadw hσ.head hθ.head
        (Eq_s.cons slot Eq_s.nil) hrestw
      have hbase := Eq_t.Both.refl Eq_t.Both.nil hΞ
      have hθT : Wf_s Ξ
          (dTel.instantiate (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) rest)
          (fun ⦃β⦄ (j : _ ∋ β) => θ (C.inr j)) :=
        Wf_s.ofEq (Wf_t.refl hΞ) hθ.tail (Eq_t.symm hΞ hTT')
      refine .cons ?head ?tail
      case head =>
        intro hne
        refine (slot hne).trans ?_
        refine Eq.mp (congrArg (fun T => Eq_e ((Ξ ⋈ T))
          (θ (C.inl (C.singleSlot α))) _)
          (dTel.binding_head_instantiate bind boundary rest θ)) ?_
        exact h'.slot (C.inl (C.singleSlot α)) (fun hEq => hne
          (Eq.mp (congrArg Bd.isEq
            (dTel.declaration_head_instantiate bind boundary rest θ)) hEq))
      case tail =>
        refine Eq_s.trans hΞ hrest ?_ (Wf_t.instantiate hσ.head hrestw) hσ.tail hθT
        exact Eq_s.ofBoth hbase h'.tail (Eq_t.toBoth hbase (Eq_t.symm hΞ hTT'))
          hθ.tail hθT

/-- Agreement of substitutions between ambients is symmetric. -/
theorem Eq_sub.symm {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    {σ θ : Subst Γ Γ'} (hA : Ambient.Wf A) (hA' : Ambient.Wf A')
    (hst : Eq_sub A A' σ θ) (hσ : Wf_sub A A' σ) (hθ : Wf_sub A A' θ) :
    Eq_sub A A' θ σ :=
  Eq_s.toEq_sub (Eq_s.symm hA' hst.toAgreement (hA.weaken A')
    hσ.toFilling hθ.toFilling)

/-- Agreement of substitutions between ambients is transitive. -/
theorem Eq_sub.trans {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    {σ θ κ : Subst Γ Γ'} (hA : Ambient.Wf A) (hA' : Ambient.Wf A')
    (hst : Eq_sub A A' σ θ) (htk : Eq_sub A A' θ κ)
    (hσ : Wf_sub A A' σ) (hθ : Wf_sub A A' θ) : Eq_sub A A' σ κ :=
  Eq_s.toEq_sub (Eq_s.trans hA' hst.toAgreement htk.toAgreement (hA.weaken A')
    hσ.toFilling hθ.toFilling)

/-- Composition of substitutions between ambients respects agreement. -/
theorem Eq_sub.comp {Γ Δ Ω : C.Arity} {A : Ambient Γ} {B : Ambient Δ}
    {D : Ambient Ω} {τ τ' : Subst Γ Δ} {σ σ' : Subst Δ Ω}
    (hA : Ambient.Wf A) (hB : Ambient.Wf B) (hD : Ambient.Wf D)
    (hτ : Wf_sub A B τ) (hτ' : Wf_sub A B τ')
    (hσ : Wf_sub B D σ) (hσ' : Wf_sub B D σ')
    (htt : Eq_sub A B τ τ') (hss : Eq_sub B D σ σ') :
    Eq_sub A D (Subst.comp (Γ := 1) τ σ) (Subst.comp (Γ := 1) τ' σ') := by
  refine Eq_sub.trans hA hD ?first ?second (hτ.comp hσ) (hτ'.comp hσ)
  case first =>
    refine Eq_s.toEq_sub (Eq.mp (congrArg (fun T => Eq_s D T
      (Subst.comp (Γ := 1) τ σ) (Subst.comp (Γ := 1) τ' σ))
      (Ambient.actBase_weaken A σ)) ?_)
    exact Eq_s.subst_ambient hσ htt.toAgreement
  case second =>
    intro α x hne
    have hT : Wf_t B (τ' ⋆ A.binding x) :=
      Wf_t.subst_ambient hτ' (Wf_t.binding hA x)
    have hbase := Eq_t.Both.refl Eq_t.Both.nil hD
    have hamb := Eq_t.Both.concatenate hbase
      (Eq_t.toBoth hbase (Eq_t.agree hB hD hσ hσ' hss hT))
    have hlift := Wf_sub.ofBoth (Wf_t.concatenate hB hT) hamb.symm
      (Wf_sub.lift hσ' hT)
    have hne' : ¬ (Bd.applyAt τ' α (A.declaration x)).isEq := by
      intro hEq
      refine hne (Eq.mp (congrArg Bd.isEq
        (Bd.act_comp τ' σ α (A.declaration x)).symm) ?_)
      exact (Bd.isEq_act σ α _).mpr hEq
    have hres := Eq_e.agree (Wf_t.concatenate hB hT) (Wf_sub.lift hσ hT) hlift
      (Eq_sub.lift hσ hT hss) ((hτ' x).2.1 hne')
    have hdepth := Eq.mp (congrArg₂
      (Eq_e (D ⋈ dTel.actBase σ (dTel.actBase τ' (A.binding x))))
      (Subst.act_lift_depth σ (τ' x)) (Subst.act_lift_depth σ' (τ' x))) hres
    exact Eq.mp (congrArg (fun T₀ => Eq_e (D ⋈ T₀)
      (Subst.act (Γ := 1) σ α (τ' x)) (Subst.act (Γ := 1) σ' α (τ' x)))
      (dTel.actBase_comp τ' σ (A.binding x)).symm) hdepth

/-- 8(10): a filling is invariant under an equal telescope. -/
theorem Wf_s.ofEq_t {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ Θ' : dTel Δ Ω}
    {σ : Subst Ω Δ} (hΞ : Ambient.Wf Ξ) (hσ : Wf_s Ξ Θ σ) (h : Eq_t Ξ Θ Θ') :
    Wf_s Ξ Θ' σ :=
  Wf_s.ofEq (Wf_t.refl hΞ) hσ h

/-- 8(10): agreement of fillings is invariant under an equal telescope. -/
theorem Eq_s.ofEq_t {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ Θ' : dTel Δ Ω}
    {σ θ : Subst Ω Δ} (hΞ : Ambient.Wf Ξ) (hst : Eq_s Ξ Θ σ θ)
    (hσ : Wf_s Ξ Θ σ) (h : Eq_t Ξ Θ Θ') : Eq_s Ξ Θ' σ θ :=
  Eq_s.ofBoth (Eq_t.Both.refl Eq_t.Both.nil hΞ) hst
    (Eq_t.toBoth (Eq_t.Both.refl Eq_t.Both.nil hΞ) h) hσ
    (Wf_s.ofEq (Wf_t.refl hΞ) hσ h)

/-- 8(9): agreeing substitutions between ambients send a filling to agreeing
fillings. -/
theorem Eq_s.agree {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    {σ θ : Subst Γ Γ'} (hA : Ambient.Wf A) (hA' : Ambient.Wf A')
    (hσ : Wf_sub A A' σ) (hθ : Wf_sub A A' θ) (hst : Eq_sub A A' σ θ)
    {Χ : C.Arity} {X : dTel Γ Χ} {τ : Subst Χ Γ} (hX : Wf_t A X)
    (hτ : Wf_s A X τ) : Eq_s A' (σ ⋆ X) (σ ⋆ τ) (θ ⋆ τ) := by
  refine Eq_s.slotwise_actBase X σ ?_
  intro Λ z hne
  have hb := dTel.binding_actBase σ X z
  have hd := dTel.declaration_actBase σ X z
  have hint := dTel.actBase_instantiate σ τ (X.binding z)
  have hT : Wf_t A (dTel.instantiate τ (X.binding z)) :=
    Wf_t.instantiate hτ (Wf_t.binding hX z)
  have hne' : ¬ (Bd.fill τ (X.declaration z)).isEq := by
    intro hEq
    refine hne (Eq.mp (congrArg
      (fun b => (Bd.fill (Subst.applyEach σ τ) b).isEq) hd.symm) ?_)
    exact (Bd.isEq_act _ _ _).mpr ((Bd.isEq_act _ _ _).mpr
      ((Bd.isEq_act _ _ _).mp hEq))
  have hbase := Eq_t.Both.refl Eq_t.Both.nil hA'
  have hamb := Eq_t.Both.concatenate hbase
    (Eq_t.toBoth hbase (Eq_t.agree hA hA' hσ hθ hst hT))
  have hθlift := Wf_sub.ofBoth (Wf_t.concatenate hA hT) hamb.symm
    (Wf_sub.lift hθ hT)
  have hres := Eq_e.agree (Wf_t.concatenate hA hT) (Wf_sub.lift hσ hT) hθlift
    (Eq_sub.lift hσ hT hst) (Wf_s.filler hτ z hne')
  have hdepth := Eq.mp (congrArg₂
    (Eq_e (A' ⋈ dTel.actBase σ (dTel.instantiate τ (X.binding z))))
    (Subst.act_lift_depth σ (τ z)) (Subst.act_lift_depth θ (τ z))) hres
  refine Eq.mp (congrArg (fun T => Eq_e (A' ⋈ T)
    (Subst.act (Γ := 1) σ Λ (τ z)) (Subst.act (Γ := 1) θ Λ (τ z))) ?_) hdepth
  exact hint.trans (congrArg (dTel.instantiate (Subst.applyEach σ τ)) hb.symm)
