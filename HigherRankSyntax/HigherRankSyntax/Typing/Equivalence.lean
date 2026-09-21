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
