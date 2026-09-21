import HigherRankSyntax.Typing.SubstitutionLemma

/-!
# Invariance under an equal ambient and telescope agreement

8(10): every judgement holds over an ambient exactly when it holds over an
`Eq_t`-equal one.  The ambient enters a derivation through the `isEq` test on a
head's declaration, through the entries a head binds, through the declaration
named by `Eq_e.hyp`, and through `boundaryOf`; the last two read the declaration
comparison over the ambient built from the *second* telescope, which `Eq_t` does
not carry.  The block is therefore stated over `Eq_t.Both`, which carries both
readings, and `Eq_t.toBoth` supplies it.

8(9): agreeing substitutions send a well-formed telescope to equal telescopes.
Invariance lets both lifted substitutions land in the ambient extended by the
first substituted binding or prefix.
-/

/-- Equal boundaries assert an equation together. -/
theorem Eq_bd.isEq {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {β β' : Bd Δ}, Eq_bd Ξ β β' → (β.isEq ↔ β'.isEq)
  | _, _, .sort => Iff.rfl
  | _, _, .of _ => Iff.rfl
  | _, _, .eq _ _ => Iff.rfl

mutual

/-- 8(10): well-formedness of expressions is invariant under an equal ambient. -/
theorem Wf_e.ofBoth {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) A B) :
    ∀ {e : Expr Δ}, A ⊢ e → B ⊢ e
  | _, .ap x args head fill =>
      .ap x args (fun hne => head ((Eq_bd.isEq (h.toEq_t.declaration x)).mpr hne))
        (Wf_s.ofBoth h fill (h.binding x))

/-- 8(10): the computed boundary of a well-formed expression over an equal
ambient is equal to the one over the original. -/
theorem boundaryOf_ofBoth {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) A B) :
    ∀ {e : Expr Δ}, A ⊢ e → Eq_bd B (B.boundaryOf e) (A.boundaryOf e)
  | _, .ap x args _ fill =>
      Eq_bd.instantiate (Wf_s.ofBoth h fill (h.binding x))
        (h.declaration_right x).symm

/-- 8(10): equality of expressions is invariant under an equal ambient. -/
theorem Eq_e.ofBoth {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) A B) :
    ∀ {e e' : Expr Δ}, A ⊢ e ≈ e' → B ⊢ e ≈ e'
  | _, _, .refl he => .refl (Wf_e.ofBoth h he)
  | _, _, .symm he => .symm (Eq_e.ofBoth h he)
  | _, _, .trans he he' => .trans (Eq_e.ofBoth h he) (Eq_e.ofBoth h he')
  | _, _, .hyp q _ _ args decl _ _ fill => by
      have hfill : Wf_s B (B.binding q) args := Wf_s.ofBoth h fill (h.binding q)
      obtain ⟨_, _, hdecl, hl, hr⟩ :=
        Eq_bd.eq_inv (Eq.mp (congrArg
          (fun β => Eq_bd (B ⋈ B.binding q) β (B.declaration q)) decl)
          (h.declaration_right q))
      refine .trans (Eq_e.instantiate hfill hl)
        (.trans ?_ (Eq_e.instantiate hfill hr).symm)
      exact .hyp q _ _ args hdecl (Eq_e.wf_right hl) (Eq_e.wf_right hr) hfill
  | _, _, .congr σ θ hΘ hσ hθ agree he =>
      .congr σ θ (Wf_t.ofBoth h hΘ) (Wf_s.ofBoth h hσ (Eq_t.Both.refl h hΘ))
        (Wf_s.ofBoth h hθ (Eq_t.Both.refl h hΘ))
        (Eq_s.ofBoth h (Eq_t.Both.refl h hΘ) hσ
          (Wf_s.ofBoth h hσ (Eq_t.Both.refl h hΘ)) agree)
        (Eq_e.ofBoth (Eq_t.Both.concatenate h (Eq_t.Both.refl h hΘ)) he)

/-- 8(10): equality of boundaries is invariant under an equal ambient. -/
theorem Eq_bd.ofBoth {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) A B) :
    ∀ {β β' : Bd Δ}, A ⊢ β ≈ β' → B ⊢ β ≈ β'
  | _, _, .sort => .sort
  | _, _, .of he => .of (Eq_e.ofBoth h he)
  | _, _, .eq hl hr => .eq (Eq_e.ofBoth h hl) (Eq_e.ofBoth h hr)

/-- 8(10): filling is invariant under an equal ambient and an equal telescope. -/
theorem Wf_s.ofBoth {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) A B) :
    ∀ {Ω : C.Arity} {T T' : dTel Δ Ω} {τ : Subst Ω Δ},
      A ⊢ τ : T → Eq_t.Both A B T T' → B ⊢ τ : T'
  | _, _, _, _, .nil, hT => by
      obtain rfl := Eq_t.Both.nil_inv hT
      exact .nil
  | _, _, _, _, .cons (α := α) (σ := τ) (bind := bind) (boundary := boundary)
      (rest := rest) equation filler declared hrest, hT => by
      obtain ⟨bind', boundary', rest', rfl, hbind, hboundary, hb', hrest'⟩ :=
        Eq_t.Both.cons_inv hT
      have hamb : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1)
          (A ⋈ bind) (B ⋈ bind') := Eq_t.Both.concatenate h hbind
      have hequation : ∀ l r : Expr (Δ ⋈ α), boundary' = .eq l r →
          Eq_e (B ⋈ bind') l r := by
        intro l r hβ'
        obtain ⟨l₀, r₀, hβ, hl, hr⟩ := Eq_bd.eq_inv (Eq_bd.symm
          (Eq.mp (congrArg (Eq_bd (B ⋈ bind') boundary) hβ') hb'))
        exact hl.trans ((Eq_e.ofBoth hamb (equation l₀ r₀ hβ)).trans hr.symm)
      have hfiller : ¬ boundary'.isEq →
          Wf_e (B ⋈ bind') (τ (C.inl (C.singleSlot α))) :=
        fun hne => Wf_e.ofBoth hamb
          (filler (fun hEq => hne ((Eq_bd.isEq hb').mp hEq)))
      have hdeclared : ¬ boundary'.isEq →
          Eq_bd (B ⋈ bind')
            ((B ⋈ bind').boundaryOf (τ (C.inl (C.singleSlot α)))) boundary' := by
        intro hne
        have h₀ : ¬ boundary.isEq := fun hEq => hne ((Eq_bd.isEq hb').mp hEq)
        refine Eq_bd.trans ?_ hb'
        exact Eq_bd.trans (boundaryOf_ofBoth hamb (filler h₀))
          (Eq_bd.ofBoth hamb (declared h₀))
      have hκ : Wf_s A (dTel.cons bind boundary .nil)
          (fun ⦃β⦄ (i : C.single α ∋ β) => τ (C.inl i)) :=
        .cons equation filler declared .nil
      have hκ' : Wf_s B (dTel.cons bind' boundary' .nil)
          (fun ⦃β⦄ (i : C.single α ∋ β) => τ (C.inl i)) :=
        .cons hequation hfiller hdeclared .nil
      exact .cons hequation hfiller hdeclared
        (Wf_s.ofBoth h hrest (Eq_t.Both.filling (Wf_s.filling hκ)
          (Wf_s.filling hκ') rfl hrest'))

/-- 8(10): agreement is invariant under an equal ambient and an equal
telescope. -/
theorem Eq_s.ofBoth {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) A B) :
    ∀ {Ω : C.Arity} {T T' : dTel Δ Ω} {σ θ : Subst Ω Δ},
      Eq_t.Both A B T T' → A ⊢ σ : T → B ⊢ σ : T' → A ⊢ σ ≈ θ : T →
        B ⊢ σ ≈ θ : T'
  | _, _, _, σ, _, hT, hσ, hσ', .mk slot => by
      refine .mk (fun _ z hne => ?_)
      refine Eq_e.ofBoth (Eq_t.Both.concatenate h
        (Eq_t.Both.filling (Wf_s.filling hσ) (Wf_s.filling hσ') rfl
          (hT.binding z))) ?_
      exact slot z (fun hEq => hne
        ((Eq_bd.isEq (Eq_bd.subst hσ (hT.toEq_t.declaration z))).mp hEq))

/-- 8(10): a well-formed declaration is invariant under an equal ambient. -/
theorem Wf_bd.ofBoth {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) A B) :
    ∀ {Ω : C.Arity} {T : dTel Δ Ω} {β : Bd (Δ ⋈ Ω)},
      Eq_t.Both A B T T → Wf_bd A T β → Wf_bd B T β
  | _, _, _, _, .sort => .sort
  | _, _, _, hT, .of hS hsort => by
      have hamb := Eq_t.Both.concatenate h hT
      refine Wf_bd.of (Wf_e.ofBoth hamb hS) ?_
      exact Eq_bd.trans (boundaryOf_ofBoth hamb hS) (Eq_bd.ofBoth hamb hsort)
  | _, _, _, hT, .eq hl hr heq => by
      have hamb := Eq_t.Both.concatenate h hT
      refine Wf_bd.eq (Wf_e.ofBoth hamb hl) (Wf_e.ofBoth hamb hr) ?_
      refine Eq_bd.trans (boundaryOf_ofBoth hamb hl) ?_
      exact Eq_bd.trans (Eq_bd.ofBoth hamb heq) (boundaryOf_ofBoth hamb hr).symm

/-- A well-formed telescope is equal to itself over two equal ambients. -/
theorem Eq_t.Both.refl {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) A B) :
    ∀ {Ω : C.Arity} {T : dTel Δ Ω}, Wf_t A T → Eq_t.Both A B T T
  | _, _, .nil => Eq_t.Both.nil
  | _, _, .cons hbind hboundary hrest => by
      have hb := Eq_t.Both.refl h hbind
      have hhead := Eq_t.Both.cons hb (Wf_bd.refl hboundary)
        (Wf_bd.refl (Wf_bd.ofBoth h hb hboundary)) Eq_t.Both.nil
      exact Eq_t.Both.cons hb (Wf_bd.refl hboundary)
        (Wf_bd.refl (Wf_bd.ofBoth h hb hboundary))
        (Eq_t.Both.refl (Eq_t.Both.concatenate h hhead) hrest)

/-- 8(10): a well-formed telescope is invariant under an equal ambient. -/
theorem Wf_t.ofBoth {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) A B) :
    ∀ {Ω : C.Arity} {T : dTel Δ Ω}, Wf_t A T → Wf_t B T
  | _, _, .nil => .nil
  | _, _, .cons hbind hboundary hrest => by
      have hb := Eq_t.Both.refl h hbind
      have hhead := Eq_t.Both.cons hb (Wf_bd.refl hboundary)
        (Wf_bd.refl (Wf_bd.ofBoth h hb hboundary)) Eq_t.Both.nil
      exact .cons (Wf_t.ofBoth h hbind) (Wf_bd.ofBoth h hb hboundary)
        (Wf_t.ofBoth (Eq_t.Both.concatenate h hhead) hrest)

end

/-- Equal telescopes are equal over both of the ambients they build. -/
theorem Eq_t.toBoth {Δ : C.Arity} {Ξ Ξ' : Ambient Δ}
    (hΞ : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) Ξ Ξ') :
    ∀ {Ω : C.Arity} {Θ Θ' : dTel Δ Ω}, Eq_t Ξ Θ Θ' → Eq_t.Both Ξ Ξ' Θ Θ'
  | _, .nil, _, h => by
      obtain rfl := Eq_t.nil_inv h
      exact Eq_t.Both.nil
  | _, .cons bind boundary rest, _, h => by
      obtain ⟨bind', boundary', rest', rfl, hbind, hboundary, hrest⟩ :=
        Eq_t.cons_inv h
      have hb : Eq_t.Both Ξ Ξ' bind bind' := Eq_t.toBoth hΞ hbind
      have hb' : Eq_bd (Ξ' ⋈ bind') boundary boundary' :=
        Eq_bd.ofBoth (Eq_t.Both.concatenate hΞ hb) hboundary
      exact Eq_t.Both.cons hb hboundary hb'
        (Eq_t.toBoth (Eq_t.Both.concatenate hΞ
          (Eq_t.Both.cons hb hboundary hb' Eq_t.Both.nil)) hrest)

/-- 8(10): well-formedness of expressions is invariant under an equal ambient. -/
theorem Wf_e.ofEq {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t (.nil : Ambient 1) A B) {e : Expr Δ} : A ⊢ e → B ⊢ e :=
  Wf_e.ofBoth (Eq_t.toBoth Eq_t.Both.nil h)

/-- 8(10): equality of expressions is invariant under an equal ambient. -/
theorem Eq_e.ofEq {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t (.nil : Ambient 1) A B) {e e' : Expr Δ} : A ⊢ e ≈ e' → B ⊢ e ≈ e' :=
  Eq_e.ofBoth (Eq_t.toBoth Eq_t.Both.nil h)

/-- 8(10): equality of boundaries is invariant under an equal ambient. -/
theorem Eq_bd.ofEq {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t (.nil : Ambient 1) A B) {β β' : Bd Δ} : A ⊢ β ≈ β' → B ⊢ β ≈ β' :=
  Eq_bd.ofBoth (Eq_t.toBoth Eq_t.Both.nil h)

/-- 8(10): a well-formed telescope is invariant under an equal ambient. -/
theorem Wf_t.ofEq {Δ Ω : C.Arity} {A B : Ambient Δ}
    (h : Eq_t (.nil : Ambient 1) A B) {T : dTel Δ Ω} : Wf_t A T → Wf_t B T :=
  Wf_t.ofBoth (Eq_t.toBoth Eq_t.Both.nil h)

/-- 8(10): filling is invariant under an equal ambient and an equal telescope. -/
theorem Wf_s.ofEq {Δ Ω : C.Arity} {A B : Ambient Δ}
    (h : Eq_t (.nil : Ambient 1) A B) {T T' : dTel Δ Ω} {τ : Subst Ω Δ}
    (hτ : A ⊢ τ : T) (hT : Eq_t A T T') : B ⊢ τ : T' :=
  Wf_s.ofBoth (Eq_t.toBoth Eq_t.Both.nil h) hτ
    (Eq_t.toBoth (Eq_t.toBoth Eq_t.Both.nil h) hT)

/-- Equality over both ambients is symmetric, swapping the ambients too. -/
theorem Eq_t.Both.symm {Δ : C.Arity} {A B : Ambient Δ} :
    ∀ {Ω : C.Arity} {T T' : dTel Δ Ω},
      Eq_t.Both A B T T' → Eq_t.Both B A T' T
  | _, .nil, _, h => by
      obtain rfl := Eq_t.Both.nil_inv h
      exact Eq_t.Both.nil
  | _, .cons _ _ _, _, h => by
      obtain ⟨_, _, _, rfl, hbind, hboundary, hboundary', hrest⟩ :=
        Eq_t.Both.cons_inv h
      exact Eq_t.Both.cons hbind.symm hboundary'.symm hboundary.symm hrest.symm

/-- A substitution from a well-formed ambient is invariant under replacing its
target by an equal ambient. -/
theorem Wf_sub.ofBoth {Γ Δ : C.Arity} {A : Ambient Γ} {B B' : Ambient Δ}
    {σ : Subst Γ Δ} (hA : Ambient.Wf A)
    (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) B B')
    (hσ : Wf_sub A B σ) : Wf_sub A B' σ := by
  intro α x
  have hT : Wf_t B (σ ⋆ A.binding x) :=
    Wf_t.subst_ambient hσ (Wf_t.binding hA x)
  have hext := Eq_t.Both.concatenate h (Eq_t.Both.refl h hT)
  refine ⟨?_, ?_, ?_⟩
  · intro l r hlr
    exact Eq_e.ofBoth hext ((hσ x).1 l r hlr)
  · intro hne
    exact Wf_e.ofBoth hext ((hσ x).2.1 hne)
  · intro hne
    exact (boundaryOf_ofBoth hext ((hσ x).2.1 hne)).trans
      (Eq_bd.ofBoth hext ((hσ x).2.2 hne))

/-- 8(9): agreeing substitutions between well-formed ambients send a
well-formed telescope to equal telescopes. -/
theorem Eq_t.agree {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    {σ θ : Subst Γ Γ'} (hA : Ambient.Wf A) (hA' : Ambient.Wf A')
    (hσ : Wf_sub A A' σ) (hθ : Wf_sub A A' θ) (hst : Eq_sub A A' σ θ) :
    ∀ {Χ : C.Arity} {T : dTel Γ Χ}, Wf_t A T → Eq_t A' (σ ⋆ T) (θ ⋆ T)
  | _, _, .nil => Eq_t.nil
  | _, _, .cons (α := α) (bind := bind) (boundary := boundary)
      hbind hboundary hrest => by
      have hbase := Eq_t.Both.refl Eq_t.Both.nil hA'
      have hb := Eq_t.agree hA hA' hσ hθ hst hbind
      have hamb := Eq_t.Both.concatenate hbase (Eq_t.toBoth hbase hb)
      have hθbind := Wf_sub.ofBoth (Wf_t.concatenate hA hbind) hamb.symm
        (Wf_sub.lift hθ hbind)
      have hβ : Eq_bd (A' ⋈ σ ⋆ bind)
          (Bd.applyAt σ α boundary) (Bd.applyAt θ α boundary) :=
        Eq.mp (congrArg₂ (Eq_bd (A' ⋈ σ ⋆ bind))
          (Bd.act_lift_depth σ boundary) (Bd.act_lift_depth θ boundary))
          (Eq_bd.agree (Wf_t.concatenate hA hbind) (Wf_sub.lift hσ hbind)
            hθbind (Eq_sub.lift hσ hbind hst) (Wf_bd.refl hboundary))
      have hhead : Wf_t A (dTel.cons bind boundary .nil) :=
        .cons hbind hboundary .nil
      have heqhead := Eq_t.cons hb hβ Eq_t.nil
      have hambhead := Eq_t.Both.concatenate hbase (Eq_t.toBoth hbase heqhead)
      have hθhead := Wf_sub.ofBoth (Wf_t.concatenate hA hhead) hambhead.symm
        (Wf_sub.lift hθ hhead)
      exact Eq_t.cons hb hβ
        (Eq_t.agree (Wf_t.concatenate hA hhead)
          (Wf_t.concatenate hA' (Wf_t.subst_ambient hσ hhead))
          (Wf_sub.lift hσ hhead) hθhead (Eq_sub.lift hσ hhead hst) hrest)
