import HigherRankSyntax.Typing.SubstitutionLemma

/-!
# Invariance under an equal ambient

Each judgement over an ambient `A` carries over to every ambient `B` with
`Eq_t.Both .nil .nil A B`, which follows from `Eq_t .nil A B`: for a declaration
provided its bound entries are well formed over `A`, for an agreement of
fillings provided the first filling fills the telescope, and for an equality of
telescopes provided the first is well formed over `A`.  For fillings and
agreements the telescope may moreover be replaced by an equal one.  Well-formed
agreeing substitutions between well-formed ambients send a well-formed telescope
to equal telescopes.
-/

/-- Of two equal boundaries, one is an equation exactly when the other is. -/
theorem Eq_bd.isEq {Δ : C.Arity} {Ξ : Ambient Δ} :
  ∀ {β β' : Bd Δ}, Eq_bd Ξ β β' → (β.isEq ↔ β'.isEq)
  | _, _, .sort => Iff.rfl
  | _, _, .of _ => Iff.rfl
  | _, _, .eq _ _ => Iff.rfl

mutual

/-- If `Eq_t.Both .nil .nil A B`, an expression well formed over `A` is well
formed over `B`. -/
theorem Wf_e.ofBoth
    {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) A B) :
  ∀ {e : Expr Δ}, A ⊢ e → B ⊢ e
  | _, .ap x _ head fill => by
      apply Wf_e.ap
      · rwa [← Eq_bd.isEq (h.toEq_t.declaration x)]
      · apply Wf_s.ofBoth h fill (h.binding x)

/-- If `Eq_t.Both .nil .nil A B` and `e` is well formed over `A`, the computed
boundaries of `e` over `B` and over `A` are equal over `B`. -/
theorem boundaryOf_ofBoth
    {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) A B) :
  ∀ {e : Expr Δ}, A ⊢ e → Eq_bd B (B.boundaryOf e) (A.boundaryOf e)
  | _, .ap x _ _ fill => by
      apply Eq_bd.instantiate (Wf_s.ofBoth h fill (h.binding x))
      apply Eq_bd.symm (h.declaration_right x)

/-- If `Eq_t.Both .nil .nil A B`, expressions equal over `A` are equal over `B`. -/
theorem Eq_e.ofBoth
    {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) A B) :
  ∀ {e e' : Expr Δ}, A ⊢ e ≈ e' → B ⊢ e ≈ e'
  | _, _, .refl he => .refl (Wf_e.ofBoth h he)
  | _, _, .symm he => .symm (Eq_e.ofBoth h he)
  | _, _, .trans he he' => .trans (Eq_e.ofBoth h he) (Eq_e.ofBoth h he')
  | _, _, .hyp q _ _ args decl _ _ fill => by
      have hfill := Wf_s.ofBoth h fill (h.binding q)
      have hdecl := h.declaration_right q
      rw [decl] at hdecl
      obtain ⟨_, _, hdecl, hl, hr⟩ := Eq_bd.eq_inv hdecl
      apply Eq_e.trans (Eq_e.instantiate hfill hl)
      apply Eq_e.trans _ (Eq_e.symm (Eq_e.instantiate hfill hr))
      apply Eq_e.hyp q _ _ args hdecl (Eq_e.wf_right hl) (Eq_e.wf_right hr) hfill
  | _, _, .congr σ θ hΘ hσ hθ agree he => by
      have hΘ' := Eq_t.Both.refl h hΘ
      apply Eq_e.congr σ θ (Wf_t.ofBoth h hΘ) (Wf_s.ofBoth h hσ hΘ') (Wf_s.ofBoth h hθ hΘ')
        (Eq_s.ofBoth h agree hΘ' hσ (Wf_s.ofBoth h hσ hΘ'))
        (Eq_e.ofBoth (Eq_t.Both.concatenate h hΘ') he)

/-- If `Eq_t.Both .nil .nil A B`, boundaries equal over `A` are equal over `B`. -/
theorem Eq_bd.ofBoth
    {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) A B) :
  ∀ {β β' : Bd Δ}, A ⊢ β ≈ β' → B ⊢ β ≈ β'
  | _, _, .sort => .sort
  | _, _, .of he => .of (Eq_e.ofBoth h he)
  | _, _, .eq hl hr => .eq (Eq_e.ofBoth h hl) (Eq_e.ofBoth h hr)

/-- If `Eq_t.Both .nil .nil A B`, `τ` fills `T` over `A`, and `T` and `T'` are
equal over `A` and `B`, then `τ` fills `T'` over `B`. -/
theorem Wf_s.ofBoth
    {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) A B) :
  ∀ {Ω : C.Arity} {T T' : dTel Δ Ω} {τ : Subst Ω Δ},
    A ⊢ τ : T → Eq_t.Both A B T T' → B ⊢ τ : T'
  | _, _, _, _, .nil, hT => by
      obtain rfl := Eq_t.Both.nil_inv hT
      apply Wf_s.nil
  | _, _, _, _, .cons (α := α) (σ := τ) (bind := bind) (boundary := boundary)
      equation filler declared hrest, hT => by
      obtain ⟨bind', boundary', _, rfl, hbind, _, hboundary, hrest'⟩ :=
        Eq_t.Both.cons_inv hT
      have hamb := Eq_t.Both.concatenate h hbind
      have hisEq := Eq_bd.isEq hboundary
      have hequation : ∀ l r : Expr (Δ ⋈ α), boundary' = .eq l r →
          Eq_e (B ⋈ bind') l r := by
        rintro l r rfl
        obtain ⟨l₀, r₀, hβ, hl, hr⟩ := Eq_bd.eq_inv (Eq_bd.symm hboundary)
        apply Eq_e.trans hl
        apply Eq_e.trans (Eq_e.ofBoth hamb (equation l₀ r₀ hβ)) (Eq_e.symm hr)
      have hfiller : ¬ boundary'.isEq →
          Wf_e (B ⋈ bind') (τ (C.inl (C.singleSlot α))) := by
        rw [← hisEq]
        intro hne
        apply Wf_e.ofBoth hamb (filler hne)
      have hdeclared : ¬ boundary'.isEq →
          Eq_bd (B ⋈ bind')
            ((B ⋈ bind').boundaryOf (τ (C.inl (C.singleSlot α)))) boundary' := by
        rw [← hisEq]
        intro hne
        apply Eq_bd.trans (boundaryOf_ofBoth hamb (filler hne))
        apply Eq_bd.trans (Eq_bd.ofBoth hamb (declared hne)) hboundary
      have hhead : Wf_s A (dTel.cons bind boundary .nil)
          (fun ⦃β⦄ (i : C.single α ∋ β) => τ (C.inl i)) :=
        Wf_s.cons equation filler declared .nil
      have hhead' : Wf_s B (dTel.cons bind' boundary' .nil)
          (fun ⦃β⦄ (i : C.single α ∋ β) => τ (C.inl i)) :=
        Wf_s.cons hequation hfiller hdeclared .nil
      apply Wf_s.cons hequation hfiller hdeclared
      apply Wf_s.ofBoth h hrest
      apply Eq_t.Both.filling (Wf_s.filling hhead) (Wf_s.filling hhead') rfl hrest'

/-- If `Eq_t.Both .nil .nil A B`, `σ` and `θ` agree as fillings of `T` over `A`,
`T` and `T'` are equal over `A` and `B`, and `σ` fills `T` over `A` and `T'` over
`B`, then `σ` and `θ` agree as fillings of `T'` over `B`. -/
theorem Eq_s.ofBoth
    {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) A B) :
  ∀ {Ω : C.Arity} {T T' : dTel Δ Ω} {σ θ : Subst Ω Δ},
    A ⊢ σ ≈ θ : T → Eq_t.Both A B T T' → A ⊢ σ : T → B ⊢ σ : T' →
      B ⊢ σ ≈ θ : T'
  | _, _, _, _, _, .nil, hT, _, _ => by
      obtain rfl := Eq_t.Both.nil_inv hT
      apply Eq_s.nil
  | _, _, _, _, _, .cons slot hrest, hT, hσ, hσ' => by
      obtain ⟨_, _, _, rfl, hbind, _, hboundary, hrest'⟩ := Eq_t.Both.cons_inv hT
      apply Eq_s.cons
      · rw [← Eq_bd.isEq hboundary]
        intro hne
        apply Eq_e.ofBoth (Eq_t.Both.concatenate h hbind) (slot hne)
      · apply Eq_s.ofBoth h hrest _ hσ.tail hσ'.tail
        apply Eq_t.Both.filling (Wf_s.filling hσ.head) (Wf_s.filling hσ'.head) rfl hrest'

/-- If `Eq_t.Both .nil .nil A B` and `T` is equal to itself over `A` and `B`, a
declaration well formed over `A` with bound entries `T` is well formed over `B`
with bound entries `T`. -/
theorem Wf_bd.ofBoth
    {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) A B) :
  ∀ {Ω : C.Arity} {T : dTel Δ Ω} {β : Bd (Δ ⋈ Ω)},
    Eq_t.Both A B T T → Wf_bd A T β → Wf_bd B T β
  | _, _, _, _, .sort => .sort
  | _, _, _, hT, .of hS hsort => by
      have hamb := Eq_t.Both.concatenate h hT
      apply Wf_bd.of (Wf_e.ofBoth hamb hS)
      apply Eq_bd.trans (boundaryOf_ofBoth hamb hS) (Eq_bd.ofBoth hamb hsort)
  | _, _, _, hT, .eq hl hr heq => by
      have hamb := Eq_t.Both.concatenate h hT
      apply Wf_bd.eq (Wf_e.ofBoth hamb hl) (Wf_e.ofBoth hamb hr)
      apply Eq_bd.trans (boundaryOf_ofBoth hamb hl)
      apply Eq_bd.trans (Eq_bd.ofBoth hamb heq) (Eq_bd.symm (boundaryOf_ofBoth hamb hr))

/-- If `Eq_t.Both .nil .nil A B`, a telescope well formed over `A` is equal to
itself over `A` and `B`. -/
theorem Eq_t.Both.refl
    {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) A B) :
  ∀ {Ω : C.Arity} {T : dTel Δ Ω}, Wf_t A T → Eq_t.Both A B T T
  | _, _, .nil => Eq_t.Both.nil
  | _, _, .cons hbind hboundary hrest => by
      have hb := Eq_t.Both.refl h hbind
      have hhead := Eq_t.Both.cons hb (Wf_bd.refl hboundary)
        (Wf_bd.refl (Wf_bd.ofBoth h hb hboundary)) Eq_t.Both.nil
      apply Eq_t.Both.concatenate hhead
      apply Eq_t.Both.refl (Eq_t.Both.concatenate h hhead) hrest

/-- If `Eq_t.Both .nil .nil A B`, a telescope well formed over `A` is well formed
over `B`. -/
theorem Wf_t.ofBoth
    {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) A B) :
  ∀ {Ω : C.Arity} {T : dTel Δ Ω}, Wf_t A T → Wf_t B T
  | _, _, .nil => .nil
  | _, _, .cons hbind hboundary hrest => by
      have hb := Eq_t.Both.refl h hbind
      have hhead := Eq_t.Both.cons hb (Wf_bd.refl hboundary)
        (Wf_bd.refl (Wf_bd.ofBoth h hb hboundary)) Eq_t.Both.nil
      apply Wf_t.cons (Wf_t.ofBoth h hbind) (Wf_bd.ofBoth h hb hboundary)
      apply Wf_t.ofBoth (Eq_t.Both.concatenate h hhead) hrest

end

/-- If `Eq_t.Both .nil .nil Ξ Ξ'`, telescopes equal over `Ξ` are equal over `Ξ`
and `Ξ'`. -/
theorem Eq_t.toBoth
    {Δ : C.Arity} {Ξ Ξ' : Ambient Δ}
    (hΞ : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) Ξ Ξ') :
  ∀ {Ω : C.Arity} {Θ Θ' : dTel Δ Ω}, Eq_t Ξ Θ Θ' → Eq_t.Both Ξ Ξ' Θ Θ'
  | _, .nil, _, h => by
      obtain rfl := Eq_t.nil_inv h
      apply Eq_t.Both.nil
  | _, .cons _ _ _, _, h => by
      obtain ⟨_, _, _, rfl, hbind, hboundary, hrest⟩ := Eq_t.cons_inv h
      have hb := Eq_t.toBoth hΞ hbind
      have hhead := Eq_t.Both.cons hb hboundary
        (Eq_bd.ofBoth (Eq_t.Both.concatenate hΞ hb) hboundary) Eq_t.Both.nil
      apply Eq_t.Both.concatenate hhead
      apply Eq_t.toBoth (Eq_t.Both.concatenate hΞ hhead) hrest

/-- If `Eq_t .nil A B`, an expression well formed over `A` is well formed over
`B`. -/
theorem Wf_e.ofEq
    {Δ : C.Arity} {A B : Ambient Δ} (h : Eq_t (.nil : Ambient 1) A B) {e : Expr Δ} :
  A ⊢ e → B ⊢ e
  := Wf_e.ofBoth (Eq_t.toBoth Eq_t.Both.nil h)

/-- If `Eq_t .nil A B`, boundaries equal over `A` are equal over `B`. -/
theorem Eq_bd.ofEq
    {Δ : C.Arity} {A B : Ambient Δ} (h : Eq_t (.nil : Ambient 1) A B) {β β' : Bd Δ} :
  A ⊢ β ≈ β' → B ⊢ β ≈ β'
  := Eq_bd.ofBoth (Eq_t.toBoth Eq_t.Both.nil h)

/-- If `Eq_t .nil A B` and `e` is well formed over `A`, the computed boundaries
of `e` over `B` and over `A` are equal over `B`. -/
theorem boundaryOf_ofEq
    {Δ : C.Arity} {A B : Ambient Δ} (h : Eq_t (.nil : Ambient 1) A B) {e : Expr Δ} :
  A ⊢ e → Eq_bd B (B.boundaryOf e) (A.boundaryOf e)
  := boundaryOf_ofBoth (Eq_t.toBoth Eq_t.Both.nil h)

/-- If `Eq_t .nil A B`, a telescope well formed over `A` is well formed over
`B`. -/
theorem Wf_t.ofEq
    {Δ Ω : C.Arity} {A B : Ambient Δ} (h : Eq_t (.nil : Ambient 1) A B) {T : dTel Δ Ω} :
  Wf_t A T → Wf_t B T
  := Wf_t.ofBoth (Eq_t.toBoth Eq_t.Both.nil h)

/-- If `Eq_t .nil A B`, `τ` fills `T` over `A`, and `T` and `T'` are equal over
`A`, then `τ` fills `T'` over `B`. -/
theorem Wf_s.ofEq
    {Δ Ω : C.Arity} {A B : Ambient Δ} (h : Eq_t (.nil : Ambient 1) A B)
    {T T' : dTel Δ Ω} {τ : Subst Ω Δ} (hτ : A ⊢ τ : T) (hT : Eq_t A T T') :
  B ⊢ τ : T'
  := by
  have hAB := Eq_t.toBoth Eq_t.Both.nil h
  apply Wf_s.ofBoth hAB hτ (Eq_t.toBoth hAB hT)

/-- Equality of telescopes over two ambients is symmetric, swapping the
ambients. -/
theorem Eq_t.Both.symm {Δ : C.Arity} {A B : Ambient Δ} :
  ∀ {Ω : C.Arity} {T T' : dTel Δ Ω}, Eq_t.Both A B T T' → Eq_t.Both B A T' T
  | _, .nil, _, h => by
      obtain rfl := Eq_t.Both.nil_inv h
      apply Eq_t.Both.nil
  | _, .cons _ _ _, _, h => by
      obtain ⟨_, _, _, rfl, hbind, hboundary, hboundary', hrest⟩ := Eq_t.Both.cons_inv h
      apply Eq_t.Both.cons hbind.symm hboundary'.symm hboundary.symm hrest.symm

/-- If `A` is well formed and `Eq_t.Both .nil .nil B B'`, a well-formed
substitution from `A` to `B` is a well-formed substitution from `A` to `B'`. -/
theorem Wf_sub.ofBoth
    {Γ Δ : C.Arity} {A : Ambient Γ} {B B' : Ambient Δ} {σ : Subst Γ Δ}
    (hA : Ambient.Wf A) (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) B B')
    (hσ : Wf_sub A B σ) :
  Wf_sub A B' σ
  := by
  intro α x
  obtain ⟨hequation, hfiller, hdeclared⟩ := hσ x
  have hext := Eq_t.Both.concatenate h
    (Eq_t.Both.refl h (Wf_t.subst_ambient hσ (Wf_t.binding hA x)))
  and_intros
  · intro l r hlr
    apply Eq_e.ofBoth hext (hequation l r hlr)
  · intro hne
    apply Wf_e.ofBoth hext (hfiller hne)
  · intro hne
    apply Eq_bd.trans (boundaryOf_ofBoth hext (hfiller hne))
    apply Eq_bd.ofBoth hext (hdeclared hne)

/-- If `σ` and `θ` are well-formed agreeing substitutions from a well-formed `A`
to a well-formed `A'`, then `σ ⋆ T` and `θ ⋆ T` are equal over `A'` for every `T`
well formed over `A`. -/
theorem Eq_t.agree
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'} {σ θ : Subst Γ Γ'}
    (hA : Ambient.Wf A) (hA' : Ambient.Wf A')
    (hσ : Wf_sub A A' σ) (hθ : Wf_sub A A' θ) (hst : Eq_sub A A' σ θ) :
  ∀ {Χ : C.Arity} {T : dTel Γ Χ}, Wf_t A T → Eq_t A' (σ ⋆ T) (θ ⋆ T)
  | _, _, .nil => Eq_t.nil
  | _, _, .cons (α := α) (bind := bind) (boundary := boundary)
      hbind hboundary hrest => by
      have hbase := Eq_t.Both.refl Eq_t.Both.nil hA'
      have hb := Eq_t.agree hA hA' hσ hθ hst hbind
      have hamb := Eq_t.Both.concatenate hbase (Eq_t.toBoth hbase hb)
      have hθbind := Wf_sub.ofBoth (Wf_t.concatenate hA hbind) hamb.symm (Wf_sub.lift hθ hbind)
      have hβ : Eq_bd (A' ⋈ σ ⋆ bind)
          (Bd.applyAt σ α boundary) (Bd.applyAt θ α boundary) := by
        convert Eq_bd.agree (Wf_t.concatenate hA hbind) (Wf_sub.lift hσ hbind) hθbind
          (Eq_sub.lift hσ hbind hst) (Wf_bd.refl hboundary) using 1
        · symm
          apply Bd.act_lift_depth
        · symm
          apply Bd.act_lift_depth
      have hhead := Wf_t.cons hbind hboundary .nil
      have hambhead := Eq_t.Both.concatenate hbase (Eq_t.toBoth hbase (Eq_t.cons hb hβ Eq_t.nil))
      have hθhead := Wf_sub.ofBoth (Wf_t.concatenate hA hhead) hambhead.symm
        (Wf_sub.lift hθ hhead)
      apply Eq_t.cons hb hβ
      apply Eq_t.agree (Wf_t.concatenate hA hhead)
        (Wf_t.concatenate hA' (Wf_t.subst_ambient hσ hhead)) (Wf_sub.lift hσ hhead) hθhead
        (Eq_sub.lift hσ hhead hst) hrest

/-- If `Eq_t.Both .nil .nil A B` and `T` is well formed over `A`, then `T` and a
telescope equal to it over `A` are equal over `B`. -/
theorem Eq_t.ofBoth
    {Δ : C.Arity} {A B : Ambient Δ}
    (h : Eq_t.Both (.nil : Ambient 1) (.nil : Ambient 1) A B) :
  ∀ {Ω : C.Arity} {T T' : dTel Δ Ω}, Wf_t A T → Eq_t A T T' → Eq_t B T T'
  | _, _, _, .nil, hT => by
      obtain rfl := Eq_t.nil_inv hT
      apply Eq_t.nil
  | _, _, _, .cons hbind hboundary hrest, hT => by
      obtain ⟨_, _, _, rfl, hbind', hboundary', hrest'⟩ := Eq_t.cons_inv hT
      apply Eq_t.cons (Eq_t.ofBoth h hbind hbind')
      · apply Eq_bd.ofBoth (Eq_t.Both.concatenate h (Eq_t.Both.refl h hbind)) hboundary'
      · apply Eq_t.ofBoth
          (Eq_t.Both.concatenate h (Eq_t.Both.refl h (Wf_t.cons hbind hboundary .nil)))
          hrest hrest'

/-- If `Eq_t .nil A B` and `T` is well formed over `A`, then `T` and a telescope
equal to it over `A` are equal over `B`. -/
theorem Eq_t.ofEq
    {Δ Ω : C.Arity} {A B : Ambient Δ} (h : Eq_t (.nil : Ambient 1) A B)
    {T T' : dTel Δ Ω} (hT : Wf_t A T) :
  Eq_t A T T' → Eq_t B T T'
  := Eq_t.ofBoth (Eq_t.toBoth Eq_t.Both.nil h) hT
