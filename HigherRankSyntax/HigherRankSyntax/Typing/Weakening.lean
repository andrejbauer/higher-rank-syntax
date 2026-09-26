import HigherRankSyntax.Typing.Rules

/-!
# Weakening

A renaming of ambients `A → A'` is a renaming of slots under which the
declaration and the bound entries of the image of a slot are the renamed
declaration and bound entries of the slot.  A renaming of ambients carries every
judgement over `A` to the renamed judgement over `A'`.  The inclusion of `Ξ` into
`Ξ ⋈ Θ` is a renaming of ambients, and renamings of ambients extend along
telescopes.  Consequently the declaration and the bound entries of every slot of
a well-formed telescope are well formed, and the declarations of equal
telescopes are equal, as are the declarations and the bound entries of
telescopes equal over two ambients.  Equality of telescopes, over one ambient or
over two, is preserved by concatenation.
-/

/-! ## Renamings of ambients -/

/-- A renaming of ambients `A → A'`: a renaming of slots under which the
declaration and the bound entries of the image of each slot are the renamed
declaration and bound entries of the slot. -/
structure Ambient.Renaming {Γ Γ' : C.Arity} (A : Ambient Γ) (A' : Ambient Γ') where
  slot : Γ →ʳ Γ'
  declaration : ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α),
    A'.declaration (slot x) = Bd.rename (slot ⇑ʳ α) (A.declaration x)
  binding : ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α),
    A'.binding (slot x) = dTel.rename slot (A.binding x)

namespace Ambient.Renaming

/-- The declaration of the image of a slot under a renaming of ambients is an
equation exactly when the declaration of the slot is. -/
theorem isEq
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') {α : C.Arity} (x : Γ ∋ α) :
  (A'.declaration (ι.slot x)).isEq ↔ (A.declaration x).isEq
  := by
  rw [ι.declaration x]
  apply Bd.isEq_rename

/-- The inclusion of an ambient `Ξ` into `Ξ ⋈ Θ` is a renaming of ambients. -/
def weaken {Δ Ω : C.Arity} (Ξ : Ambient Δ) (Θ : dTel Δ Ω) :
    Ambient.Renaming Ξ (Ξ ⋈ Θ) where
  slot := Renaming.inl Δ Ω
  declaration := fun ⦃_⦄ x => dTel.declaration_concatenate_inl Ξ Θ x
  binding := fun ⦃_⦄ x => dTel.binding_concatenate_inl Ξ Θ x

/-- The inclusion `Renaming.inr` of `A` into
`A' ⋈ dTel.rename (Renaming.fromUnit Γ') A` is a renaming of ambients. -/
def weakenInto {Γ Γ' : C.Arity} (A : Ambient Γ) (A' : Ambient Γ') :
    Ambient.Renaming A (A' ⋈ dTel.rename (Renaming.fromUnit Γ') A) where
  slot := Renaming.inr Γ' Γ
  declaration := by
    intro α x
    apply Eq.trans (dTel.declaration_concatenate_inr _ _ x)
    rw [dTel.declaration_rename]
    congr 2
    apply Renaming.fromUnit_extend
  binding := by
    intro α x
    apply Eq.trans (dTel.binding_concatenate_inr _ _ x)
    rw [dTel.binding_rename]
    congr 1
    apply Renaming.fromUnit_extend

/-- The renaming of slots out of the empty ambient is a renaming of ambients into
every ambient. -/
def fromEmpty {Δ : C.Arity} (Ξ : Ambient Δ) :
    Ambient.Renaming (.nil : Ambient 1) Ξ where
  slot := Renaming.fromUnit Δ
  declaration := fun ⦃_⦄ x => (C.unit_is_empty x).elim
  binding := fun ⦃_⦄ x => (C.unit_is_empty x).elim

/-- A renaming of ambients `ι : A → A'` extends to
`A ⋈ Θ → A' ⋈ dTel.rename ι.slot Θ`, fixing the slots of `Θ`. -/
def extend {Γ Γ' Ω : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') (Θ : dTel Γ Ω) :
    Ambient.Renaming (A ⋈ Θ) (A' ⋈ dTel.rename ι.slot Θ) where
  slot := ι.slot ⇑ʳ Ω
  declaration := by
    intro α x
    rcases C.cover Γ Ω x with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · rw [Renaming.extend_inl, dTel.declaration_concatenate_inl,
        dTel.declaration_concatenate_inl, ι.declaration]
      calc _
          = Bd.rename ((Renaming.inl Γ' Ω ∘ʳ ι.slot) ⇑ʳ α) (A.declaration y) := by
            rw [Renaming.extend_comp, Bd.rename_comp]
            rfl
        _ = _ := by
            rw [Renaming.inl_comp, Renaming.extend_comp, Bd.rename_comp]
            rfl
    · rw [Renaming.extend_inr, dTel.declaration_concatenate_inr,
        dTel.declaration_concatenate_inr, dTel.declaration_rename]
      rfl
  binding := by
    intro α x
    rcases C.cover Γ Ω x with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · rw [Renaming.extend_inl, dTel.binding_concatenate_inl,
        dTel.binding_concatenate_inl, ι.binding]
      calc _
          = dTel.rename (Renaming.inl Γ' Ω ∘ʳ ι.slot) (A.binding y) := by
            rw [dTel.rename_comp]
            rfl
        _ = _ := by
            rw [Renaming.inl_comp, dTel.rename_comp]
            rfl
    · rw [Renaming.extend_inr, dTel.binding_concatenate_inr,
        dTel.binding_concatenate_inr, dTel.binding_rename]
      rfl

/-- The computed boundary of a renamed expression is the renamed computed
boundary. -/
theorem boundaryOf
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') :
  ∀ e : Expr Γ, A'.boundaryOf (⟦ ι.slot ⟧ʳ e) = Bd.rename ι.slot (A.boundaryOf e)
  | .ap x args => by
      rw [Renaming.act_ap, dTel.boundaryOf_ap, dTel.boundaryOf_ap, ι.declaration x]
      simpa only [Renaming.extend_unit] using Bd.act_rename (Φ := 1) ι.slot args (A.declaration x)

end Ambient.Renaming

/-! ## Stability of the judgements -/

mutual

/-- Well-formedness of expressions is stable under a renaming of ambients. -/
theorem Wf_e.weaken
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') :
  ∀ {e : Expr Γ}, Wf_e A e → Wf_e A' (⟦ ι.slot ⟧ʳ e)
  | _, .ap x _ head fill => by
      apply Wf_e.ap
      · rwa [ι.isEq x]
      · rw [ι.binding x]
        apply Wf_s.weaken ι fill

/-- Equality of expressions is stable under a renaming of ambients. -/
theorem Eq_e.weaken
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') :
  ∀ {e e' : Expr Γ}, Eq_e A e e' → Eq_e A' (⟦ ι.slot ⟧ʳ e) (⟦ ι.slot ⟧ʳ e')
  | _, _, .refl h => .refl (Wf_e.weaken ι h)
  | _, _, .symm h => .symm (Eq_e.weaken ι h)
  | _, _, .trans h h' => .trans (Eq_e.weaken ι h) (Eq_e.weaken ι h')
  | _, _, .hyp q _ _ _ decl hl hr fill => by
      rw [← act_rename, ← act_rename]
      apply Eq_e.hyp (ι.slot q)
      · rw [ι.declaration q, decl]
        rfl
      · rw [ι.binding q]
        apply Wf_e.weaken (ι.extend (A.binding q)) hl
      · rw [ι.binding q]
        apply Wf_e.weaken (ι.extend (A.binding q)) hr
      · rw [ι.binding q]
        apply Wf_s.weaken ι fill
  | _, _, .congr (Θ := Θ) _ _ hΘ hσ hθ agree h => by
      rw [← act_rename, ← act_rename]
      apply Eq_e.congr _ _ (Wf_t.weaken ι hΘ) (Wf_s.weaken ι hσ) (Wf_s.weaken ι hθ)
        (Eq_s.weaken ι agree) (Eq_e.weaken (ι.extend Θ) h)

/-- Equality of boundaries is stable under a renaming of ambients. -/
theorem Eq_bd.weaken
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') :
  ∀ {β β' : Bd Γ}, Eq_bd A β β' → Eq_bd A' (Bd.rename ι.slot β) (Bd.rename ι.slot β')
  | _, _, .sort => .sort
  | _, _, .of h => .of (Eq_e.weaken ι h)
  | _, _, .eq hl hr => .eq (Eq_e.weaken ι hl) (Eq_e.weaken ι hr)

/-- Filling is stable under a renaming of ambients. -/
theorem Wf_s.weaken
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') :
  ∀ {Ω : C.Arity} {Θ : dTel Γ Ω} {σ : Subst Ω Γ}, Wf_s A Θ σ →
    Wf_s A' (dTel.rename ι.slot Θ) (fun ⦃Λ⦄ i => ⟦ ι.slot ⇑ʳ Λ ⟧ʳ (σ i))
  | _, _, _, .nil => .nil
  | _, _, _, .cons (bind := bind) equation filler declared hrest => by
      apply Wf_s.cons
      · intro l r h
        obtain ⟨l₀, r₀, hβ, rfl, rfl⟩ := Bd.rename_eq_inv _ h
        apply Eq_e.weaken (ι.extend bind) (equation l₀ r₀ hβ)
      · rw [Bd.isEq_rename]
        intro hne
        apply Wf_e.weaken (ι.extend bind) (filler hne)
      · rw [Bd.isEq_rename]
        intro hne
        convert Eq_bd.weaken (ι.extend bind) (declared hne) using 2
        apply (ι.extend bind).boundaryOf
      · convert Wf_s.weaken ι hrest using 1
        apply dTel.instantiate_rename

/-- Agreement of fillings is stable under a renaming of ambients. -/
theorem Eq_s.weaken
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') :
  ∀ {Ω : C.Arity} {Θ : dTel Γ Ω} {σ θ : Subst Ω Γ}, Eq_s A Θ σ θ →
    Eq_s A' (dTel.rename ι.slot Θ) (fun ⦃Λ⦄ i => ⟦ ι.slot ⇑ʳ Λ ⟧ʳ (σ i))
      (fun ⦃Λ⦄ i => ⟦ ι.slot ⇑ʳ Λ ⟧ʳ (θ i))
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons (bind := bind) slot hrest => by
      apply Eq_s.cons
      · rw [Bd.isEq_rename]
        intro hne
        apply Eq_e.weaken (ι.extend bind) (slot hne)
      · convert Eq_s.weaken ι hrest using 1
        apply dTel.instantiate_rename

/-- A well-formed declaration stays well formed under a renaming of ambients. -/
theorem Wf_bd.weaken
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') {Λ : C.Arity} (Θ : dTel Γ Λ) :
  ∀ {β : Bd (Γ ⋈ Λ)}, Wf_bd A Θ β →
    Wf_bd A' (dTel.rename ι.slot Θ) (Bd.rename (ι.slot ⇑ʳ Λ) β)
  | _, .sort => .sort
  | _, .of hS hsort => by
      apply Wf_bd.of (Wf_e.weaken (ι.extend Θ) hS)
      convert Eq_bd.weaken (ι.extend Θ) hsort using 2
      apply (ι.extend Θ).boundaryOf
  | _, .eq hl hr heq => by
      apply Wf_bd.eq (Wf_e.weaken (ι.extend Θ) hl) (Wf_e.weaken (ι.extend Θ) hr)
      convert Eq_bd.weaken (ι.extend Θ) heq using 2 <;> apply (ι.extend Θ).boundaryOf

/-- A well-formed telescope stays well formed under a renaming of ambients. -/
theorem Wf_t.weaken
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') :
  ∀ {Ω : C.Arity} {Θ : dTel Γ Ω}, Wf_t A Θ → Wf_t A' (dTel.rename ι.slot Θ)
  | _, _, .nil => .nil
  | _, _, .cons (bind := bind) (boundary := boundary) hbind hboundary hrest =>
      .cons (Wf_t.weaken ι hbind) (Wf_bd.weaken ι bind hboundary)
        (Wf_t.weaken (ι.extend (dTel.cons bind boundary .nil)) hrest)

end

/-! ## Well-formed and equal telescopes -/

/-- A well-formed ambient, reindexed along `Renaming.fromUnit Δ`, is a
well-formed telescope over every `Ξ : Ambient Δ`. -/
theorem Ambient.Wf.weaken
    {Δ Ω : C.Arity} {A : Ambient Ω} (h : Ambient.Wf A) (Ξ : Ambient Δ) :
  Wf_t Ξ (dTel.rename (Renaming.fromUnit Δ) A)
  := Wf_t.weaken (Ambient.Renaming.fromEmpty Ξ) h

/-- The declaration of every slot `z` of a telescope `Θ` well formed over `Ξ` is
well formed over `Ξ ⋈ Θ` with bound entries `Θ.binding z`. -/
theorem Wf_t.declaration {Δ : C.Arity} {Ξ : Ambient Δ} :
  ∀ {Ω : C.Arity} {Θ : dTel Δ Ω}, Wf_t Ξ Θ → ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
    Wf_bd (Ξ ⋈ Θ) (Θ.binding z) (Θ.declaration z)
  | _, _, .nil, _, z => (C.unit_is_empty z).elim
  | _, _, .cons _ hboundary hrest, _, z => by
      induction z using slotCases with
      | head =>
        rw [dTel.binding_head, dTel.declaration_head]
        apply Wf_bd.weaken (Ambient.Renaming.weaken Ξ _) _ hboundary
      | tail y =>
        rw [dTel.binding_tail, dTel.declaration_tail]
        convert Wf_t.declaration hrest y using 1
        symm
        apply dTel.concatenate_assoc

/-- A declaration well formed over `Ξ` with bound entries `Θ` is equal to itself
over `Ξ ⋈ Θ`. -/
theorem Wf_bd.refl {Δ Λ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Λ} :
  ∀ {β : Bd (Δ ⋈ Λ)}, Wf_bd Ξ Θ β → Eq_bd (Ξ ⋈ Θ) β β
  | _, .sort => .sort
  | _, .of hS _ => .of (.refl hS)
  | _, .eq hl hr _ => .eq (.refl hl) (.refl hr)

/-- The entries bound by every slot of a telescope `Θ` well formed over `Ξ` are
well formed over `Ξ ⋈ Θ`. -/
theorem Wf_t.binding {Δ : C.Arity} {Ξ : Ambient Δ} :
  ∀ {Ω : C.Arity} {Θ : dTel Δ Ω}, Wf_t Ξ Θ → ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
    Wf_t (Ξ ⋈ Θ) (Θ.binding z)
  | _, _, .nil, _, z => (C.unit_is_empty z).elim
  | _, _, .cons hbind _ hrest, _, z => by
      induction z using slotCases with
      | head =>
        rw [dTel.binding_head]
        apply Wf_t.weaken (Ambient.Renaming.weaken Ξ _) hbind
      | tail y =>
        rw [dTel.binding_tail]
        convert Wf_t.binding hrest y using 1
        symm
        apply dTel.concatenate_assoc

/-- A well-formed telescope is equal to itself. -/
theorem Wf_t.refl {Δ : C.Arity} {Ξ : Ambient Δ} :
  ∀ {Ω : C.Arity} {Θ : dTel Δ Ω}, Wf_t Ξ Θ → Eq_t Ξ Θ Θ
  | _, _, .nil => .nil
  | _, _, .cons hbind hboundary hrest =>
      .cons (Wf_t.refl hbind) (Wf_bd.refl hboundary) (Wf_t.refl hrest)

/-- Equality of telescopes is stable under a renaming of ambients. -/
theorem Eq_t.weaken
    {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') :
  ∀ {Ω : C.Arity} {Θ Θ' : dTel Γ Ω}, Eq_t A Θ Θ' →
    Eq_t A' (dTel.rename ι.slot Θ) (dTel.rename ι.slot Θ')
  | _, .nil, _, h => by
      obtain rfl := Eq_t.nil_inv h
      apply Eq_t.nil
  | _, .cons bind boundary _, _, h => by
      obtain ⟨_, _, _, rfl, hbind, hboundary, hrest⟩ := Eq_t.cons_inv h
      apply Eq_t.cons (Eq_t.weaken ι hbind) (Eq_bd.weaken (ι.extend bind) hboundary)
      apply Eq_t.weaken (ι.extend (dTel.cons bind boundary .nil)) hrest

/-- If `Θ` and `Θ'` are equal over `Ξ`, and `X` and `X'` over `Ξ ⋈ Θ`, then
`Θ ⋈ X` and `Θ' ⋈ X'` are equal over `Ξ`. -/
theorem Eq_t.concatenate {Δ : C.Arity} {Ξ : Ambient Δ} :
  ∀ {Ω Φ : C.Arity} {Θ Θ' : dTel Δ Ω} {X X' : dTel (Δ ⋈ Ω) Φ},
    Eq_t Ξ Θ Θ' → Eq_t (Ξ ⋈ Θ) X X' →
      Eq_t Ξ (dTel.concatenate Θ X) (dTel.concatenate Θ' X')
  | _, _, .nil, _, _, _, h, hX => by
      obtain rfl := Eq_t.nil_inv h
      convert hX using 1
      symm
      apply dTel.concatenate_nil
  | _, _, .cons _ _ _, _, _, _, h, hX => by
      obtain ⟨_, _, _, rfl, hbind, hboundary, hrest⟩ := Eq_t.cons_inv h
      apply Eq_t.cons hbind hboundary
      apply Eq_t.concatenate hrest
      rwa [dTel.concatenate_assoc]

/-- If `Θ` and `Θ'` are equal over `Ξ`, their declarations at every slot `z` are
equal over `Ξ ⋈ Θ ⋈ Θ.binding z`. -/
theorem Eq_t.declaration {Δ : C.Arity} {Ξ : Ambient Δ} :
  ∀ {Ω : C.Arity} {Θ Θ' : dTel Δ Ω}, Eq_t Ξ Θ Θ' →
    ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
      Eq_bd (Ξ ⋈ Θ ⋈ Θ.binding z) (Θ.declaration z) (Θ'.declaration z)
  | _, .nil, _, _, _, z => (C.unit_is_empty z).elim
  | _, .cons bind _ _, _, h, _, z => by
      obtain ⟨_, _, _, rfl, _, hboundary, hrest⟩ := Eq_t.cons_inv h
      induction z using slotCases with
      | head =>
        rw [dTel.declaration_head, dTel.declaration_head, dTel.binding_head]
        apply Eq_bd.weaken ((Ambient.Renaming.weaken Ξ _).extend bind) hboundary
      | tail y =>
        rw [dTel.declaration_tail, dTel.declaration_tail, dTel.binding_tail]
        convert Eq_t.declaration hrest y using 2
        symm
        apply dTel.concatenate_assoc

/-! ### Telescopes equal over two ambients -/

/-- Renamings of ambients `A → A'` and `A₁ → A₁'` with the same renaming of
slots carry telescopes equal over `A` and `A₁` to telescopes equal over `A'` and
`A₁'`. -/
theorem Eq_t.Both.weaken
    {Γ Γ' : C.Arity} {A A₁ : Ambient Γ} {A' A₁' : Ambient Γ'}
    (ι : Ambient.Renaming A A') (ι₁ : Ambient.Renaming A₁ A₁')
    (hslot : ι₁.slot = ι.slot) :
  ∀ {Ω : C.Arity} {Θ Θ' : dTel Γ Ω}, Eq_t.Both A A₁ Θ Θ' →
    Eq_t.Both A' A₁' (dTel.rename ι.slot Θ) (dTel.rename ι.slot Θ')
  | _, .nil, _, h => by
      obtain rfl := Eq_t.Both.nil_inv h
      apply Eq_t.Both.nil
  | _, .cons (α := α) bind boundary _, _, h => by
      obtain ⟨bind', boundary', _, rfl, hbind, hboundary, hboundary', hrest⟩ :=
        Eq_t.Both.cons_inv h
      apply Eq_t.Both.cons (Eq_t.Both.weaken ι ι₁ hslot hbind)
      · apply Eq_bd.weaken (ι.extend bind) hboundary
      · rw [← hslot]
        apply Eq_bd.weaken (ι₁.extend bind') hboundary'
      · have hrest := Eq_t.Both.weaken (ι.extend (dTel.cons bind boundary .nil))
          (ι₁.extend (dTel.cons bind' boundary' .nil)) (congrArg (· ⇑ʳ C.single α) hslot)
          hrest
        rwa [hslot] at hrest

/-- If `Θ` and `Θ'` are equal over `Ξ` and `Ξ'`, and `X` and `X'` over `Ξ ⋈ Θ`
and `Ξ' ⋈ Θ'`, then `Θ ⋈ X` and `Θ' ⋈ X'` are equal over `Ξ` and `Ξ'`. -/
theorem Eq_t.Both.concatenate {Δ : C.Arity} {Ξ Ξ' : Ambient Δ} :
  ∀ {Ω Φ : C.Arity} {Θ Θ' : dTel Δ Ω} {X X' : dTel (Δ ⋈ Ω) Φ},
    Eq_t.Both Ξ Ξ' Θ Θ' → Eq_t.Both (Ξ ⋈ Θ) (Ξ' ⋈ Θ') X X' →
      Eq_t.Both Ξ Ξ' (dTel.concatenate Θ X) (dTel.concatenate Θ' X')
  | _, _, .nil, _, _, _, h, hX => by
      obtain rfl := Eq_t.Both.nil_inv h
      convert hX using 1
      · symm
        apply dTel.concatenate_nil
      · symm
        apply dTel.concatenate_nil
  | _, _, .cons _ _ _, _, _, _, h, hX => by
      obtain ⟨_, _, _, rfl, hbind, hboundary, hboundary', hrest⟩ := Eq_t.Both.cons_inv h
      apply Eq_t.Both.cons hbind hboundary hboundary'
      apply Eq_t.Both.concatenate hrest
      rwa [dTel.concatenate_assoc, dTel.concatenate_assoc]

/-- If `Θ` and `Θ'` are equal over `Ξ` and `Ξ'`, their declarations at every
slot `z` are equal over `Ξ' ⋈ Θ' ⋈ Θ'.binding z`. -/
theorem Eq_t.Both.declaration_right {Δ : C.Arity} {Ξ Ξ' : Ambient Δ} :
  ∀ {Ω : C.Arity} {Θ Θ' : dTel Δ Ω}, Eq_t.Both Ξ Ξ' Θ Θ' →
    ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
      Eq_bd (Ξ' ⋈ Θ' ⋈ Θ'.binding z) (Θ.declaration z) (Θ'.declaration z)
  | _, .nil, _, _, _, z => (C.unit_is_empty z).elim
  | _, .cons _ _ _, _, h, _, z => by
      obtain ⟨bind', _, _, rfl, _, _, hboundary', hrest⟩ := Eq_t.Both.cons_inv h
      induction z using slotCases with
      | head =>
        rw [dTel.declaration_head, dTel.declaration_head, dTel.binding_head]
        apply Eq_bd.weaken ((Ambient.Renaming.weaken Ξ' _).extend bind') hboundary'
      | tail y =>
        rw [dTel.declaration_tail, dTel.declaration_tail, dTel.binding_tail]
        convert Eq_t.Both.declaration_right hrest y using 2
        symm
        apply dTel.concatenate_assoc

/-- If `Θ` and `Θ'` are equal over `Ξ` and `Ξ'`, the entries they bind at every
slot are equal over `Ξ ⋈ Θ` and `Ξ' ⋈ Θ'`. -/
theorem Eq_t.Both.binding {Δ : C.Arity} {Ξ Ξ' : Ambient Δ} :
  ∀ {Ω : C.Arity} {Θ Θ' : dTel Δ Ω}, Eq_t.Both Ξ Ξ' Θ Θ' →
    ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
      Eq_t.Both (Ξ ⋈ Θ) (Ξ' ⋈ Θ') (Θ.binding z) (Θ'.binding z)
  | _, .nil, _, _, _, z => (C.unit_is_empty z).elim
  | _, .cons _ _ _, _, h, _, z => by
      obtain ⟨_, _, _, rfl, hbind, _, _, hrest⟩ := Eq_t.Both.cons_inv h
      induction z using slotCases with
      | head =>
        rw [dTel.binding_head, dTel.binding_head]
        apply Eq_t.Both.weaken (Ambient.Renaming.weaken Ξ _)
          (Ambient.Renaming.weaken Ξ' _) rfl hbind
      | tail y =>
        rw [dTel.binding_tail, dTel.binding_tail]
        convert Eq_t.Both.binding hrest y using 1
        · symm
          apply dTel.concatenate_assoc
        · symm
          apply dTel.concatenate_assoc
