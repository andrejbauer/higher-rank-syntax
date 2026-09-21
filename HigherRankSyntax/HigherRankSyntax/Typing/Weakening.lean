import HigherRankSyntax.Typing.Rules

/-!
# Weakening

A derivation stays valid when declarations it does not mention are added to the
ambient.  Stated over a renaming of ambients rather than over a literal insertion,
so that the source ambient is a variable and the induction can case on the
derivation; the insertion is recovered as `(Ambient.Renaming.weaken Ξ Θ).extend Ψ`.
-/

/-! ## Renamings of ambients -/

/-- A renaming of ambients: slots keep the entries they bind and their
declaration, both up to the renaming. -/
structure Ambient.Renaming {Γ Γ' : C.Arity} (A : Ambient Γ) (A' : Ambient Γ') where
  slot : Γ →ʳ Γ'
  declaration : ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α),
    A'.declaration (slot x) = Bd.rename (slot ⇑ʳ α) (A.declaration x)
  binding : ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α),
    A'.binding (slot x) = dTel.rename slot (A.binding x)

namespace Ambient.Renaming

/-- A renamed slot is equational exactly when it was. -/
theorem isEq {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') {α : C.Arity} (x : Γ ∋ α) :
    (A'.declaration (ι.slot x)).isEq ↔ (A.declaration x).isEq :=
  (Eq.to_iff (congrArg Bd.isEq (ι.declaration x))).trans (Bd.isEq_rename _ _)

/-- Weakening on the right is a renaming of ambients. -/
def weaken {Δ Ω : C.Arity} (Ξ : Ambient Δ) (Θ : dTel Δ Ω) :
    Ambient.Renaming Ξ ((Ξ ⋈ Θ)) where
  slot := Renaming.inl Δ Ω
  declaration := fun ⦃_⦄ x => dTel.declaration_concatenate_inl Ξ Θ x
  binding := fun ⦃_⦄ x => dTel.binding_concatenate_inl Ξ Θ x

/-- An ambient is a renaming of itself weakened into another. -/
def weakenInto {Γ Γ' : C.Arity} (A : Ambient Γ) (A' : Ambient Γ') :
    Ambient.Renaming A (A' ⋈ dTel.rename (Renaming.fromUnit Γ') A) where
  slot := Renaming.inr Γ' Γ
  declaration := by
    intro α x
    refine Eq.trans (dTel.declaration_concatenate_inr A'
      (dTel.rename (Renaming.fromUnit Γ') A) x) ?_
    refine Eq.trans (dTel.declaration_rename (Renaming.fromUnit Γ') A x) ?_
    exact congrArg (fun ρ => Bd.rename (ρ ⇑ʳ α) (A.declaration x))
      (Renaming.fromUnit_extend Γ' Γ)
  binding := by
    intro α x
    refine Eq.trans (dTel.binding_concatenate_inr A'
      (dTel.rename (Renaming.fromUnit Γ') A) x) ?_
    refine Eq.trans (dTel.binding_rename (Renaming.fromUnit Γ') A x) ?_
    exact congrArg (fun ρ => dTel.rename ρ (A.binding x))
      (Renaming.fromUnit_extend Γ' Γ)

/-- The empty ambient maps into every ambient. -/
def fromEmpty {Δ : C.Arity} (Ξ : Ambient Δ) :
    Ambient.Renaming (.nil : Ambient 1) Ξ where
  slot := Renaming.fromUnit Δ
  declaration := fun ⦃_⦄ x => (C.unit_is_empty x).elim
  binding := fun ⦃_⦄ x => (C.unit_is_empty x).elim

/-- A renaming of ambients extends along a telescope. -/
def extend {Γ Γ' Ω : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') (Θ : dTel Γ Ω) :
    Ambient.Renaming ((A ⋈ Θ)) ((A' ⋈ dTel.rename ι.slot Θ)) where
  slot := ι.slot ⇑ʳ Ω
  declaration := by
    intro α x
    rcases C.cover Γ Ω x with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · refine Eq.trans (congrArg (fun w => ((A' ⋈ dTel.rename ι.slot Θ)).declaration w)
        (Renaming.extend_inl ι.slot y)) ?_
      refine Eq.trans (dTel.declaration_concatenate_inl _ _ _) ?_
      refine Eq.trans (congrArg (Bd.rename (Renaming.inl Γ' Ω ⇑ʳ α)) (ι.declaration y)) ?_
      refine Eq.trans (Bd.rename_comp _ _ _).symm ?_
      refine Eq.trans ?_ (congrArg (Bd.rename ((ι.slot ⇑ʳ Ω) ⇑ʳ α))
        (dTel.declaration_concatenate_inl A Θ y)).symm
      refine Eq.trans ?_ (Bd.rename_comp _ _ _)
      exact congrArg (fun ρ => Bd.rename ρ (A.declaration y))
        (((Renaming.extend_comp _ _ α).symm.trans
          (congrArg (fun s => s ⇑ʳ α) (Renaming.inl_comp ι.slot))).trans
            (Renaming.extend_comp _ _ α))
    · refine Eq.trans (congrArg (fun w => ((A' ⋈ dTel.rename ι.slot Θ)).declaration w)
        (Renaming.extend_inr ι.slot z)) ?_
      refine Eq.trans (dTel.declaration_concatenate_inr _ _ _) ?_
      refine Eq.trans (dTel.declaration_rename _ _ _) ?_
      exact congrArg (Bd.rename ((ι.slot ⇑ʳ Ω) ⇑ʳ α))
        (dTel.declaration_concatenate_inr A Θ z).symm
  binding := by
    intro α x
    rcases C.cover Γ Ω x with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · refine Eq.trans (congrArg (fun w => ((A' ⋈ dTel.rename ι.slot Θ)).binding w)
        (Renaming.extend_inl ι.slot y)) ?_
      refine Eq.trans (dTel.binding_concatenate_inl _ _ _) ?_
      refine Eq.trans (congrArg (dTel.rename (Renaming.inl Γ' Ω)) (ι.binding y)) ?_
      refine Eq.trans (dTel.rename_comp _ _ _).symm ?_
      refine Eq.trans ?_ (congrArg (dTel.rename (ι.slot ⇑ʳ Ω))
        (dTel.binding_concatenate_inl A Θ y)).symm
      refine Eq.trans ?_ (dTel.rename_comp _ _ _)
      exact congrArg (fun ρ => dTel.rename ρ (A.binding y)) (Renaming.inl_comp ι.slot)
    · refine Eq.trans (congrArg (fun w => ((A' ⋈ dTel.rename ι.slot Θ)).binding w)
        (Renaming.extend_inr ι.slot z)) ?_
      refine Eq.trans (dTel.binding_concatenate_inr _ _ _) ?_
      refine Eq.trans (dTel.binding_rename _ _ _) ?_
      exact congrArg (dTel.rename (ι.slot ⇑ʳ Ω)) (dTel.binding_concatenate_inr A Θ z).symm

/-- A renaming of ambients carries computed boundaries to computed boundaries. -/
theorem boundaryOf {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') :
    ∀ e : Expr Γ, A'.boundaryOf (⟦ ι.slot ⟧ʳ e) = Bd.rename ι.slot (A.boundaryOf e)
  | .ap (α := α) x args => by
      refine Eq.trans (dTel.boundaryOf_ap _ _ _) ?_
      refine Eq.trans (congrArg (Bd.instantiate _) (ι.declaration x)) ?_
      refine Eq.trans (congrArg (Bd.instantiate (fun ⦃Λ⦄ i => ⟦ ι.slot ⇑ʳ Λ ⟧ʳ (args i)))
        (congrArg (fun ρ => Bd.rename ρ (A.declaration x))
          (Renaming.extend_unit (ι.slot ⇑ʳ α)).symm)) ?_
      refine Eq.trans (Bd.act_rename (Φ := 1) ι.slot args (A.declaration x)) ?_
      exact congrArg (fun ρ => Bd.rename ρ (Bd.instantiate args (A.declaration x)))
        (Renaming.extend_unit ι.slot)

end Ambient.Renaming

/-! ## Stability of the judgements -/

mutual

/-- 8(8): well-formedness of expressions is stable under a renaming of ambients. -/
theorem Wf_e.weaken {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') :
    ∀ {e : Expr Γ}, Wf_e A e → Wf_e A' (⟦ ι.slot ⟧ʳ e)
  | _, .ap (α := α) x args head fill => by
      refine Wf_e.ap _ _ ?head ?fill
      case head =>
        exact fun hEq => head ((ι.isEq x).mp hEq)
      case fill =>
        refine Eq.mp ?_ (Wf_s.weaken ι fill)
        exact congrArg (fun T => Wf_s A' T (fun ⦃Λ⦄ i => ⟦ ι.slot ⇑ʳ Λ ⟧ʳ (args i)))
          (ι.binding x).symm

/-- 8(8): equality of expressions is stable under a renaming of ambients. -/
theorem Eq_e.weaken {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') :
    ∀ {e e' : Expr Γ}, Eq_e A e e' → Eq_e A' (⟦ ι.slot ⟧ʳ e) (⟦ ι.slot ⟧ʳ e')
  | _, _, .refl h => .refl (Wf_e.weaken ι h)
  | _, _, .symm h => .symm (Eq_e.weaken ι h)
  | _, _, .trans h h' => .trans (Eq_e.weaken ι h) (Eq_e.weaken ι h')
  | _, _, .hyp (Λ := Λ) q l r args decl hl hr fill => by
      refine Eq.mp ?_ (Eq_e.hyp (Ξ := A') (ι.slot q) (⟦ ι.slot ⇑ʳ Λ ⟧ʳ l) (⟦ ι.slot ⇑ʳ Λ ⟧ʳ r)
        (fun ⦃_⦄ i => ⟦ ι.slot ⇑ʳ _ ⟧ʳ (args i)) ?decl ?hl ?hr ?fill)
      case decl =>
        exact (ι.declaration q).trans (congrArg (Bd.rename (ι.slot ⇑ʳ Λ)) decl)
      case hl =>
        refine Eq.mp ?_ (Wf_e.weaken (ι.extend (A.binding q)) hl)
        exact congrArg (fun T => Wf_e ((A' ⋈ T)) (⟦ ι.slot ⇑ʳ Λ ⟧ʳ l)) (ι.binding q).symm
      case hr =>
        refine Eq.mp ?_ (Wf_e.weaken (ι.extend (A.binding q)) hr)
        exact congrArg (fun T => Wf_e ((A' ⋈ T)) (⟦ ι.slot ⇑ʳ Λ ⟧ʳ r)) (ι.binding q).symm
      case fill =>
        refine Eq.mp ?_ (Wf_s.weaken ι fill)
        exact congrArg (fun T => Wf_s A' T (fun ⦃_⦄ i => ⟦ ι.slot ⇑ʳ _ ⟧ʳ (args i)))
          (ι.binding q).symm
      exact congrArg₂ (Eq_e A') (act_rename _ _ _ ι.slot args l) (act_rename _ _ _ ι.slot args r)
  | _, _, .congr (Ω := Ω) (Θ := Θ) (e := e₁) (e' := e₂) σ θ hΘ hσ hθ agree h => by
      refine Eq.mp ?_ (Eq_e.congr (Ξ := A') (Θ := dTel.rename ι.slot Θ)
        (fun ⦃Λ⦄ i => ⟦ ι.slot ⇑ʳ Λ ⟧ʳ (σ i)) (fun ⦃Λ⦄ i => ⟦ ι.slot ⇑ʳ Λ ⟧ʳ (θ i))
        (Wf_t.weaken ι hΘ) (Wf_s.weaken ι hσ) (Wf_s.weaken ι hθ)
        (Eq_s.weaken ι agree) (Eq_e.weaken (ι.extend Θ) h))
      exact congrArg₂ (Eq_e A') (act_rename _ _ _ ι.slot σ _) (act_rename _ _ _ ι.slot θ _)

/-- 8(8): equality of boundaries is stable under a renaming of ambients. -/
theorem Eq_bd.weaken {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') :
    ∀ {β β' : Bd Γ}, Eq_bd A β β' →
      Eq_bd A' (Bd.rename ι.slot β) (Bd.rename ι.slot β')
  | _, _, .sort => .sort
  | _, _, .of h => .of (Eq_e.weaken ι h)
  | _, _, .eq hl hr => .eq (Eq_e.weaken ι hl) (Eq_e.weaken ι hr)

/-- 8(8): filling is stable under a renaming of ambients. -/
theorem Wf_s.weaken {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') :
    ∀ {Ω : C.Arity} {Θ : dTel Γ Ω} {σ : Subst Ω Γ}, Wf_s A Θ σ →
      Wf_s A' (dTel.rename ι.slot Θ) (fun ⦃Λ⦄ i => ⟦ ι.slot ⇑ʳ Λ ⟧ʳ (σ i))
  | _, _, _, .nil => .nil
  | _, _, _, .cons (α := α) (σ := σ) (bind := bind) (boundary := boundary)
      (rest := rest) equation filler declared hrest => by
      refine .cons ?equation ?filler ?declared ?hrest
      case equation =>
        intro l r h
        obtain ⟨l₀, r₀, hβ, hl, hr⟩ := Bd.rename_eq_inv (ι.slot ⇑ʳ α) h
        subst hl
        subst hr
        exact Eq_e.weaken (ι.extend bind) (equation l₀ r₀ hβ)
      case filler =>
        intro hne
        exact Wf_e.weaken (ι.extend bind)
          (filler (fun hEq => hne ((Bd.isEq_rename (ι.slot ⇑ʳ α) boundary).mpr hEq)))
      case declared =>
        intro hne
        have h₀ : ¬ boundary.isEq :=
          fun hEq => hne ((Bd.isEq_rename (ι.slot ⇑ʳ α) boundary).mpr hEq)
        refine Eq.mp ?_ (Eq_bd.weaken (ι.extend bind) (declared h₀))
        exact congrArg (fun b => Eq_bd ((A' ⋈ dTel.rename ι.slot bind)) b
            (Bd.rename (ι.slot ⇑ʳ α) boundary))
          (Ambient.Renaming.boundaryOf (ι.extend bind)
            (σ (C.inl (C.singleSlot α)))).symm
      case hrest =>
        refine Eq.mp (congrArg (fun T => Wf_s A' T
          (fun ⦃β⦄ (j : _ ∋ β) => ⟦ ι.slot ⇑ʳ β ⟧ʳ (σ (C.inr j))))
          (dTel.instantiate_rename ι.slot
            (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) rest).symm) ?_
        exact Wf_s.weaken ι hrest

/-- 8(8): agreement of fillings is stable under a renaming of ambients. -/
theorem Eq_s.weaken {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') :
    ∀ {Ω : C.Arity} {Θ : dTel Γ Ω} {σ θ : Subst Ω Γ}, Eq_s A Θ σ θ →
      Eq_s A' (dTel.rename ι.slot Θ) (fun ⦃Λ⦄ i => ⟦ ι.slot ⇑ʳ Λ ⟧ʳ (σ i))
        (fun ⦃Λ⦄ i => ⟦ ι.slot ⇑ʳ Λ ⟧ʳ (θ i))
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons (α := α) (σ := σ) (θ := θ) (bind := bind)
      (boundary := boundary) (rest := rest) slot hrest => by
      refine .cons ?slot ?hrest
      case slot =>
        intro hne
        exact Eq_e.weaken (ι.extend bind)
          (slot (fun hEq => hne ((Bd.isEq_rename (ι.slot ⇑ʳ α) boundary).mpr hEq)))
      case hrest =>
        refine Eq.mp (congrArg (fun T => Eq_s A' T
          (fun ⦃β⦄ (j : _ ∋ β) => ⟦ ι.slot ⇑ʳ β ⟧ʳ (σ (C.inr j)))
          (fun ⦃β⦄ (j : _ ∋ β) => ⟦ ι.slot ⇑ʳ β ⟧ʳ (θ (C.inr j))))
          (dTel.instantiate_rename ι.slot
            (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) rest).symm) ?_
        exact Eq_s.weaken ι hrest

/-- 8(8): a well-formed declaration stays well formed under a renaming of ambients. -/
theorem Wf_bd.weaken {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') {Λ : C.Arity} (Θ : dTel Γ Λ) :
    ∀ {β : Bd (Γ ⋈ Λ)}, Wf_bd A Θ β →
      Wf_bd A' (dTel.rename ι.slot Θ) (Bd.rename (ι.slot ⇑ʳ Λ) β)
  | _, .sort => .sort
  | _, .of (S := S) hS hsort => by
      refine Wf_bd.of (Wf_e.weaken (ι.extend Θ) hS) ?_
      refine Eq.mp ?_ (Eq_bd.weaken (ι.extend Θ) hsort)
      exact congrArg (fun b => Eq_bd ((A' ⋈ dTel.rename ι.slot Θ)) b Bd.sort)
        (Ambient.Renaming.boundaryOf (ι.extend Θ) S).symm
  | _, .eq (l := l) (r := r) hl hr heq => by
      refine Wf_bd.eq (Wf_e.weaken (ι.extend Θ) hl) (Wf_e.weaken (ι.extend Θ) hr) ?_
      refine Eq.mp ?_ (Eq_bd.weaken (ι.extend Θ) heq)
      exact congrArg₂ (fun b c => Eq_bd ((A' ⋈ dTel.rename ι.slot Θ)) b c)
        (Ambient.Renaming.boundaryOf (ι.extend Θ) l).symm
        (Ambient.Renaming.boundaryOf (ι.extend Θ) r).symm

/-- 8(8): a well-formed telescope stays well formed under a renaming of ambients. -/
theorem Wf_t.weaken {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') :
    ∀ {Ω : C.Arity} {Θ : dTel Γ Ω}, Wf_t A Θ → Wf_t A' (dTel.rename ι.slot Θ)
  | _, _, .nil => .nil
  | _, _, .cons (bind := bind) (boundary := boundary) hbind hboundary hrest =>
      .cons (Wf_t.weaken ι hbind) (Wf_bd.weaken ι bind hboundary)
        (Wf_t.weaken (ι.extend (dTel.cons bind boundary .nil)) hrest)

end

/-! ## Stability of telescopes -/

/-- A well-formed ambient is a well-formed telescope over every ambient. -/
theorem Ambient.Wf.weaken {Δ Ω : C.Arity} {A : Ambient Ω} (h : Ambient.Wf A)
    (Ξ : Ambient Δ) : Wf_t Ξ (dTel.rename (Renaming.fromUnit Δ) A) :=
  Wf_t.weaken (Ambient.Renaming.fromEmpty Ξ) h

/-- The declaration of every slot of a well-formed telescope is well formed. -/
theorem Wf_t.declaration {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {Ω : C.Arity} {Θ : dTel Δ Ω}, Wf_t Ξ Θ → ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
      Wf_bd ((Ξ ⋈ Θ)) (Θ.binding z) (Θ.declaration z)
  | _, _, .nil, _, z => (C.unit_is_empty z).elim
  | _, _, .cons (α := α) (Ω := Δ') (bind := bind) (boundary := boundary)
      (rest := rest) hbind hboundary hrest, Λ, z => by
      refine slotCases (α := α) (Δ := Δ')
        (motive := fun ⦃Λ⦄ z => Wf_bd ((Ξ ⋈ dTel.cons bind boundary rest))
          ((dTel.cons bind boundary rest).binding z)
          ((dTel.cons bind boundary rest).declaration z)) ?head ?tail z
      case head =>
        refine Eq.mp ?_ (Wf_bd.weaken
          (Ambient.Renaming.weaken Ξ (dTel.cons bind boundary rest)) bind hboundary)
        exact congrArg₂ (fun (T : dTel (Δ ⋈ (C.single α ⋈ Δ')) α)
            (b : Bd ((Δ ⋈ (C.single α ⋈ Δ')) ⋈ α)) =>
            Wf_bd ((Ξ ⋈ dTel.cons bind boundary rest)) T b)
          (dTel.binding_head bind boundary rest).symm
          (dTel.declaration_head bind boundary rest).symm
      case tail =>
        intro γ y
        refine Eq.mp (Eq.trans (congrArg (fun (B : Ambient (Δ ⋈ (C.single α ⋈ Δ'))) =>
            Wf_bd B (rest.binding y) (rest.declaration y))
          (dTel.concatenate_assoc Ξ (dTel.cons bind boundary .nil) rest)) ?_)
          (Wf_t.declaration hrest y)
        exact congrArg₂ (fun (T : dTel (Δ ⋈ (C.single α ⋈ Δ')) γ)
            (b : Bd ((Δ ⋈ (C.single α ⋈ Δ')) ⋈ γ)) =>
            Wf_bd ((Ξ ⋈ dTel.cons bind boundary rest)) T b)
          (dTel.binding_tail bind boundary rest y).symm
          (dTel.declaration_tail bind boundary rest y).symm

/-- A well-formed declaration is equal to itself. -/
theorem Wf_bd.refl {Δ Λ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Λ} :
    ∀ {β : Bd (Δ ⋈ Λ)}, Wf_bd Ξ Θ β → Eq_bd ((Ξ ⋈ Θ)) β β
  | _, .sort => .sort
  | _, .of hS _ => .of (.refl hS)
  | _, .eq hl hr _ => .eq (.refl hl) (.refl hr)

/-- The entries bound by every slot of a well-formed telescope are well formed. -/
theorem Wf_t.binding {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {Ω : C.Arity} {Θ : dTel Δ Ω}, Wf_t Ξ Θ → ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
      Wf_t ((Ξ ⋈ Θ)) (Θ.binding z)
  | _, _, .nil, _, z => (C.unit_is_empty z).elim
  | _, _, .cons (α := α) (Ω := Δ') (bind := bind) (boundary := boundary)
      (rest := rest) hbind hboundary hrest, Λ, z => by
      refine slotCases (α := α) (Δ := Δ')
        (motive := fun ⦃Λ⦄ z => Wf_t ((Ξ ⋈ dTel.cons bind boundary rest))
          ((dTel.cons bind boundary rest).binding z)) ?head ?tail z
      case head =>
        refine Eq.mp ?_ (Wf_t.weaken
          (Ambient.Renaming.weaken Ξ (dTel.cons bind boundary rest)) hbind)
        exact congrArg (fun (T : dTel (Δ ⋈ (C.single α ⋈ Δ')) α) =>
            Wf_t ((Ξ ⋈ dTel.cons bind boundary rest)) T)
          (dTel.binding_head bind boundary rest).symm
      case tail =>
        intro γ y
        refine Eq.mp (Eq.trans (congrArg (fun (B : Ambient (Δ ⋈ (C.single α ⋈ Δ'))) =>
            Wf_t B (rest.binding y))
          (dTel.concatenate_assoc Ξ (dTel.cons bind boundary .nil) rest)) ?_)
          (Wf_t.binding hrest y)
        exact congrArg (fun (T : dTel (Δ ⋈ (C.single α ⋈ Δ')) γ) =>
            Wf_t ((Ξ ⋈ dTel.cons bind boundary rest)) T)
          (dTel.binding_tail bind boundary rest y).symm

/-- A well-formed telescope is equal to itself. -/
theorem Wf_t.refl {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {Ω : C.Arity} {Θ : dTel Δ Ω}, Wf_t Ξ Θ → Eq_t Ξ Θ Θ
  | _, _, .nil => .nil
  | _, _, .cons hbind hboundary hrest =>
      .cons (Wf_t.refl hbind) (Wf_bd.refl hboundary) (Wf_t.refl hrest)

/-- 8(8): equality of telescopes is stable under a renaming of ambients. -/
theorem Eq_t.weaken {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') :
    ∀ {Ω : C.Arity} {Θ Θ' : dTel Γ Ω}, Eq_t A Θ Θ' →
      Eq_t A' (dTel.rename ι.slot Θ) (dTel.rename ι.slot Θ')
  | _, .nil, _, h => by
      obtain rfl := Eq_t.nil_inv h
      exact Eq_t.nil
  | _, .cons bind boundary rest, _, h => by
      obtain ⟨_, _, _, rfl, hbind, hboundary, hrest⟩ := Eq_t.cons_inv h
      exact Eq_t.cons (Eq_t.weaken ι hbind) (Eq_bd.weaken (ι.extend bind) hboundary)
        (Eq_t.weaken (ι.extend (dTel.cons bind boundary .nil)) hrest)

/-- Equality of telescopes is preserved by concatenation. -/
theorem Eq_t.concatenate {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {Ω Φ : C.Arity} {Θ Θ' : dTel Δ Ω} {X X' : dTel (Δ ⋈ Ω) Φ},
      Eq_t Ξ Θ Θ' → Eq_t (Ξ ⋈ Θ) X X' →
        Eq_t Ξ (dTel.concatenate Θ X) (dTel.concatenate Θ' X')
  | _, _, .nil, _, X, X', h, hX => by
      obtain rfl := Eq_t.nil_inv h
      exact Eq.mp (congrArg (fun A => Eq_t A X X') (dTel.concatenate_nil Ξ)) hX
  | _, _, .cons bind boundary rest, _, X, X', h, hX => by
      obtain ⟨_, _, _, rfl, hbind, hboundary, hrest⟩ := Eq_t.cons_inv h
      refine Eq_t.cons hbind hboundary (Eq_t.concatenate hrest ?_)
      exact Eq.mp (congrArg (fun A => Eq_t A X X')
        (dTel.concatenate_assoc Ξ (dTel.cons bind boundary .nil) rest).symm) hX

/-- The declarations of equal telescopes are equal at every slot. -/
theorem Eq_t.declaration {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {Ω : C.Arity} {Θ Θ' : dTel Δ Ω}, Eq_t Ξ Θ Θ' → ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
      Eq_bd ((Ξ ⋈ Θ ⋈ Θ.binding z)) (Θ.declaration z) (Θ'.declaration z)
  | _, .nil, _, _, _, z => (C.unit_is_empty z).elim
  | _, .cons (α := α) (Δ := Δ') bind boundary rest, _, h, Λ, z => by
      obtain ⟨bind', boundary', rest', rfl, hbind, hboundary, hrest⟩ :=
        Eq_t.cons_inv h
      refine slotCases (α := α) (Δ := Δ')
        (motive := fun ⦃Λ⦄ z => Eq_bd ((Ξ ⋈ dTel.cons bind boundary rest
            ⋈ (dTel.cons bind boundary rest).binding z))
          ((dTel.cons bind boundary rest).declaration z)
          ((dTel.cons bind' boundary' rest').declaration z)) ?head ?tail z
      case head =>
        refine Eq.mp ?_ (Eq_bd.weaken
          ((Ambient.Renaming.weaken Ξ (dTel.cons bind boundary rest)).extend bind)
          hboundary)
        refine Eq.trans (congrArg (fun (T : dTel (Δ ⋈ (C.single α ⋈ Δ')) α) =>
            Eq_bd ((Ξ ⋈ dTel.cons bind boundary rest ⋈ T))
              (Bd.rename (Renaming.inl Δ (C.single α ⋈ Δ') ⇑ʳ α) boundary)
              (Bd.rename (Renaming.inl Δ (C.single α ⋈ Δ') ⇑ʳ α) boundary'))
          (dTel.binding_head bind boundary rest).symm) ?_
        exact congrArg₂ (fun (a b : Bd ((Δ ⋈ (C.single α ⋈ Δ')) ⋈ α)) =>
            Eq_bd ((Ξ ⋈ dTel.cons bind boundary rest
              ⋈ (dTel.cons bind boundary rest).binding (C.inl (C.singleSlot α)))) a b)
          (dTel.declaration_head bind boundary rest).symm
          (dTel.declaration_head bind' boundary' rest').symm
      case tail =>
        intro γ y
        refine Eq.mp ?_ (Eq_t.declaration hrest y)
        refine Eq.trans (congrArg (fun (B : Ambient (Δ ⋈ (C.single α ⋈ Δ'))) =>
            Eq_bd ((B ⋈ rest.binding y)) (rest.declaration y) (rest'.declaration y))
          (dTel.concatenate_assoc Ξ (dTel.cons bind boundary .nil) rest)) ?_
        refine Eq.trans (congrArg (fun (T : dTel (Δ ⋈ (C.single α ⋈ Δ')) γ) =>
            Eq_bd ((Ξ ⋈ dTel.cons bind boundary rest ⋈ T))
              (rest.declaration y) (rest'.declaration y))
          (dTel.binding_tail bind boundary rest y).symm) ?_
        exact congrArg₂ (fun (a b : Bd ((Δ ⋈ (C.single α ⋈ Δ')) ⋈ γ)) =>
            Eq_bd ((Ξ ⋈ dTel.cons bind boundary rest
              ⋈ (dTel.cons bind boundary rest).binding (C.inr y))) a b)
          (dTel.declaration_tail bind boundary rest y).symm
          (dTel.declaration_tail bind' boundary' rest' y).symm

/-- The entries bound by equal telescopes are equal at every slot. -/
theorem Eq_t.binding {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {Ω : C.Arity} {Θ Θ' : dTel Δ Ω}, Eq_t Ξ Θ Θ' → ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
      Eq_t ((Ξ ⋈ Θ)) (Θ.binding z) (Θ'.binding z)
  | _, .nil, _, _, _, z => (C.unit_is_empty z).elim
  | _, .cons (α := α) (Δ := Δ') bind boundary rest, _, h, Λ, z => by
      obtain ⟨bind', boundary', rest', rfl, hbind, hboundary, hrest⟩ :=
        Eq_t.cons_inv h
      refine slotCases (α := α) (Δ := Δ')
        (motive := fun ⦃Λ⦄ z => Eq_t ((Ξ ⋈ dTel.cons bind boundary rest))
          ((dTel.cons bind boundary rest).binding z)
          ((dTel.cons bind' boundary' rest').binding z)) ?head ?tail z
      case head =>
        refine Eq.mp ?_ (Eq_t.weaken
          (Ambient.Renaming.weaken Ξ (dTel.cons bind boundary rest)) hbind)
        exact congrArg₂ (fun (T U : dTel (Δ ⋈ (C.single α ⋈ Δ')) α) =>
            Eq_t ((Ξ ⋈ dTel.cons bind boundary rest)) T U)
          (dTel.binding_head bind boundary rest).symm
          (dTel.binding_head bind' boundary' rest').symm
      case tail =>
        intro γ y
        refine Eq.mp ?_ (Eq_t.binding hrest y)
        refine Eq.trans (congrArg (fun (B : Ambient (Δ ⋈ (C.single α ⋈ Δ'))) =>
            Eq_t B (rest.binding y) (rest'.binding y))
          (dTel.concatenate_assoc Ξ (dTel.cons bind boundary .nil) rest)) ?_
        exact congrArg₂ (fun (T U : dTel (Δ ⋈ (C.single α ⋈ Δ')) γ) =>
            Eq_t ((Ξ ⋈ dTel.cons bind boundary rest)) T U)
          (dTel.binding_tail bind boundary rest y).symm
          (dTel.binding_tail bind' boundary' rest' y).symm

/-! ### Telescopes equal over two ambients -/

/-- Telescopes equal over two ambients stay so under a renaming of each by one
map. -/
theorem Eq_t.Both.weaken {Γ Γ' : C.Arity} {A A₁ : Ambient Γ} {A' A₁' : Ambient Γ'}
    (ι : Ambient.Renaming A A') (ι₁ : Ambient.Renaming A₁ A₁')
    (hslot : ι₁.slot = ι.slot) :
    ∀ {Ω : C.Arity} {Θ Θ' : dTel Γ Ω}, Eq_t.Both A A₁ Θ Θ' →
      Eq_t.Both A' A₁' (dTel.rename ι.slot Θ) (dTel.rename ι.slot Θ')
  | _, .nil, _, h => by
      obtain rfl := Eq_t.Both.nil_inv h
      exact Eq_t.Both.nil
  | _, .cons (α := α) bind boundary rest, _, h => by
      obtain ⟨bind', boundary', rest', rfl, hbind, hboundary, hboundary', hrest⟩ :=
        Eq_t.Both.cons_inv h
      refine Eq_t.Both.cons (Eq_t.Both.weaken ι ι₁ hslot hbind)
        (Eq_bd.weaken (ι.extend bind) hboundary) ?boundary ?rest
      case boundary =>
        refine Eq.mp ?_ (Eq_bd.weaken (ι₁.extend bind') hboundary')
        exact congrArg (fun (ρ : Γ →ʳ Γ') => Eq_bd ((A₁' ⋈ dTel.rename ρ bind'))
          (Bd.rename (ρ ⇑ʳ α) boundary) (Bd.rename (ρ ⇑ʳ α) boundary')) hslot
      case rest =>
        refine Eq.mp ?_ (Eq_t.Both.weaken
          (ι.extend (dTel.cons bind boundary .nil))
          (ι₁.extend (dTel.cons bind' boundary' .nil))
          (congrArg (fun (ρ : Γ →ʳ Γ') => ρ ⇑ʳ C.single α) hslot) hrest)
        exact congrArg (fun (ρ : Γ →ʳ Γ') => Eq_t.Both
          ((A' ⋈ dTel.rename ι.slot (dTel.cons bind boundary .nil)))
          ((A₁' ⋈ dTel.rename ρ (dTel.cons bind' boundary' .nil)))
          (dTel.rename (ι.slot ⇑ʳ C.single α) rest)
          (dTel.rename (ι.slot ⇑ʳ C.single α) rest')) hslot

/-- Telescopes equal over two ambients stay so under concatenation. -/
theorem Eq_t.Both.concatenate {Δ : C.Arity} {Ξ Ξ' : Ambient Δ} :
    ∀ {Ω Φ : C.Arity} {Θ Θ' : dTel Δ Ω} {X X' : dTel (Δ ⋈ Ω) Φ},
      Eq_t.Both Ξ Ξ' Θ Θ' → Eq_t.Both ((Ξ ⋈ Θ)) ((Ξ' ⋈ Θ')) X X' →
        Eq_t.Both Ξ Ξ' (dTel.concatenate Θ X) (dTel.concatenate Θ' X')
  | _, _, .nil, _, X, X', h, hX => by
      obtain rfl := Eq_t.Both.nil_inv h
      exact Eq.mp (congrArg₂ (fun (A B : Ambient Δ) => Eq_t.Both A B X X')
        (dTel.concatenate_nil Ξ) (dTel.concatenate_nil Ξ')) hX
  | _, _, .cons bind boundary rest, _, X, X', h, hX => by
      obtain ⟨bind', boundary', rest', rfl, hbind, hboundary, hboundary', hrest⟩ :=
        Eq_t.Both.cons_inv h
      refine Eq_t.Both.cons hbind hboundary hboundary'
        (Eq_t.Both.concatenate hrest ?_)
      exact Eq.mp (congrArg₂ (fun (A B : Ambient _) => Eq_t.Both A B X X')
        (dTel.concatenate_assoc Ξ (dTel.cons bind boundary .nil) rest).symm
        (dTel.concatenate_assoc Ξ' (dTel.cons bind' boundary' .nil) rest').symm) hX

/-- The declarations of telescopes equal over two ambients are equal at every
slot, over the ambient built from the second. -/
theorem Eq_t.Both.declaration_right {Δ : C.Arity} {Ξ Ξ' : Ambient Δ} :
    ∀ {Ω : C.Arity} {Θ Θ' : dTel Δ Ω}, Eq_t.Both Ξ Ξ' Θ Θ' →
      ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
        Eq_bd ((Ξ' ⋈ Θ' ⋈ Θ'.binding z)) (Θ.declaration z) (Θ'.declaration z)
  | _, .nil, _, _, _, z => (C.unit_is_empty z).elim
  | _, .cons (α := α) (Δ := Δ') bind boundary rest, _, h, Λ, z => by
      obtain ⟨bind', boundary', rest', rfl, hbind, hboundary, hboundary', hrest⟩ :=
        Eq_t.Both.cons_inv h
      refine slotCases (α := α) (Δ := Δ')
        (motive := fun ⦃Λ⦄ z => Eq_bd ((Ξ' ⋈ dTel.cons bind' boundary' rest'
            ⋈ (dTel.cons bind' boundary' rest').binding z))
          ((dTel.cons bind boundary rest).declaration z)
          ((dTel.cons bind' boundary' rest').declaration z)) ?head ?tail z
      case head =>
        refine Eq.mp ?_ (Eq_bd.weaken
          ((Ambient.Renaming.weaken Ξ' (dTel.cons bind' boundary' rest')).extend bind')
          hboundary')
        refine Eq.trans (congrArg (fun (T : dTel (Δ ⋈ (C.single α ⋈ Δ')) α) =>
            Eq_bd ((Ξ' ⋈ dTel.cons bind' boundary' rest' ⋈ T))
              (Bd.rename (Renaming.inl Δ (C.single α ⋈ Δ') ⇑ʳ α) boundary)
              (Bd.rename (Renaming.inl Δ (C.single α ⋈ Δ') ⇑ʳ α) boundary'))
          (dTel.binding_head bind' boundary' rest').symm) ?_
        exact congrArg₂ (fun (a b : Bd ((Δ ⋈ (C.single α ⋈ Δ')) ⋈ α)) =>
            Eq_bd ((Ξ' ⋈ dTel.cons bind' boundary' rest'
              ⋈ (dTel.cons bind' boundary' rest').binding (C.inl (C.singleSlot α))))
              a b)
          (dTel.declaration_head bind boundary rest).symm
          (dTel.declaration_head bind' boundary' rest').symm
      case tail =>
        intro γ y
        refine Eq.mp ?_ (Eq_t.Both.declaration_right hrest y)
        refine Eq.trans (congrArg (fun (B : Ambient (Δ ⋈ (C.single α ⋈ Δ'))) =>
            Eq_bd ((B ⋈ rest'.binding y)) (rest.declaration y) (rest'.declaration y))
          (dTel.concatenate_assoc Ξ' (dTel.cons bind' boundary' .nil) rest')) ?_
        refine Eq.trans (congrArg (fun (T : dTel (Δ ⋈ (C.single α ⋈ Δ')) γ) =>
            Eq_bd ((Ξ' ⋈ dTel.cons bind' boundary' rest' ⋈ T))
              (rest.declaration y) (rest'.declaration y))
          (dTel.binding_tail bind' boundary' rest' y).symm) ?_
        exact congrArg₂ (fun (a b : Bd ((Δ ⋈ (C.single α ⋈ Δ')) ⋈ γ)) =>
            Eq_bd ((Ξ' ⋈ dTel.cons bind' boundary' rest'
              ⋈ (dTel.cons bind' boundary' rest').binding (C.inr y))) a b)
          (dTel.declaration_tail bind boundary rest y).symm
          (dTel.declaration_tail bind' boundary' rest' y).symm

/-- The entries bound at a slot of telescopes equal over two ambients are equal
over the extended ambients. -/
theorem Eq_t.Both.binding {Δ : C.Arity} {Ξ Ξ' : Ambient Δ} :
    ∀ {Ω : C.Arity} {Θ Θ' : dTel Δ Ω}, Eq_t.Both Ξ Ξ' Θ Θ' →
      ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
        Eq_t.Both ((Ξ ⋈ Θ)) ((Ξ' ⋈ Θ')) (Θ.binding z) (Θ'.binding z)
  | _, .nil, _, _, _, z => (C.unit_is_empty z).elim
  | _, .cons (α := α) (Δ := Δ') bind boundary rest, _, h, Λ, z => by
      obtain ⟨bind', boundary', rest', rfl, hbind, hboundary, hboundary', hrest⟩ :=
        Eq_t.Both.cons_inv h
      refine slotCases (α := α) (Δ := Δ')
        (motive := fun ⦃Λ⦄ z => Eq_t.Both ((Ξ ⋈ dTel.cons bind boundary rest))
          ((Ξ' ⋈ dTel.cons bind' boundary' rest'))
          ((dTel.cons bind boundary rest).binding z)
          ((dTel.cons bind' boundary' rest').binding z)) ?head ?tail z
      case head =>
        refine Eq.mp ?_ (Eq_t.Both.weaken
          (Ambient.Renaming.weaken Ξ (dTel.cons bind boundary rest))
          (Ambient.Renaming.weaken Ξ' (dTel.cons bind' boundary' rest')) rfl hbind)
        exact congrArg₂ (fun (T U : dTel (Δ ⋈ (C.single α ⋈ Δ')) α) =>
            Eq_t.Both ((Ξ ⋈ dTel.cons bind boundary rest))
              ((Ξ' ⋈ dTel.cons bind' boundary' rest')) T U)
          (dTel.binding_head bind boundary rest).symm
          (dTel.binding_head bind' boundary' rest').symm
      case tail =>
        intro γ y
        refine Eq.mp ?_ (Eq_t.Both.binding hrest y)
        refine Eq.trans (congrArg₂ (fun (B B' : Ambient (Δ ⋈ (C.single α ⋈ Δ'))) =>
            Eq_t.Both B B' (rest.binding y) (rest'.binding y))
          (dTel.concatenate_assoc Ξ (dTel.cons bind boundary .nil) rest)
          (dTel.concatenate_assoc Ξ' (dTel.cons bind' boundary' .nil) rest')) ?_
        exact congrArg₂ (fun (T U : dTel (Δ ⋈ (C.single α ⋈ Δ')) γ) =>
            Eq_t.Both ((Ξ ⋈ dTel.cons bind boundary rest))
              ((Ξ' ⋈ dTel.cons bind' boundary' rest')) T U)
          (dTel.binding_tail bind boundary rest y).symm
          (dTel.binding_tail bind' boundary' rest' y).symm
