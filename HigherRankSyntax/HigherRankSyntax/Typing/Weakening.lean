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
  | _, _, .congr (Ω := Ω) (Θ := Θ) (e := e₁) (e' := e₂) σ θ hσ hθ agree h => by
      refine Eq.mp ?_ (Eq_e.congr (Ξ := A') (Θ := dTel.rename ι.slot Θ)
        (fun ⦃Λ⦄ i => ⟦ ι.slot ⇑ʳ Λ ⟧ʳ (σ i)) (fun ⦃Λ⦄ i => ⟦ ι.slot ⇑ʳ Λ ⟧ʳ (θ i))
        (Wf_s.weaken ι hσ) (Wf_s.weaken ι hθ) ?agree (Eq_e.weaken (ι.extend Θ) h))
      case agree =>
        intro Λ z hne
        have h₀ : ¬ (Bd.act (Ξ := 1) σ Λ (Θ.declaration z)).isEq := by
          refine fun hEq => hne ?_
          exact Eq.mp (congrArg Bd.isEq (dTel.act_declaration_rename ι.slot σ Θ z).symm)
            ((Bd.isEq_rename (ι.slot ⇑ʳ Λ) _).mpr hEq)
        refine Eq.mp ?_ (Eq_e.weaken (ι.extend (dTel.instantiate σ (Θ.binding z)))
          (agree z h₀))
        exact congrArg (fun T => Eq_e ((A' ⋈ T))
            (⟦ ι.slot ⇑ʳ Λ ⟧ʳ (σ z)) (⟦ ι.slot ⇑ʳ Λ ⟧ʳ (θ z)))
          (dTel.instantiate_binding_rename ι.slot σ Θ z).symm
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
  | _, _, _, .mk (Θ := Θ) (σ := σ) equation filler declared => by
      refine Wf_s.mk ?equation ?filler ?declared
      case equation =>
        intro Λ z l r h
        replace h := (dTel.act_declaration_rename ι.slot σ Θ z).symm.trans h
        cases hb : Bd.act (Ξ := 1) σ Λ (Θ.declaration z) with
        | sort =>
            rw [hb] at h
            replace h := (Bd.rename_sort _).symm.trans h
            cases h
        | of S =>
            rw [hb] at h
            replace h := (Bd.rename_of _ _).symm.trans h
            cases h
        | eq l₀ r₀ =>
            rw [hb] at h
            replace h := (Bd.rename_eq _ _ _).symm.trans h
            injection h with hl hr
            subst hl
            subst hr
            refine Eq.mp ?_ (Eq_e.weaken (ι.extend (dTel.instantiate σ (Θ.binding z)))
              (equation z l₀ r₀ hb))
            exact congrArg (fun T => Eq_e ((A' ⋈ T))
              (⟦ ι.slot ⇑ʳ Λ ⟧ʳ l₀) (⟦ ι.slot ⇑ʳ Λ ⟧ʳ r₀))
              (dTel.instantiate_binding_rename ι.slot σ Θ z).symm
      case filler =>
        intro Λ z hne
        refine Eq.mp ?_ (Wf_e.weaken (ι.extend (dTel.instantiate σ (Θ.binding z)))
          (filler z ?h₀))
        case h₀ =>
          refine fun hEq => hne ?_
          exact Eq.mp (congrArg Bd.isEq (dTel.act_declaration_rename ι.slot σ Θ z).symm)
            ((Bd.isEq_rename (ι.slot ⇑ʳ Λ) _).mpr hEq)
        exact congrArg (fun T => Wf_e ((A' ⋈ T)) (⟦ ι.slot ⇑ʳ Λ ⟧ʳ (σ z)))
          (dTel.instantiate_binding_rename ι.slot σ Θ z).symm
      case declared =>
        intro Λ z hne
        have h₀ : ¬ (Bd.act (Ξ := 1) σ Λ (Θ.declaration z)).isEq := by
          refine fun hEq => hne ?_
          exact Eq.mp (congrArg Bd.isEq (dTel.act_declaration_rename ι.slot σ Θ z).symm)
            ((Bd.isEq_rename (ι.slot ⇑ʳ Λ) _).mpr hEq)
        refine Eq.mp ?_ (Eq_bd.weaken (ι.extend (dTel.instantiate σ (Θ.binding z)))
          (declared z h₀))
        refine Eq.trans (congrArg₂ (fun (b c : Bd (Γ' ⋈ Λ)) =>
            Eq_bd (A' ⋈ dTel.rename ι.slot (dTel.instantiate σ (Θ.binding z))) b c)
          (Ambient.Renaming.boundaryOf (ι.extend (dTel.instantiate σ (Θ.binding z)))
            (σ z)).symm
          (dTel.act_declaration_rename ι.slot σ Θ z).symm) ?_
        exact congrArg (fun T => Eq_bd ((A' ⋈ T))
            (((A' ⋈ T)).boundaryOf (⟦ ι.slot ⇑ʳ Λ ⟧ʳ (σ z)))
            (Bd.act (Ξ := 1) (fun ⦃Λ'⦄ i => ⟦ ι.slot ⇑ʳ Λ' ⟧ʳ (σ i)) Λ
              ((dTel.rename ι.slot Θ).declaration z)))
          (dTel.instantiate_binding_rename ι.slot σ Θ z).symm

end

/-! ## Stability of telescopes -/

/-- 8(8): a well-formed declaration stays well formed under a renaming of ambients. -/
theorem Wf_bd.weaken {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') {Λ : C.Arity} (Θ : dTel Γ Λ) :
    ∀ {β : Bd (Γ ⋈ Λ)}, Wf_bd A Θ β →
      Wf_bd A' (dTel.rename ι.slot Θ) (Bd.rename (ι.slot ⇑ʳ Λ) β)
  | .sort, _ => trivial
  | .of S, ⟨hS, hsort⟩ => by
      refine ⟨Wf_e.weaken (ι.extend Θ) hS, ?_⟩
      refine Eq.mp ?_ (Eq_bd.weaken (ι.extend Θ) hsort)
      exact congrArg (fun b => Eq_bd ((A' ⋈ dTel.rename ι.slot Θ)) b Bd.sort)
        (Ambient.Renaming.boundaryOf (ι.extend Θ) S).symm
  | .eq l r, ⟨hl, hr, heq⟩ => by
      refine ⟨Wf_e.weaken (ι.extend Θ) hl, Wf_e.weaken (ι.extend Θ) hr, ?_⟩
      refine Eq.mp ?_ (Eq_bd.weaken (ι.extend Θ) heq)
      exact congrArg₂ (fun b c => Eq_bd ((A' ⋈ dTel.rename ι.slot Θ)) b c)
        (Ambient.Renaming.boundaryOf (ι.extend Θ) l).symm
        (Ambient.Renaming.boundaryOf (ι.extend Θ) r).symm

/-- 8(8): a well-formed telescope stays well formed under a renaming of ambients. -/
theorem Wf_t.weaken {Γ Γ' : C.Arity} {A : Ambient Γ} {A' : Ambient Γ'}
    (ι : Ambient.Renaming A A') :
    ∀ {Ω : C.Arity} {Θ : dTel Γ Ω}, Wf_t A Θ → Wf_t A' (dTel.rename ι.slot Θ)
  | _, .nil, _ => trivial
  | _, .cons bind boundary rest, h =>
      ⟨Wf_t.weaken ι h.1, Wf_bd.weaken ι bind h.2.1,
        Wf_t.weaken (ι.extend (dTel.cons bind boundary .nil)) h.2.2⟩

/-- A well-formed ambient is a well-formed telescope over every ambient. -/
theorem Ambient.Wf.weaken {Δ Ω : C.Arity} {A : Ambient Ω} (h : Ambient.Wf A)
    (Ξ : Ambient Δ) : Wf_t Ξ (dTel.rename (Renaming.fromUnit Δ) A) :=
  Wf_t.weaken (Ambient.Renaming.fromEmpty Ξ) h

/-- The declaration of every slot of a well-formed telescope is well formed. -/
theorem Wf_t.declaration {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {Ω : C.Arity} {Θ : dTel Δ Ω}, Wf_t Ξ Θ → ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
      Wf_bd ((Ξ ⋈ Θ)) (Θ.binding z) (Θ.declaration z)
  | _, .nil, _, _, z => (C.unit_is_empty z).elim
  | _, .cons (α := α) (Δ := Δ') bind boundary rest, h, Λ, z => by
      refine slotCases (α := α) (Δ := Δ')
        (motive := fun ⦃Λ⦄ z => Wf_bd ((Ξ ⋈ dTel.cons bind boundary rest))
          ((dTel.cons bind boundary rest).binding z)
          ((dTel.cons bind boundary rest).declaration z)) ?head ?tail z
      case head =>
        refine Eq.mp ?_ (Wf_bd.weaken
          (Ambient.Renaming.weaken Ξ (dTel.cons bind boundary rest)) bind h.2.1)
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
          (Wf_t.declaration h.2.2 y)
        exact congrArg₂ (fun (T : dTel (Δ ⋈ (C.single α ⋈ Δ')) γ)
            (b : Bd ((Δ ⋈ (C.single α ⋈ Δ')) ⋈ γ)) =>
            Wf_bd ((Ξ ⋈ dTel.cons bind boundary rest)) T b)
          (dTel.binding_tail bind boundary rest y).symm
          (dTel.declaration_tail bind boundary rest y).symm

/-- A well-formed declaration is equal to itself. -/
theorem Wf_bd.refl {Δ Λ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Λ} :
    ∀ {β : Bd (Δ ⋈ Λ)}, Wf_bd Ξ Θ β → Eq_bd ((Ξ ⋈ Θ)) β β
  | .sort, _ => .sort
  | .of _, ⟨hS, _⟩ => .of (.refl hS)
  | .eq _ _, ⟨hl, hr, _⟩ => .eq (.refl hl) (.refl hr)

/-- The entries bound by every slot of a well-formed telescope are well formed. -/
theorem Wf_t.binding {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {Ω : C.Arity} {Θ : dTel Δ Ω}, Wf_t Ξ Θ → ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
      Wf_t ((Ξ ⋈ Θ)) (Θ.binding z)
  | _, .nil, _, _, z => (C.unit_is_empty z).elim
  | _, .cons (α := α) (Δ := Δ') bind boundary rest, h, Λ, z => by
      refine slotCases (α := α) (Δ := Δ')
        (motive := fun ⦃Λ⦄ z => Wf_t ((Ξ ⋈ dTel.cons bind boundary rest))
          ((dTel.cons bind boundary rest).binding z)) ?head ?tail z
      case head =>
        refine Eq.mp ?_ (Wf_t.weaken
          (Ambient.Renaming.weaken Ξ (dTel.cons bind boundary rest)) h.1)
        exact congrArg (fun (T : dTel (Δ ⋈ (C.single α ⋈ Δ')) α) =>
            Wf_t ((Ξ ⋈ dTel.cons bind boundary rest)) T)
          (dTel.binding_head bind boundary rest).symm
      case tail =>
        intro γ y
        refine Eq.mp (Eq.trans (congrArg (fun (B : Ambient (Δ ⋈ (C.single α ⋈ Δ'))) =>
            Wf_t B (rest.binding y))
          (dTel.concatenate_assoc Ξ (dTel.cons bind boundary .nil) rest)) ?_)
          (Wf_t.binding h.2.2 y)
        exact congrArg (fun (T : dTel (Δ ⋈ (C.single α ⋈ Δ')) γ) =>
            Wf_t ((Ξ ⋈ dTel.cons bind boundary rest)) T)
          (dTel.binding_tail bind boundary rest y).symm
