import HigherRankSyntax.Ctx.Universe

/-!
# Equations

The entry declaring the equation between the expressions two fillings of an
entry binding nothing supply, and the types it presents.
-/

open CategoryTheory

namespace Ctx

/-- The entry declaring the equation between what two fillings supply is well
formed. -/
theorem Ob.Entry.id_wf {X : Ob} {β : Bd (X.arity ⋈ 1)}
    {wβ : Ob.Tele.Wf X (dTel.cons .nil β .nil)} (hne : ¬ β.isEq)
    (τ τ' : Ob.Fill X (Ob.Entry.mk 1 .nil β wβ).toTele) :
    Ob.Tele.Wf X (dTel.cons .nil (.eq τ.filler τ'.filler) .nil) := by
  obtain ⟨Γ⟩ := X
  have hs : Wf_s Γ.ambient (dTel.cons .nil β .nil) τ.1 := τ.2.2
  have hs' : Wf_s Γ.ambient (dTel.cons .nil β .nil) τ'.1 := τ'.2.2
  have hb := dTel.binding_head_instantiate (.nil : dTel Γ.arity 1) β .nil τ.1
  have hd := dTel.declaration_head_instantiate (.nil : dTel Γ.arity 1) β .nil τ.1
  have hb' := dTel.binding_head_instantiate (.nil : dTel Γ.arity 1) β .nil τ'.1
  have hd' := dTel.declaration_head_instantiate (.nil : dTel Γ.arity 1) β .nil τ'.1
  have hl := Eq.mp (congrArg (fun T => Wf_e (Γ.ambient ⋈ T) τ.filler) hb)
    (hs.filler (C.inl (C.singleSlot 1)) (by rw [hd]; exact hne))
  have hr := Eq.mp (congrArg (fun T => Wf_e (Γ.ambient ⋈ T) τ'.filler) hb')
    (hs'.filler (C.inl (C.singleSlot 1)) (by rw [hd']; exact hne))
  have hdl := Eq.mp (congrArg₂ (fun T b => Eq_bd (Γ.ambient ⋈ T)
      ((Γ.ambient ⋈ T).boundaryOf τ.filler) b) hb hd)
    (hs.declared (C.inl (C.singleSlot 1)) (by rw [hd]; exact hne))
  have hdr := Eq.mp (congrArg₂ (fun T b => Eq_bd (Γ.ambient ⋈ T)
      ((Γ.ambient ⋈ T).boundaryOf τ'.filler) b) hb' hd')
    (hs'.declared (C.inl (C.singleSlot 1)) (by rw [hd']; exact hne))
  exact Wf_t.cons Wf_t.nil (Wf_bd.eq hl hr (Eq_bd.trans hdl (Eq_bd.symm hdr)))
    Wf_t.nil

/-- The entry declaring the equation between what two fillings supply. -/
def Ob.Entry.id {X : Ob} {β : Bd (X.arity ⋈ 1)}
    {wβ : Ob.Tele.Wf X (dTel.cons .nil β .nil)} (hne : ¬ β.isEq)
    (τ τ' : Ob.Fill X (Ob.Entry.mk 1 .nil β wβ).toTele) : Ob.Entry X where
  arity := 1
  binding := .nil
  declaration := .eq τ.filler τ'.filler
  wf := Ob.Entry.id_wf hne τ τ'

theorem Ob.Entry.id_congr {X : Ob} {β : Bd (X.arity ⋈ 1)}
    {wβ : Ob.Tele.Wf X (dTel.cons .nil β .nil)} (hne : ¬ β.isEq)
    {τ τ' σ σ' : Ob.Fill X (Ob.Entry.mk 1 .nil β wβ).toTele}
    (h : Ob.Fill.Rel τ σ) (h' : Ob.Fill.Rel τ' σ') :
    Ob.Entry.Rel (Ob.Entry.id hne τ τ') (Ob.Entry.id hne σ σ') := by
  obtain ⟨Γ⟩ := X
  obtain ⟨hw, hws, he⟩ := h
  obtain ⟨hw', hws', he'⟩ := h'
  have hes : Eq_s Γ.ambient (dTel.cons .nil β .nil) τ.1 σ.1 := he
  have hes' : Eq_s Γ.ambient (dTel.cons .nil β .nil) τ'.1 σ'.1 := he'
  have hb := dTel.binding_head_instantiate (.nil : dTel Γ.arity 1) β .nil τ.1
  have hd := dTel.declaration_head_instantiate (.nil : dTel Γ.arity 1) β .nil τ.1
  have hb' := dTel.binding_head_instantiate (.nil : dTel Γ.arity 1) β .nil τ'.1
  have hd' := dTel.declaration_head_instantiate (.nil : dTel Γ.arity 1) β .nil τ'.1
  have hsl := Eq.mp (congrArg (fun T => Eq_e (Γ.ambient ⋈ T) τ.filler σ.filler) hb)
    (hes.slot (C.inl (C.singleSlot 1)) (by rw [hd]; exact hne))
  have hsr := Eq.mp
    (congrArg (fun T => Eq_e (Γ.ambient ⋈ T) τ'.filler σ'.filler) hb')
    (hes'.slot (C.inl (C.singleSlot 1)) (by rw [hd']; exact hne))
  exact ⟨rfl, Ob.Entry.id_wf hne τ τ',
    Eq_t.cons Eq_t.nil (Eq_bd.eq hsl hsr) Eq_t.nil⟩

/-- The filling of the entry declaring that what a filling supplies equals
itself. -/
theorem Ob.Entry.id_fill_wf {X : Ob} {β : Bd (X.arity ⋈ 1)}
    {wβ : Ob.Tele.Wf X (dTel.cons .nil β .nil)} (hne : ¬ β.isEq)
    (τ : Ob.Fill X (Ob.Entry.mk 1 .nil β wβ).toTele) :
    Ob.Fill.Wf X (Ob.Entry.id hne τ τ).toTele.telescope
      (_root_.Subst.single τ.filler) := by
  obtain ⟨Γ⟩ := X
  obtain ⟨hnil, hbd, hrest⟩ := Wf_t.cons_inv (Ob.Entry.id_wf hne τ τ)
  cases hbd with
  | eq hl hr heq =>
    refine ⟨Ob.Entry.id_wf hne τ τ, ?_⟩
    refine (Wf_s.single_iff τ.filler).mpr ⟨fun a b he => ?_,
      fun hn => absurd trivial hn, fun hn => absurd trivial hn⟩
    injection he with h₁ h₂
    subst h₁
    subst h₂
    exact Eq_e.refl hl

/-- The filling declaring that what a filling supplies equals itself. -/
def Ob.Fill.idRefl {X : Ob} {β : Bd (X.arity ⋈ 1)}
    {wβ : Ob.Tele.Wf X (dTel.cons .nil β .nil)} (hne : ¬ β.isEq)
    (τ : Ob.Fill X (Ob.Entry.mk 1 .nil β wβ).toTele) :
    Ob.Fill X (Ob.Entry.id hne τ τ).toTele :=
  ⟨_root_.Subst.single τ.filler, Ob.Entry.id_fill_wf hne τ⟩

/-- The type asserting that the two sorts two classes of fillings supply are
equal. -/
def IdSortOf (X : Ob)
    (u u' : Quotient (Ob.Fill.setoid (Ob.Entry.sort X).toTele)) : Ty₁ X :=
  Quotient.liftOn₂ u u'
    (fun τ τ' => Quotient.mk (Ob.Entry.setoid X)
      (Ob.Entry.id (β := Bd.sort) not_false τ τ'))
    (fun _ _ _ _ h h' => by
      exact Quotient.sound (Ob.Entry.id_congr (β := Bd.sort) not_false h h'))

/-- The type asserting that two sorts are equal. -/
def IdSort {X : Ob} (S S' : Tm₁ X (U X)) : Ty₁ X :=
  IdSortOf X (Tm₁.fillEquiv (Ob.Entry.sort X) S)
    (Tm₁.fillEquiv (Ob.Entry.sort X) S')

/-- Every sort equals itself. -/
def IdSort_refl {X : Ob} (S : Tm₁ X (U X)) : Tm₁ X (IdSort S S) :=
  Quotient.hrecOn (motive := fun u => Tm₁ X (IdSortOf X u u))
    (Tm₁.fillEquiv (Ob.Entry.sort X) S)
    (fun τ => Tm₁.ofFill (Ob.Fill.idRefl (β := Bd.sort) not_false τ))
    (by
      intro τ τ' h
      refine Tm₁.heq_of_eq ?_
      obtain ⟨Γ⟩ := X
      obtain ⟨hca, hcwf, hceq⟩ :=
        Ob.Entry.id_congr (β := Bd.sort) not_false h h
      refine Quotient.sound (Exists.intro
        (rfl : C.single 1 ⋈ 1 = C.single 1 ⋈ 1) ?_)
      exact ⟨⟨hcwf, hceq⟩, hcwf,
        (Ob.Entry.id_fill_wf (β := Bd.sort) not_false τ).2,
        Eq_s.cons (fun hn => absurd trivial hn) Eq_s.nil⟩)


/-- A type declaring an equation has at most one term. -/
theorem Tm₁.subsingleton {X : Ob} {u : Ob.Entry X} (h : u.declaration.isEq)
    (t t' : Tm₁ X (Quotient.mk (Ob.Entry.setoid X) u)) : t = t' := by
  obtain ⟨Γ⟩ := X
  refine Tm₁.ind (motive := fun t => ∀ t', t = t') ?_ t t'
  intro τ t'
  refine Tm₁.ind (motive := fun t' => Tm₁.ofFill τ = t') ?_ t'
  intro τ'
  exact Subtype.ext (Quotient.sound ⟨rfl, ⟨u.wf, Wf_t.refl u.wf⟩, u.wf, τ.2.2,
    Eq_s.cons (fun hne => absurd h hne) Eq_s.nil⟩)

theorem IdSort_irrelevant {X : Ob} {S S' : Tm₁ X (U X)}
    (t t' : Tm₁ X (IdSort S S')) : t = t' := by
  refine Tm₁.ind (motive := fun S => ∀ (S' : Tm₁ X (U X))
    (t t' : Tm₁ X (IdSort S S')), t = t') ?_ S S' t t'
  intro τ S' t t'
  refine Tm₁.ind (motive := fun S' => ∀ (t t' : Tm₁ X (IdSort (Tm₁.ofFill τ) S')),
    t = t') ?_ S' t t'
  intro τ' t t'
  exact Tm₁.subsingleton (u := Ob.Entry.id (β := Bd.sort) not_false τ τ') trivial t t'

theorem IdSort_reflect {X : Ob} {S S' : Tm₁ X (U X)}
    (t : Tm₁ X (IdSort S S')) : S = S' := by
  refine Tm₁.ind (motive := fun S => ∀ (S' : Tm₁ X (U X))
    (_ : Tm₁ X (IdSort S S')), S = S') ?_ S S' t
  intro τ S' t
  refine Tm₁.ind (motive := fun S' =>
    ∀ _ : Tm₁ X (IdSort (Tm₁.ofFill τ) S'), Tm₁.ofFill τ = S') ?_ S' t
  intro τ' t
  refine Tm₁.ind (motive := fun _ => Tm₁.ofFill τ = Tm₁.ofFill τ') ?_ t
  intro ρ
  obtain ⟨Γ⟩ := X
  have hs : Wf_s Γ.ambient
      (dTel.cons .nil (.eq τ.filler τ'.filler) .nil) ρ.1 := ρ.2.2
  have hb := dTel.binding_head_instantiate (.nil : dTel Γ.arity 1)
    (Bd.eq τ.filler τ'.filler) .nil ρ.1
  have hd := dTel.declaration_head_instantiate (.nil : dTel Γ.arity 1)
    (Bd.eq τ.filler τ'.filler) .nil ρ.1
  have heq := Eq.mp (congrArg (fun T => Eq_e (Γ.ambient ⋈ T) τ.filler τ'.filler) hb)
    (hs.equation (C.inl (C.singleSlot 1)) τ.filler τ'.filler hd)
  refine Subtype.ext (Quotient.sound ⟨rfl, ⟨(Ob.Entry.sort Γ.toOb).wf, ?_⟩,
    (Ob.Entry.sort Γ.toOb).wf, τ.2.2, ?_⟩)
  · exact Wf_t.refl (Ob.Entry.sort Γ.toOb).wf
  · exact Eq_s.cons (fun _ => heq) Eq_s.nil

theorem IdSort_subst {X Y : Ob} (S S' : Tm₁ X (U X)) (σ : Y ⟶ X) :
    (IdSort S S').subst σ
      = IdSort (U_subst σ ▸ S.subst σ) (U_subst σ ▸ S'.subst σ) := by
  induction σ using Quotient.ind with
  | _ σ =>
  refine Tm₁.ind (motive := fun S => ∀ S' : Tm₁ X (U X),
    (IdSort S S').subst (Quotient.mk _ σ)
      = IdSort (U_subst (Quotient.mk _ σ) ▸ S.subst (Quotient.mk _ σ))
        (U_subst (Quotient.mk _ σ) ▸ S'.subst (Quotient.mk _ σ))) ?_ S S'
  intro τ S'
  refine Tm₁.ind (motive := fun S' =>
    (IdSort (Tm₁.ofFill τ) S').subst (Quotient.mk _ σ)
      = IdSort (U_subst (Quotient.mk _ σ) ▸ (Tm₁.ofFill τ).subst (Quotient.mk _ σ))
        (U_subst (Quotient.mk _ σ) ▸ S'.subst (Quotient.mk _ σ))) ?_ S'
  intro τ'
  rfl

/-- The type of elements of the sort a class of fillings supplies. -/
def ElOf (X : Ob) (u : Quotient (Ob.Fill.setoid (Ob.Entry.sort X).toTele)) :
    Ty₁ X :=
  Quotient.liftOn u (fun τ => Quotient.mk (Ob.Entry.setoid X) (Ob.Entry.of τ))
    (fun _ _ h => by exact Quotient.sound (Ob.Entry.of_congr h))

/-- The type asserting that the two elements two classes of fillings supply are
equal. -/
def IdOfEntry (X : Ob) (τ : Ob.Fill X (Ob.Entry.sort X).toTele)
    (v v' : Quotient (Ob.Fill.setoid (Ob.Entry.of τ).toTele)) : Ty₁ X :=
  Quotient.liftOn₂ v v'
    (fun ρ ρ' => Quotient.mk (Ob.Entry.setoid X)
      (Ob.Entry.id (β := Bd.of τ.filler) not_false ρ ρ'))
    (fun _ _ _ _ h h' => by
      exact Quotient.sound
        (Ob.Entry.id_congr (β := Bd.of τ.filler) not_false h h'))

/-- The type asserting that two elements of the sort a class of fillings
supplies are equal. -/
def IdElementOf (X : Ob)
    (u : Quotient (Ob.Fill.setoid (Ob.Entry.sort X).toTele)) :
    Tm₁ X (ElOf X u) → Tm₁ X (ElOf X u) → Ty₁ X :=
  Quotient.hrecOn (motive := fun u => Tm₁ X (ElOf X u) → Tm₁ X (ElOf X u) → Ty₁ X)
    u
    (fun τ l r => IdOfEntry X τ (Tm₁.fillEquiv (Ob.Entry.of τ) l)
      (Tm₁.fillEquiv (Ob.Entry.of τ) r))
    (by
      intro τ τ' h
      have hE : Ob.Entry.Rel (Ob.Entry.of τ) (Ob.Entry.of τ') :=
        Ob.Entry.of_congr h
      refine Function.hfunext (congrArg (Tm₁ X) (Quotient.sound hE)) ?_
      intro l l' hl
      refine Function.hfunext (congrArg (Tm₁ X) (Quotient.sound hE)) ?_
      intro r r' hr
      apply heq_of_eq
      induction l using Tm₁.ind with
      | _ ρ =>
      induction l' using Tm₁.ind with
      | _ ρ'' =>
      induction r using Tm₁.ind with
      | _ σ =>
      induction r' using Tm₁.ind with
      | _ σ'' =>
      obtain ⟨Γ⟩ := X
      obtain ⟨hla, hlt, hlf⟩ :=
        Quotient.exact (Tm₁.eq_of_heq (Quotient.sound hE) hl)
      obtain ⟨hra, hrt, hrf⟩ :=
        Quotient.exact (Tm₁.eq_of_heq (Quotient.sound hE) hr)
      have hbl := dTel.binding_head_instantiate (.nil : dTel Γ.arity 1)
        (Bd.of τ.filler) .nil ρ.1
      have hbr := dTel.binding_head_instantiate (.nil : dTel Γ.arity 1)
        (Bd.of τ.filler) .nil σ.1
      have hel := Eq.mp
        (congrArg (fun T => Eq_e (Γ.ambient ⋈ T) ρ.filler ρ''.filler) hbl)
        (hlf.2.2.slot (C.inl (C.singleSlot 1)) not_false)
      have her := Eq.mp
        (congrArg (fun T => Eq_e (Γ.ambient ⋈ T) σ.filler σ''.filler) hbr)
        (hrf.2.2.slot (C.inl (C.singleSlot 1)) not_false)
      refine Quotient.sound ?_
      exact ⟨rfl, Ob.Entry.id_wf (β := Bd.of τ.filler) not_false ρ σ,
        Eq_t.cons Eq_t.nil (Eq_bd.eq hel her) Eq_t.nil⟩)

/-- The type asserting that two elements of a sort are equal. -/
def IdElement {X : Ob} {S : Tm₁ X (U X)} (l r : Tm₁ X (El S)) : Ty₁ X :=
  IdElementOf X (Tm₁.fillEquiv (Ob.Entry.sort X) S) l r


theorem IdElement_irrelevant {X : Ob} {S : Tm₁ X (U X)} {l r : Tm₁ X (El S)}
    (t t' : Tm₁ X (IdElement l r)) : t = t' := by
  induction S using Tm₁.ind with
  | _ τ =>
  induction l using Tm₁.ind with
  | _ ρ =>
  induction r using Tm₁.ind with
  | _ σ =>
  exact Tm₁.subsingleton
    (u := Ob.Entry.id (β := Bd.of τ.filler) not_false ρ σ) trivial t t'

theorem IdElement_reflect {X : Ob} {S : Tm₁ X (U X)} {l r : Tm₁ X (El S)}
    (t : Tm₁ X (IdElement l r)) : l = r := by
  induction S using Tm₁.ind with
  | _ τ =>
  induction l using Tm₁.ind with
  | _ ρ =>
  induction r using Tm₁.ind with
  | _ σ =>
  induction t using Tm₁.ind with
  | _ ν =>
  obtain ⟨Γ⟩ := X
  have hs : Wf_s Γ.ambient
      (dTel.cons .nil (.eq ρ.filler σ.filler) .nil) ν.1 := ν.2.2
  have hb := dTel.binding_head_instantiate (.nil : dTel Γ.arity 1)
    (Bd.eq ρ.filler σ.filler) .nil ν.1
  have hd := dTel.declaration_head_instantiate (.nil : dTel Γ.arity 1)
    (Bd.eq ρ.filler σ.filler) .nil ν.1
  have heq := Eq.mp (congrArg (fun T => Eq_e (Γ.ambient ⋈ T) ρ.filler σ.filler) hb)
    (hs.equation (C.inl (C.singleSlot 1)) ρ.filler σ.filler hd)
  refine Subtype.ext (Quotient.sound ⟨rfl, ⟨(Ob.Entry.of τ).wf, ?_⟩,
    (Ob.Entry.of τ).wf, ρ.2.2, ?_⟩)
  · exact Wf_t.refl (Ob.Entry.of τ).wf
  · exact Eq_s.cons (fun _ => heq) Eq_s.nil

/-- Every element equals itself. -/
def IdElement_refl {X : Ob} {S : Tm₁ X (U X)} (l : Tm₁ X (El S)) :
    Tm₁ X (IdElement l l) :=
  Quotient.hrecOn
    (motive := fun u => (l : Tm₁ X (ElOf X u)) → Tm₁ X (IdElementOf X u l l))
    (Tm₁.fillEquiv (Ob.Entry.sort X) S)
    (fun τ l => Quotient.hrecOn (motive := fun v => Tm₁ X (IdOfEntry X τ v v))
      (Tm₁.fillEquiv (Ob.Entry.of τ) l)
      (fun ρ => Tm₁.ofFill (Ob.Fill.idRefl (β := Bd.of τ.filler) not_false ρ))
      (by
        intro ρ ρ' h
        refine Tm₁.heq_of_eq ?_
        obtain ⟨Γ⟩ := X
        obtain ⟨hca, hcwf, hceq⟩ :=
          Ob.Entry.id_congr (β := Bd.of τ.filler) not_false h h
        refine Quotient.sound (Exists.intro
          (rfl : C.single 1 ⋈ 1 = C.single 1 ⋈ 1) ?_)
        exact ⟨⟨hcwf, hceq⟩, hcwf,
          (Ob.Entry.id_fill_wf (β := Bd.of τ.filler) not_false ρ).2,
          Eq_s.cons (fun hn => absurd trivial hn) Eq_s.nil⟩))
    (by
      intro τ τ' h
      have hE : Ob.Entry.Rel (Ob.Entry.of τ) (Ob.Entry.of τ') :=
        Ob.Entry.of_congr h
      refine Function.hfunext (congrArg (Tm₁ X) (Quotient.sound hE)) ?_
      intro l l' hl
      refine Tm₁.heq_of_eq ?_
      induction l using Tm₁.ind with
      | _ ρ =>
      induction l' using Tm₁.ind with
      | _ ρ'' =>
      obtain ⟨Γ⟩ := X
      obtain ⟨hla, hlt, hlf⟩ :=
        Quotient.exact (Tm₁.eq_of_heq (Quotient.sound hE) hl)
      have hbl := dTel.binding_head_instantiate (.nil : dTel Γ.arity 1)
        (Bd.of τ.filler) .nil ρ.1
      have hel := Eq.mp
        (congrArg (fun T => Eq_e (Γ.ambient ⋈ T) ρ.filler ρ''.filler) hbl)
        (hlf.2.2.slot (C.inl (C.singleSlot 1)) not_false)
      refine Quotient.sound (Exists.intro
        (rfl : C.single 1 ⋈ 1 = C.single 1 ⋈ 1) ?_)
      exact ⟨⟨Ob.Entry.id_wf (β := Bd.of τ.filler) not_false ρ ρ,
          Eq_t.cons Eq_t.nil (Eq_bd.eq hel hel) Eq_t.nil⟩,
        Ob.Entry.id_wf (β := Bd.of τ.filler) not_false ρ ρ,
        (Ob.Entry.id_fill_wf (β := Bd.of τ.filler) not_false ρ).2,
        Eq_s.cons (fun hn => absurd trivial hn) Eq_s.nil⟩)
    l

theorem IdElement_subst {X Y : Ob} {S : Tm₁ X (U X)} (l r : Tm₁ X (El S))
    (σ : Y ⟶ X) :
    (IdElement l r).subst σ
      = IdElement (El_subst S σ ▸ l.subst σ) (El_subst S σ ▸ r.subst σ) := by
  induction σ using Quotient.ind with
  | _ σ =>
  induction S using Tm₁.ind with
  | _ τ =>
  induction l using Tm₁.ind with
  | _ ρ =>
  induction r using Tm₁.ind with
  | _ ν =>
  rfl

end Ctx
