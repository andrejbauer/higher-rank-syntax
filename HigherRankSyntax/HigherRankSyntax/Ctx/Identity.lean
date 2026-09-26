import HigherRankSyntax.Ctx.Universe

/-!
# Equations

For fillings `τ`, `τ'` of an entry binding nothing and declaring a boundary that
is not an equation, the entry `Ob.Entry.id hne τ τ'` binding nothing and
declaring the equation between what `τ` and `τ'` supply; and the types given by
its classes: `IdSort S S'` for sorts `S`, `S'` and `IdElement l r` for elements
`l`, `r` of a sort.  Each has at most one term, has one exactly when its two sides
are equal, and commutes with reindexing.
-/

open CategoryTheory

namespace Ctx

/-- For fillings `τ`, `τ'` of the entry binding nothing and declaring `β`, where
`β` is not an equation, the one-entry telescope binding nothing and declaring
`.eq τ.filler τ'.filler` is well formed. -/
theorem Ob.Entry.id_wf
    {X : Ob} {β : Bd (X.arity ⋈ 1)} {wβ : Ob.Tele.Wf X (dTel.cons .nil β .nil)}
    (hne : ¬ β.isEq) (τ τ' : Ob.Fill X (Ob.Entry.mk 1 .nil β wβ).toTele) :
  Ob.Tele.Wf X (dTel.cons .nil (.eq τ.filler τ'.filler) .nil)
  := by
  obtain ⟨Γ⟩ := X
  have hτ : Wf_s Γ.ambient (dTel.cons .nil β .nil) (Subst.single τ.filler) := by
    convert τ.2.2
    apply Subst.single_eta
  have hτ' : Wf_s Γ.ambient (dTel.cons .nil β .nil) (Subst.single τ'.filler) := by
    convert τ'.2.2
    apply Subst.single_eta
  obtain ⟨-, hl, hdl⟩ := (Wf_s.single_iff τ.filler).mp hτ
  obtain ⟨-, hr, hdr⟩ := (Wf_s.single_iff τ'.filler).mp hτ'
  apply Wf_t.cons Wf_t.nil _ Wf_t.nil
  apply Wf_bd.eq (hl hne) (hr hne)
  apply Eq_bd.trans (hdl hne) (Eq_bd.symm (hdr hne))

/-- The entry binding nothing and declaring `.eq τ.filler τ'.filler`. -/
def Ob.Entry.id {X : Ob} {β : Bd (X.arity ⋈ 1)}
    {wβ : Ob.Tele.Wf X (dTel.cons .nil β .nil)} (hne : ¬ β.isEq)
    (τ τ' : Ob.Fill X (Ob.Entry.mk 1 .nil β wβ).toTele) : Ob.Entry X where
  arity := 1
  binding := .nil
  declaration := .eq τ.filler τ'.filler
  wf := Ob.Entry.id_wf hne τ τ'

/-- `Ob.Entry.id hne τ τ'` and `Ob.Entry.id hne σ σ'` are related when `τ` agrees
with `σ` and `τ'` with `σ'`. -/
theorem Ob.Entry.id_congr
    {X : Ob} {β : Bd (X.arity ⋈ 1)} {wβ : Ob.Tele.Wf X (dTel.cons .nil β .nil)}
    (hne : ¬ β.isEq) {τ τ' σ σ' : Ob.Fill X (Ob.Entry.mk 1 .nil β wβ).toTele}
    (h : Ob.Fill.Rel τ σ) (h' : Ob.Fill.Rel τ' σ') :
  Ob.Entry.Rel (Ob.Entry.id hne τ τ') (Ob.Entry.id hne σ σ')
  := by
  obtain ⟨Γ⟩ := X
  obtain ⟨-, -, hτσ⟩ := h
  obtain ⟨-, -, hτσ'⟩ := h'
  use rfl, Ob.Entry.id_wf hne τ τ'
  apply Eq_t.cons Eq_t.nil _ Eq_t.nil
  apply Eq_bd.eq
  · apply hτσ.slot (C.inl (C.singleSlot 1))
    convert hne using 2
    apply dTel.declaration_head_instantiate
  · apply hτσ'.slot (C.inl (C.singleSlot 1))
    convert hne using 2
    apply dTel.declaration_head_instantiate

/-- `Subst.single τ.filler` fills the one-entry telescope of
`Ob.Entry.id hne τ τ`. -/
theorem Ob.Entry.id_fill_wf
    {X : Ob} {β : Bd (X.arity ⋈ 1)} {wβ : Ob.Tele.Wf X (dTel.cons .nil β .nil)}
    (hne : ¬ β.isEq) (τ : Ob.Fill X (Ob.Entry.mk 1 .nil β wβ).toTele) :
  Ob.Fill.Wf X (Ob.Entry.id hne τ τ).toTele.telescope (_root_.Subst.single τ.filler)
  := by
  obtain ⟨Γ⟩ := X
  obtain ⟨-, hid, -⟩ := Wf_t.cons_inv (Ob.Entry.id_wf hne τ τ)
  constructor
  · apply Ob.Entry.id_wf hne τ τ
  · apply (Wf_s.single_iff τ.filler).mpr
    constructor
    · rintro _ _ ⟨⟩
      apply Eq_e.refl (Wf_bd.eq_left hid)
    · exact ⟨absurd trivial, absurd trivial⟩

/-- The filling `Subst.single τ.filler` of `Ob.Entry.id hne τ τ`. -/
def Ob.Fill.idRefl {X : Ob} {β : Bd (X.arity ⋈ 1)}
    {wβ : Ob.Tele.Wf X (dTel.cons .nil β .nil)} (hne : ¬ β.isEq)
    (τ : Ob.Fill X (Ob.Entry.mk 1 .nil β wβ).toTele) :
    Ob.Fill X (Ob.Entry.id hne τ τ).toTele :=
  ⟨_root_.Subst.single τ.filler, Ob.Entry.id_fill_wf hne τ⟩

/-- The class of `Ob.Entry.id not_false τ τ'` for representatives `τ` of `u` and
`τ'` of `u'`. -/
def IdSortOf (X : Ob)
    (u u' : Quotient (Ob.Fill.setoid (Ob.Entry.sort X).toTele)) : Ty₁ X :=
  Quotient.liftOn₂ u u'
    (fun τ τ' => Quotient.mk (Ob.Entry.setoid X)
      (Ob.Entry.id (β := Bd.sort) not_false τ τ'))
    (fun _ _ _ _ h h' => Quotient.sound (Ob.Entry.id_congr (β := Bd.sort) not_false h h'))

/-- The type asserting that the sorts `S` and `S'` are equal. -/
def IdSort {X : Ob} (S S' : Tm₁ X (U X)) : Ty₁ X :=
  IdSortOf X (Tm₁.fillEquiv (Ob.Entry.sort X) S)
    (Tm₁.fillEquiv (Ob.Entry.sort X) S')

/-- The term of `IdSort S S` given by `Ob.Fill.idRefl` on a filling representing
`S`. -/
def IdSort_refl {X : Ob} (S : Tm₁ X (U X)) : Tm₁ X (IdSort S S) :=
  Quotient.hrecOn (motive := fun u => Tm₁ X (IdSortOf X u u))
    (Tm₁.fillEquiv (Ob.Entry.sort X) S)
    (fun τ => Tm₁.ofFill (Ob.Fill.idRefl (β := Bd.sort) not_false τ))
    (by
      intro τ τ' h
      apply Tm₁.heq_of_eq
      obtain ⟨Γ⟩ := X
      obtain ⟨_, hid⟩ := Ob.Entry.id_congr (β := Bd.sort) not_false h h
      apply Quotient.sound
      use rfl, hid, hid.1, (Ob.Entry.id_fill_wf (β := Bd.sort) not_false τ).2
      exact Eq_s.cons (absurd trivial) Eq_s.nil)

/-- A type declaring an equation has at most one term. -/
theorem Tm₁.subsingleton
    {X : Ob} {u : Ob.Entry X} (h : u.declaration.isEq)
    (t t' : Tm₁ X (Quotient.mk (Ob.Entry.setoid X) u)) :
  t = t'
  := by
  obtain ⟨Γ⟩ := X
  induction t using Tm₁.ind with
  | _ τ =>
  induction t' using Tm₁.ind with
  | _ τ' =>
  apply Subtype.ext
  apply Quotient.sound
  use rfl, ⟨u.wf, Wf_t.refl u.wf⟩, u.wf, τ.2.2
  apply Eq_s.cons (absurd h) Eq_s.nil

/-- Any two terms of `IdSort S S'` are equal. -/
theorem IdSort_irrelevant
    {X : Ob} {S S' : Tm₁ X (U X)} (t t' : Tm₁ X (IdSort S S')) :
  t = t'
  := by
  induction S using Tm₁.ind with
  | _ τ =>
  induction S' using Tm₁.ind with
  | _ τ' =>
  apply Tm₁.subsingleton (u := Ob.Entry.id (β := Bd.sort) not_false τ τ') trivial

/-- If `IdSort S S'` has a term, then `S = S'`. -/
theorem IdSort_reflect
    {X : Ob} {S S' : Tm₁ X (U X)} (t : Tm₁ X (IdSort S S')) :
  S = S'
  := by
  induction S using Tm₁.ind with
  | _ τ =>
  induction S' using Tm₁.ind with
  | _ τ' =>
  induction t using Tm₁.ind with
  | _ ρ =>
  obtain ⟨Γ⟩ := X
  have hρ : Wf_s Γ.ambient (dTel.cons .nil (.eq τ.filler τ'.filler) .nil)
      (Subst.single ρ.filler) := by
    convert ρ.2.2
    apply Subst.single_eta
  obtain ⟨heq, -, -⟩ := (Wf_s.single_iff ρ.filler).mp hρ
  apply Subtype.ext
  apply Quotient.sound
  use rfl, ⟨τ.2.1, Wf_t.refl τ.2.1⟩, τ.2.1, τ.2.2
  apply Eq_s.cons (fun _ => heq _ _ rfl) Eq_s.nil

/-- Reindexing `IdSort S S'` along `σ` gives `IdSort` of `S` and `S'` reindexed
along `σ`. -/
theorem IdSort_subst
    {X Y : Ob} (S S' : Tm₁ X (U X)) (σ : Y ⟶ X) :
  (IdSort S S').subst σ
    = IdSort (U_subst σ ▸ S.subst σ) (U_subst σ ▸ S'.subst σ)
  := by
  induction σ using Quotient.ind with
  | _ σ =>
  induction S using Tm₁.ind with
  | _ τ =>
  induction S' using Tm₁.ind with
  | _ τ' =>
  rfl

/-- The type of elements of the sort a class of fillings supplies. -/
def ElOf (X : Ob) (u : Quotient (Ob.Fill.setoid (Ob.Entry.sort X).toTele)) :
    Ty₁ X :=
  Quotient.liftOn u (fun τ => Quotient.mk (Ob.Entry.setoid X) (Ob.Entry.of τ))
    (fun _ _ h => Quotient.sound (Ob.Entry.of_congr h))

/-- The class of `Ob.Entry.id not_false ρ ρ'` for representatives `ρ` of `v` and
`ρ'` of `v'`. -/
def IdOfEntry (X : Ob) (τ : Ob.Fill X (Ob.Entry.sort X).toTele)
    (v v' : Quotient (Ob.Fill.setoid (Ob.Entry.of τ).toTele)) : Ty₁ X :=
  Quotient.liftOn₂ v v'
    (fun ρ ρ' => Quotient.mk (Ob.Entry.setoid X)
      (Ob.Entry.id (β := Bd.of τ.filler) not_false ρ ρ'))
    (fun _ _ _ _ h h' =>
      Quotient.sound (Ob.Entry.id_congr (β := Bd.of τ.filler) not_false h h'))

/-- The type asserting that two terms of `ElOf X u` are equal: `IdOfEntry X τ` of
their classes of fillings, for a representative `τ` of `u`. -/
def IdElementOf (X : Ob)
    (u : Quotient (Ob.Fill.setoid (Ob.Entry.sort X).toTele)) :
    Tm₁ X (ElOf X u) → Tm₁ X (ElOf X u) → Ty₁ X :=
  Quotient.hrecOn (motive := fun u => Tm₁ X (ElOf X u) → Tm₁ X (ElOf X u) → Ty₁ X)
    u
    (fun τ l r => IdOfEntry X τ (Tm₁.fillEquiv (Ob.Entry.of τ) l)
      (Tm₁.fillEquiv (Ob.Entry.of τ) r))
    (by
      intro τ τ' h
      have hE := Quotient.sound (s := Ob.Entry.setoid X) (Ob.Entry.of_congr h)
      apply Function.hfunext (congrArg (Tm₁ X) hE)
      intro l l' hl
      apply Function.hfunext (congrArg (Tm₁ X) hE)
      intro r r' hr
      apply heq_of_eq
      induction l using Tm₁.ind with
      | _ ρ =>
      induction l' using Tm₁.ind with
      | _ ρ' =>
      induction r using Tm₁.ind with
      | _ ν =>
      induction r' using Tm₁.ind with
      | _ ν' =>
      obtain ⟨Γ⟩ := X
      obtain ⟨_, _, -, -, hρ⟩ := Quotient.exact (Tm₁.eq_of_heq hE hl)
      obtain ⟨_, _, -, -, hν⟩ := Quotient.exact (Tm₁.eq_of_heq hE hr)
      apply Quotient.sound
      use rfl, Ob.Entry.id_wf (β := Bd.of τ.filler) not_false ρ ν
      apply Eq_t.cons Eq_t.nil _ Eq_t.nil
      apply Eq_bd.eq
      · apply hρ.slot (C.inl (C.singleSlot 1)) not_false
      · apply hν.slot (C.inl (C.singleSlot 1)) not_false)

/-- The type asserting that the elements `l` and `r` of `El S` are equal. -/
def IdElement {X : Ob} {S : Tm₁ X (U X)} (l r : Tm₁ X (El S)) : Ty₁ X :=
  IdElementOf X (Tm₁.fillEquiv (Ob.Entry.sort X) S) l r

/-- Any two terms of `IdElement l r` are equal. -/
theorem IdElement_irrelevant
    {X : Ob} {S : Tm₁ X (U X)} {l r : Tm₁ X (El S)}
    (t t' : Tm₁ X (IdElement l r)) :
  t = t'
  := by
  induction S using Tm₁.ind with
  | _ τ =>
  induction l using Tm₁.ind with
  | _ ρ =>
  induction r using Tm₁.ind with
  | _ ν =>
  apply Tm₁.subsingleton (u := Ob.Entry.id (β := Bd.of τ.filler) not_false ρ ν) trivial

/-- If `IdElement l r` has a term, then `l = r`. -/
theorem IdElement_reflect
    {X : Ob} {S : Tm₁ X (U X)} {l r : Tm₁ X (El S)}
    (t : Tm₁ X (IdElement l r)) :
  l = r
  := by
  induction S using Tm₁.ind with
  | _ τ =>
  induction l using Tm₁.ind with
  | _ ρ =>
  induction r using Tm₁.ind with
  | _ ν =>
  induction t using Tm₁.ind with
  | _ κ =>
  obtain ⟨Γ⟩ := X
  have hκ : Wf_s Γ.ambient (dTel.cons .nil (.eq ρ.filler ν.filler) .nil)
      (Subst.single κ.filler) := by
    convert κ.2.2
    apply Subst.single_eta
  obtain ⟨heq, -, -⟩ := (Wf_s.single_iff κ.filler).mp hκ
  apply Subtype.ext
  apply Quotient.sound
  use rfl, ⟨ρ.2.1, Wf_t.refl ρ.2.1⟩, ρ.2.1, ρ.2.2
  apply Eq_s.cons (fun _ => heq _ _ rfl) Eq_s.nil

/-- The term of `IdElement l l` given by `Ob.Fill.idRefl` on a filling
representing `l`. -/
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
        apply Tm₁.heq_of_eq
        obtain ⟨Γ⟩ := X
        obtain ⟨_, hid⟩ := Ob.Entry.id_congr (β := Bd.of τ.filler) not_false h h
        apply Quotient.sound
        use rfl, hid, hid.1, (Ob.Entry.id_fill_wf (β := Bd.of τ.filler) not_false ρ).2
        exact Eq_s.cons (absurd trivial) Eq_s.nil))
    (by
      intro τ τ' h
      have hE := Quotient.sound (s := Ob.Entry.setoid X) (Ob.Entry.of_congr h)
      apply Function.hfunext (congrArg (Tm₁ X) hE)
      intro l l' hl
      apply Tm₁.heq_of_eq
      induction l using Tm₁.ind with
      | _ ρ =>
      induction l' using Tm₁.ind with
      | _ ρ' =>
      obtain ⟨Γ⟩ := X
      obtain ⟨_, _, -, -, hρ⟩ := Quotient.exact (Tm₁.eq_of_heq hE hl)
      have hid := Ob.Entry.id_wf (β := Bd.of τ.filler) not_false ρ ρ
      have hρρ := hρ.slot (C.inl (C.singleSlot 1)) not_false
      apply Quotient.sound
      use rfl, ⟨hid, Eq_t.cons Eq_t.nil (Eq_bd.eq hρρ hρρ) Eq_t.nil⟩, hid,
        (Ob.Entry.id_fill_wf (β := Bd.of τ.filler) not_false ρ).2
      exact Eq_s.cons (absurd trivial) Eq_s.nil)
    l

/-- Reindexing `IdElement l r` along `σ` gives `IdElement` of `l` and `r`
reindexed along `σ`. -/
theorem IdElement_subst
    {X Y : Ob} {S : Tm₁ X (U X)} (l r : Tm₁ X (El S)) (σ : Y ⟶ X) :
  (IdElement l r).subst σ
    = IdElement (El_subst S σ ▸ l.subst σ) (El_subst S σ ▸ r.subst σ)
  := by
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
