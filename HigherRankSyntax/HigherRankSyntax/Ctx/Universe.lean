import HigherRankSyntax.Ctx.Single

/-!
# Sorts and their elements

The entries declaring a sort and declaring an element of a sort, and the types
they present.
-/

open CategoryTheory

namespace Ctx

/-- The entry binding nothing and declaring a sort. -/
def Ob.Entry.sort (X : Ob) : Ob.Entry X where
  arity := 1
  binding := .nil
  declaration := .sort
  wf := by
    obtain ⟨Γ⟩ := X
    exact Wf_t.cons Wf_t.nil Wf_bd.sort Wf_t.nil

/-- The type of sorts. -/
def U (X : Ob) : Ty₁ X :=
  Quotient.mk (Ob.Entry.setoid X) (Ob.Entry.sort X)

theorem U_subst {X Y : Ob} (σ : X ⟶ Y) : (U Y).subst σ = U X := by
  obtain ⟨σ⟩ := σ
  rfl

/-- The entry declaring an element of the sort a filling supplies is well
formed. -/
theorem Ob.Fill.filler_wf {X : Ob} (τ : Ob.Fill X (Ob.Entry.sort X).toTele) :
    Ob.Tele.Wf X (dTel.cons .nil (.of τ.filler) .nil) := by
  obtain ⟨Γ⟩ := X
  have hs : Wf_s Γ.ambient (dTel.cons .nil .sort .nil) τ.1 := τ.2.2
  have hb := dTel.binding_head_instantiate (.nil : dTel Γ.arity 1) .sort .nil τ.1
  have hd := dTel.declaration_head_instantiate (.nil : dTel Γ.arity 1) .sort .nil τ.1
  have hfill := Eq.mp (congrArg (fun T => Wf_e (Γ.ambient ⋈ T) τ.filler) hb)
    (hs.filler (C.inl (C.singleSlot 1)) (by rw [hd]; exact not_false))
  have hdecl := Eq.mp (congrArg₂ (fun T b => Eq_bd (Γ.ambient ⋈ T)
      ((Γ.ambient ⋈ T).boundaryOf τ.filler) b) hb hd)
    (hs.declared (C.inl (C.singleSlot 1)) (by rw [hd]; exact not_false))
  exact Wf_t.cons Wf_t.nil (Wf_bd.of hfill hdecl) Wf_t.nil

/-- The entry binding nothing and declaring an element of the sort a filling
supplies. -/
def Ob.Entry.of {X : Ob} (τ : Ob.Fill X (Ob.Entry.sort X).toTele) : Ob.Entry X where
  arity := 1
  binding := .nil
  declaration := .of τ.filler
  wf := τ.filler_wf

theorem Ob.Entry.of_congr {X : Ob} {τ τ' : Ob.Fill X (Ob.Entry.sort X).toTele}
    (h : Ob.Fill.Rel τ τ') : Ob.Entry.Rel (Ob.Entry.of τ) (Ob.Entry.of τ') := by
  obtain ⟨Γ⟩ := X
  obtain ⟨-, -, he⟩ := h
  have hs : Eq_s Γ.ambient (dTel.cons .nil .sort .nil) τ.1 τ'.1 := he
  have hb := dTel.binding_head_instantiate (.nil : dTel Γ.arity 1) .sort .nil τ.1
  have hd := dTel.declaration_head_instantiate (.nil : dTel Γ.arity 1) .sort .nil τ.1
  have hslot := Eq.mp (congrArg (fun T => Eq_e (Γ.ambient ⋈ T) τ.filler τ'.filler) hb)
    (hs.slot (C.inl (C.singleSlot 1)) (by rw [hd]; exact not_false))
  exact ⟨rfl, τ.filler_wf, Eq_t.cons Eq_t.nil (Eq_bd.of hslot) Eq_t.nil⟩

/-- The type of elements of a sort. -/
def El {X : Ob} (S : Tm₁ X (U X)) : Ty₁ X :=
  Quotient.liftOn (Tm₁.fillEquiv (Ob.Entry.sort X) S)
    (fun τ => Quotient.mk (Ob.Entry.setoid X) (Ob.Entry.of τ))
    (fun _ _ h => by exact Quotient.sound (Ob.Entry.of_congr h))

theorem El_ofFill {X : Ob} (τ : Ob.Fill X (Ob.Entry.sort X).toTele) :
    El (Tm₁.ofFill τ) = Quotient.mk (Ob.Entry.setoid X) (Ob.Entry.of τ) :=
  rfl

theorem El_subst {X Y : Ob} (S : Tm₁ Y (U Y)) (σ : X ⟶ Y) :
    (El S).subst σ = El (U_subst σ ▸ S.subst σ) := by
  obtain ⟨σ⟩ := σ
  refine Tm₁.ind (motive := fun S => (El S).subst (Quotient.mk _ σ)
    = El (U_subst (Quotient.mk _ σ) ▸ S.subst (Quotient.mk _ σ))) ?_ S
  intro τ
  rfl

end Ctx
