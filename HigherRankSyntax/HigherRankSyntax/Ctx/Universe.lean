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
    apply Wf_t.cons Wf_t.nil Wf_bd.sort Wf_t.nil

/-- The type of sorts. -/
def U (X : Ob) : Ty₁ X :=
  Quotient.mk (Ob.Entry.setoid X) (Ob.Entry.sort X)

/-- The type of sorts is stable under reindexing. -/
theorem U_subst {X Y : Ob} (σ : X ⟶ Y) :
  (U Y).subst σ = U X
  := by
  obtain ⟨σ⟩ := σ
  rfl

/-- The one-entry telescope declaring an element of the sort a filling supplies
is well formed. -/
theorem Ob.Fill.filler_wf {X : Ob} (τ : Ob.Fill X (Ob.Entry.sort X).toTele) :
  Ob.Tele.Wf X (dTel.cons .nil (.of τ.filler) .nil)
  := by
  obtain ⟨Γ⟩ := X
  apply Wf_t.cons Wf_t.nil _ Wf_t.nil
  apply Wf_bd.of
  · apply Wf_s.filler τ.2.2 (C.inl (C.singleSlot 1)) not_false
  · apply Wf_s.declared τ.2.2 (C.inl (C.singleSlot 1)) not_false

/-- The entry binding nothing and declaring an element of the sort a filling
supplies. -/
def Ob.Entry.of {X : Ob} (τ : Ob.Fill X (Ob.Entry.sort X).toTele) : Ob.Entry X where
  arity := 1
  binding := .nil
  declaration := .of τ.filler
  wf := τ.filler_wf

/-- Related fillings give related entries declaring an element of the sort they
supply. -/
theorem Ob.Entry.of_congr
    {X : Ob} {τ τ' : Ob.Fill X (Ob.Entry.sort X).toTele} (h : Ob.Fill.Rel τ τ') :
  Ob.Entry.Rel (Ob.Entry.of τ) (Ob.Entry.of τ')
  := by
  obtain ⟨Γ⟩ := X
  obtain ⟨-, -, hs⟩ := h
  use rfl, τ.filler_wf
  apply Eq_t.cons Eq_t.nil _ Eq_t.nil
  apply Eq_bd.of
  apply Eq_s.slot hs (C.inl (C.singleSlot 1)) not_false

/-- The type of elements of a sort. -/
def El {X : Ob} (S : Tm₁ X (U X)) : Ty₁ X :=
  Quotient.liftOn (Tm₁.fillEquiv (Ob.Entry.sort X) S)
    (fun τ => Quotient.mk (Ob.Entry.setoid X) (Ob.Entry.of τ))
    (fun _ _ h => Quotient.sound (Ob.Entry.of_congr h))

/-- Reindexing the type of elements of a sort is taking the elements of the
reindexed sort. -/
theorem El_subst {X Y : Ob} (S : Tm₁ Y (U Y)) (σ : X ⟶ Y) :
  (El S).subst σ = El (U_subst σ ▸ S.subst σ)
  := by
  obtain ⟨σ⟩ := σ
  induction S using Tm₁.ind with
  | ofFill τ => rfl

end Ctx
