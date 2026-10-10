import HigherRankSyntax.Ctx.Generation

/-!
# Inversion

Two one-entry telescopes whose slots bind nonempty telescopes are equal only if their first
bound entries are equal and the rest are equal over the extension by the first.
Consequently `Bind` determines its two arguments. `Bind` is never `U`, `El`, `IdSort` or
`IdElement`, since the entries of these bind nothing; `U` and `IdSort` are neither `El` nor
`IdElement`.

The class of an entry binding a nonempty telescope is `Bind` of the class of its first bound
entry and the class of the rest; the class of an entry binding nothing and declaring an
element of a sort, or an equation between two elements of a sort, is `El` or `IdElement` of
the terms given by the fillings of its expressions.
-/

open CategoryTheory

namespace Ctx

/-- If the one-entry telescopes whose slots bind `dTel.cons Θ β Ψ` and `dTel.cons Θ' β' Ψ'`
and declare `ε` and `ε'` are equal over `A`, then `dTel.cons Θ β .nil` and
`dTel.cons Θ' β' .nil` are equal over `A`, and `dTel.cons Ψ ε .nil` and
`dTel.cons Ψ' ε' .nil` are equal over `A ⋈ dTel.cons Θ β .nil`. -/
theorem bind_eq_inv
    {Ω γ δ : C.Arity} {A : Ambient Ω} {Θ Θ' : dTel Ω γ} {β β' : Bd (Ω ⋈ γ)}
    {Ψ Ψ' : dTel (Ω ⋈ (C.single γ ⋈ 1)) δ} {ε ε' : Bd ((Ω ⋈ (C.single γ ⋈ 1)) ⋈ δ)}
    (h : Eq_t A (dTel.cons (dTel.cons Θ β Ψ) ε .nil)
      (dTel.cons (dTel.cons Θ' β' Ψ') ε' .nil)) :
  Eq_t A (dTel.cons Θ β .nil) (dTel.cons Θ' β' .nil) ∧
    Eq_t (A ⋈ dTel.cons Θ β .nil) (dTel.cons Ψ ε .nil) (dTel.cons Ψ' ε' .nil)
  := by
  obtain ⟨_, _, _, ⟨⟩, hbind, hε, -⟩ := Eq_t.cons_inv h
  obtain ⟨_, _, _, ⟨⟩, hΘ, hβ, hΨ⟩ := Eq_t.cons_inv hbind
  constructor
  · apply Eq_t.cons hΘ hβ Eq_t.nil
  · apply Eq_t.cons hΨ _ Eq_t.nil
    rw [dTel.concatenate_assoc]
    apply hε

/-- `Bind a c` determines `a` and `c`. -/
theorem Bind_injective {X : Ob} {a a' : Ty₁ X} {c : Ty₁ (Ob.extend X a.toTy)}
    {c' : Ty₁ (Ob.extend X a'.toTy)} (h : Bind a c = Bind a' c') :
  a = a' ∧ HEq c c'
  := by
  induction X using Ob.ind with
  | h Γ =>
  induction a using Quotient.ind with
  | _ e =>
  induction a' using Quotient.ind with
  | _ e' =>
  induction c using Quotient.ind with
  | _ f =>
  induction c' using Quotient.ind with
  | _ f' =>
  obtain ⟨γ, Θ, β, w⟩ := e
  obtain ⟨γ', Θ', β', w'⟩ := e'
  obtain ⟨δ, Ψ, ε, wf⟩ := f
  obtain ⟨δ', Ψ', ε', wf'⟩ := f'
  obtain ⟨hΩ, -, heq⟩ := Quotient.exact h
  obtain ⟨rfl, rfl⟩ := C.single_mul_injective (C.single_injective hΩ)
  obtain ⟨hbase, hover⟩ := bind_eq_inv heq
  have ha : (Quotient.mk _ ⟨γ, Θ, β, w⟩ : Ty₁ Γ.toOb) = Quotient.mk _ ⟨γ, Θ', β', w'⟩ := by
    apply Quotient.sound
    use rfl
    constructor
    · apply w
    · apply hbase
  constructor
  · apply ha
  · apply Ty₁.heq_mk (Ty₁.extend_heq rfl (heq_of_eq ha))
    intro _
    constructor
    · apply Wf_t.ofEq (Eq_t.concatenate (Wf_t.refl Γ.wf) hbase) wf
    · apply Eq_t.ofEq (Eq_t.concatenate (Wf_t.refl Γ.wf) hbase) wf hover

/-- `Bind a c` is not the class of an entry binding nothing. -/
theorem Bind_ne_mk {X : Ob} (a : Ty₁ X) (c : Ty₁ (Ob.extend X a.toTy)) (u : Ob.Entry X)
    (hu : u.arity = 1) :
  Bind a c ≠ Quotient.mk _ u
  := by
  induction X using Ob.ind with
  | h Γ =>
  induction a using Quotient.ind with
  | _ e =>
  induction c using Quotient.ind with
  | _ f =>
  intro h
  obtain ⟨hΩ, -⟩ := Quotient.exact h
  apply C.single_mul_ne_one (γ := e.arity) (δ := f.arity)
  rw [← hu]
  apply C.single_injective hΩ

theorem Bind_ne_U {X : Ob} (a : Ty₁ X) (c : Ty₁ (Ob.extend X a.toTy)) :
  Bind a c ≠ U X
  := by
  apply Bind_ne_mk a c
  rfl

theorem Bind_ne_El {X : Ob} (a : Ty₁ X) (c : Ty₁ (Ob.extend X a.toTy)) (S : Tm₁ X (U X)) :
  Bind a c ≠ El S
  := by
  induction S using Tm₁.ind with
  | ofFill τ =>
  apply Bind_ne_mk a c
  rfl

theorem Bind_ne_IdSort {X : Ob} (a : Ty₁ X) (c : Ty₁ (Ob.extend X a.toTy))
    (S S' : Tm₁ X (U X)) :
  Bind a c ≠ IdSort S S'
  := by
  induction S using Tm₁.ind with
  | ofFill τ =>
  induction S' using Tm₁.ind with
  | ofFill τ' =>
  apply Bind_ne_mk a c
  rfl

theorem Bind_ne_IdElement {X : Ob} (a : Ty₁ X) (c : Ty₁ (Ob.extend X a.toTy))
    {S : Tm₁ X (U X)} (l r : Tm₁ X (El S)) :
  Bind a c ≠ IdElement l r
  := by
  induction S using Tm₁.ind with
  | ofFill τ =>
  induction l using Tm₁.ind with
  | ofFill ρ =>
  induction r using Tm₁.ind with
  | ofFill ρ' =>
  apply Bind_ne_mk a c
  rfl

theorem U_ne_El {X : Ob} (S : Tm₁ X (U X)) :
  U X ≠ El S
  := by
  induction X using Ob.ind with
  | h Γ =>
  induction S using Tm₁.ind with
  | ofFill τ =>
  intro h
  obtain ⟨hΩ, -, heq⟩ := Quotient.exact h
  obtain ⟨_, _, _, ⟨⟩, -, hβ, -⟩ := Eq_t.cons_inv heq
  cases hβ

theorem U_ne_IdElement {X : Ob} {S : Tm₁ X (U X)} (l r : Tm₁ X (El S)) :
  U X ≠ IdElement l r
  := by
  induction X using Ob.ind with
  | h Γ =>
  induction S using Tm₁.ind with
  | ofFill τ =>
  induction l using Tm₁.ind with
  | ofFill ρ =>
  induction r using Tm₁.ind with
  | ofFill ρ' =>
  intro h
  obtain ⟨hΩ, -, heq⟩ := Quotient.exact h
  obtain ⟨_, _, _, ⟨⟩, -, hβ, -⟩ := Eq_t.cons_inv heq
  cases hβ

theorem IdSort_ne_El {X : Ob} (S S' S'' : Tm₁ X (U X)) :
  IdSort S S' ≠ El S''
  := by
  induction X using Ob.ind with
  | h Γ =>
  induction S using Tm₁.ind with
  | ofFill τ =>
  induction S' using Tm₁.ind with
  | ofFill τ' =>
  induction S'' using Tm₁.ind with
  | ofFill τ'' =>
  intro h
  obtain ⟨hΩ, -, heq⟩ := Quotient.exact h
  obtain ⟨_, _, _, ⟨⟩, -, hβ, -⟩ := Eq_t.cons_inv heq
  cases hβ

theorem IdSort_ne_IdElement {X : Ob} (S S' : Tm₁ X (U X)) {S'' : Tm₁ X (U X)}
    (l r : Tm₁ X (El S'')) :
  IdSort S S' ≠ IdElement l r
  := by
  induction X using Ob.ind with
  | h Γ =>
  induction S using Tm₁.ind with
  | ofFill τ =>
  induction S' using Tm₁.ind with
  | ofFill τ' =>
  induction S'' using Tm₁.ind with
  | ofFill τ'' =>
  induction l using Tm₁.ind with
  | ofFill ρ =>
  induction r using Tm₁.ind with
  | ofFill ρ' =>
  intro h
  obtain ⟨hΩ, -, heq⟩ := Quotient.exact h
  obtain ⟨_, _, _, ⟨⟩, -, hβ, -⟩ := Eq_t.cons_inv heq
  cases hβ with
  | eq hl _ =>
    obtain ⟨-, -, hτ⟩ := (Wf_s.single_iff τ.filler).mp (Subst.single_eta τ.1 ▸ τ.2.2)
    obtain ⟨-, -, hρ⟩ := (Wf_s.single_iff ρ.filler).mp (Subst.single_eta ρ.1 ▸ ρ.2.2)
    have hboundary := Eq_e.boundaryOf (Wf_t.concatenate Γ.wf Wf_t.nil) hl
    cases Eq_bd.trans (Eq_bd.symm (hτ not_false)) (Eq_bd.trans hboundary (hρ not_false))

/-- The class of the entry binding `dTel.cons Θ β Ψ` and declaring `ε` is `Bind` of the class
of the entry binding `Θ` and declaring `β`, and the class of the entry binding `Ψ` and
declaring `ε` over the extension by it. -/
theorem mk_cons {Γ : Ctx} {γ δ : C.Arity} {Θ : dTel Γ.arity γ} {β : Bd (Γ.arity ⋈ γ)}
    {Ψ : dTel (Γ.arity ⋈ (C.single γ ⋈ 1)) δ} {ε : Bd ((Γ.arity ⋈ (C.single γ ⋈ 1)) ⋈ δ)}
    (w : Wf_t Γ.ambient (dTel.cons (dTel.cons Θ β Ψ) ε .nil)) :
  (Quotient.mk _ ⟨_, dTel.cons Θ β Ψ, ε, w⟩ : Ty₁ Γ.toOb)
    = model.Bind (Quotient.mk (Ob.Entry.setoid Γ.toOb) ⟨_, Θ, β, (bind_wf_inv w).1⟩)
        (Quotient.mk _ ⟨_, Ψ, ε, (bind_wf_inv w).2⟩)
  := rfl

/-- The class of the entry binding nothing and declaring an element of `S` is `El` of the
term given by a filling of the entry declaring a sort whose filler is `S`. -/
theorem mk_of {Γ : Ctx} {S : Expr (Γ.arity ⋈ 1)}
    (w : Wf_t Γ.ambient (dTel.cons .nil (.of S) .nil))
    (τ : Ob.Fill Γ.toOb (Ob.Entry.sort Γ.toOb).toTele) (h : τ.filler = S) :
  (Quotient.mk _ ⟨1, .nil, .of S, w⟩ : Ty₁ Γ.toOb) = model.El (Tm₁.ofFill τ)
  := by
  subst h
  rfl

/-- The class of the entry binding nothing and declaring the equation between `l` and `r` is
`IdElement` of the terms given by fillings of the entry declaring an element of a sort whose
fillers are `l` and `r`. -/
theorem mk_eq {Γ : Ctx} {l r : Expr (Γ.arity ⋈ 1)}
    (w : Wf_t Γ.ambient (dTel.cons .nil (.eq l r) .nil))
    {τ : Ob.Fill Γ.toOb (Ob.Entry.sort Γ.toOb).toTele}
    (ρ ρ' : Ob.Fill Γ.toOb (Ob.Entry.of τ).toTele) (hl : ρ.filler = l) (hr : ρ'.filler = r) :
  (Quotient.mk _ ⟨1, .nil, .eq l r, w⟩ : Ty₁ Γ.toOb)
    = model.IdElement (S := Tm₁.ofFill τ) (Tm₁.ofFill ρ) (Tm₁.ofFill ρ')
  := by
  subst hl hr
  rfl

end Ctx
