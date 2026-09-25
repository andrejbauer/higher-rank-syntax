import HigherRankSyntax.Ctx.Universe

/-!
# Binding

The entry whose slot takes the arguments of one entry and then those of an entry
over the extension, and declares what the latter declares.
-/

open CategoryTheory

namespace Ctx

/-- The telescope binding a telescope and then a telescope over its extension,
declaring what the latter declares, is well formed. -/
theorem bind_wf {Ω γ δ : C.Arity} {A : Ambient Ω} {Θ : dTel Ω γ} {β : Bd (Ω ⋈ γ)}
    {Ψ : dTel (Ω ⋈ (C.single γ ⋈ 1)) δ} {ε : Bd ((Ω ⋈ (C.single γ ⋈ 1)) ⋈ δ)}
    (hbase : Wf_t A (dTel.cons Θ β .nil))
    (hover : Wf_t (A ⋈ dTel.cons Θ β .nil) (dTel.cons Ψ ε .nil)) :
    Wf_t A (dTel.cons (dTel.cons Θ β Ψ) ε .nil) := by
  obtain ⟨hΘ, hβ, -⟩ := Wf_t.cons_inv hbase
  obtain ⟨hΨ, hε, -⟩ := Wf_t.cons_inv hover
  exact Wf_t.cons (Wf_t.cons hΘ hβ hΨ) (Wf_bd.concatenate hε) Wf_t.nil

/-- The telescopes binding equal telescopes and then equal telescopes over their
extensions are equal. -/
theorem bind_eq {Ω γ δ : C.Arity} {A : Ambient Ω} {Θ Θ' : dTel Ω γ}
    {β β' : Bd (Ω ⋈ γ)} {Ψ Ψ' : dTel (Ω ⋈ (C.single γ ⋈ 1)) δ}
    {ε ε' : Bd ((Ω ⋈ (C.single γ ⋈ 1)) ⋈ δ)}
    (hbase : Eq_t A (dTel.cons Θ β .nil) (dTel.cons Θ' β' .nil))
    (hover : Eq_t (A ⋈ dTel.cons Θ β .nil) (dTel.cons Ψ ε .nil)
      (dTel.cons Ψ' ε' .nil)) :
    Eq_t A (dTel.cons (dTel.cons Θ β Ψ) ε .nil)
      (dTel.cons (dTel.cons Θ' β' Ψ') ε' .nil) := by
  obtain ⟨_, _, _, hc, hΘ, hβ, -⟩ := Eq_t.cons_inv hbase
  injection hc with _ _ _ h₁ h₂ _
  subst h₁
  subst h₂
  obtain ⟨_, _, _, hd, hΨ, hε, -⟩ := Eq_t.cons_inv hover
  injection hd with _ _ _ k₁ k₂ _
  subst k₁
  subst k₂
  refine Eq_t.cons (Eq_t.cons hΘ hβ hΨ) ?_ Eq_t.nil
  exact Eq.mp (congrArg (fun T => Eq_bd T ε ε')
    (dTel.concatenate_assoc A (dTel.cons Θ β .nil) Ψ)) hε

/-- Reindexing the telescope of a bound entry reindexes the two entries it binds,
the second past the first. -/
theorem bind_actBase {Ω Ω' γ δ : C.Arity} (σ : Subst Ω Ω') {Θ : dTel Ω γ}
    {β : Bd (Ω ⋈ γ)} {Ψ : dTel (Ω ⋈ (C.single γ ⋈ 1)) δ}
    {ε : Bd ((Ω ⋈ (C.single γ ⋈ 1)) ⋈ δ)} :
    dTel.actBase σ (dTel.cons (dTel.cons Θ β Ψ) ε .nil)
      = dTel.cons (dTel.cons (dTel.actBase σ Θ) (Bd.act (Γ := 1) σ γ β)
          (dTel.actBase (Subst.lift σ (C.single γ ⋈ 1)) Ψ))
          (Bd.act (Γ := 1) (Δ := Ω ⋈ (C.single γ ⋈ 1)) (Ξ := Ω' ⋈ (C.single γ ⋈ 1))
            (Subst.lift σ (C.single γ ⋈ 1)) δ ε) .nil :=
  congrArg (fun b => dTel.cons (dTel.cons (dTel.actBase σ Θ) (Bd.act (Γ := 1) σ γ β)
      (dTel.actBase (Subst.lift σ (C.single γ ⋈ 1)) Ψ)) b .nil)
    (Bd.act_lift σ (C.single γ) δ ε).symm

/-- A filling of the entry over an extension is a filling of the bound entry. -/
theorem lam_wf_iff {Ω γ δ : C.Arity} {A : Ambient Ω} {Θ : dTel Ω γ}
    {β : Bd (Ω ⋈ γ)} {Ψ : dTel (Ω ⋈ (C.single γ ⋈ 1)) δ}
    {ε : Bd ((Ω ⋈ (C.single γ ⋈ 1)) ⋈ δ)}
    (t : Expr ((Ω ⋈ (C.single γ ⋈ 1)) ⋈ δ)) :
    Wf_s (A ⋈ dTel.cons Θ β .nil) (dTel.cons Ψ ε .nil)
        (Subst.single (Δ := Ω ⋈ (C.single γ ⋈ 1)) (α := δ) t)
      ↔ Wf_s A (dTel.cons (dTel.cons Θ β Ψ) ε .nil)
        (Subst.single (Δ := Ω) (α := C.single γ ⋈ δ) t) := by
  rw [Wf_s.single_iff, Wf_s.single_iff, dTel.concatenate_assoc]
  exact Iff.rfl

/-- Two fillings of the entry over an extension agree exactly when they agree as
fillings of the bound entry. -/
theorem lam_eq_iff {Ω γ δ : C.Arity} {A : Ambient Ω} {Θ : dTel Ω γ}
    {β : Bd (Ω ⋈ γ)} {Ψ : dTel (Ω ⋈ (C.single γ ⋈ 1)) δ}
    {ε : Bd ((Ω ⋈ (C.single γ ⋈ 1)) ⋈ δ)}
    (t t' : Expr ((Ω ⋈ (C.single γ ⋈ 1)) ⋈ δ)) :
    Eq_s (A ⋈ dTel.cons Θ β .nil) (dTel.cons Ψ ε .nil)
        (Subst.single (Δ := Ω ⋈ (C.single γ ⋈ 1)) (α := δ) t)
        (Subst.single (Δ := Ω ⋈ (C.single γ ⋈ 1)) (α := δ) t')
      ↔ Eq_s A (dTel.cons (dTel.cons Θ β Ψ) ε .nil)
        (Subst.single (Δ := Ω) (α := C.single γ ⋈ δ) t)
        (Subst.single (Δ := Ω) (α := C.single γ ⋈ δ) t') := by
  rw [Eq_s.single_iff, Eq_s.single_iff, dTel.concatenate_assoc]
  exact Iff.rfl

/-- The entry binding what an entry binds and then what an entry over the
extension binds, declaring what the latter declares. -/
def bind (Γ : Ctx) (e : Ob.Entry Γ.toOb) (f : Ob.Entry (Ctx.extend Γ e.toTele)) :
    Ob.Entry Γ.toOb where
  arity := C.single e.arity ⋈ f.arity
  binding := dTel.cons e.binding e.declaration f.binding
  declaration := f.declaration
  wf := bind_wf e.wf f.wf

theorem bind_congr_right (Γ : Ctx) (e : Ob.Entry Γ.toOb)
    {f f' : Ob.Entry (Ctx.extend Γ e.toTele)} (h : Ob.Entry.Rel f f') :
    Ob.Entry.Rel (bind Γ e f) (bind Γ e f') := by
  obtain ⟨γ, Θ, β, w⟩ := e
  obtain ⟨δ, Ψ, ε, wf⟩ := f
  obtain ⟨δ', Ψ', ε', wf'⟩ := f'
  obtain ⟨ha, -, heq⟩ := h
  have ha' : C.single δ = C.single δ' := ha
  obtain rfl := C.single_injective ha'
  obtain ⟨Ψ'', ε'', r'', hcons, hbind, hbd, -⟩ := Eq_t.cons_inv heq
  injection hcons with _ _ _ h₁ h₂ _
  subst h₁
  subst h₂
  obtain ⟨hΘ, hβ, -⟩ := Wf_t.cons_inv w
  refine ⟨rfl, (bind Γ ⟨γ, Θ, β, w⟩ ⟨δ, Ψ, ε, wf⟩).wf, ?_⟩
  refine Eq_t.cons (Eq_t.cons (Wf_t.refl hΘ) (Wf_bd.refl hβ) hbind) ?_ Eq_t.nil
  exact Eq.mp (congrArg (fun A => Eq_bd A ε ε')
    (dTel.concatenate_assoc Γ.ambient (dTel.cons Θ β .nil) Ψ)) hbd

theorem bind_congr (Γ : Ctx) {e e' : Ob.Entry Γ.toOb} (he : Ob.Entry.Rel e e')
    {f : Ob.Entry (Ctx.extend Γ e.toTele)} {f' : Ob.Entry (Ctx.extend Γ e'.toTele)}
    (harity : f.arity = f'.arity) (hbinding : HEq f.binding f'.binding)
    (hdeclaration : HEq f.declaration f'.declaration) :
    Ob.Entry.Rel (bind Γ e f) (bind Γ e' f') := by
  obtain ⟨γ, Θ, β, w⟩ := e
  obtain ⟨γ', Θ', β', w'⟩ := e'
  obtain ⟨ha, -, heq⟩ := he
  have ha' : C.single γ = C.single γ' := ha
  obtain rfl := C.single_injective ha'
  obtain ⟨Θ'', β'', r'', hcons, hbind, hbd, -⟩ := Eq_t.cons_inv heq
  injection hcons with _ _ _ h₁ h₂ _
  subst h₁
  subst h₂
  obtain ⟨δ, Ψ, ε, wf⟩ := f
  obtain ⟨δ', Ψ', ε', wf'⟩ := f'
  obtain rfl := harity
  obtain rfl := eq_of_heq hbinding
  obtain rfl := eq_of_heq hdeclaration
  obtain ⟨hΨ, hε, -⟩ := Wf_t.cons_inv wf
  refine ⟨rfl, (bind Γ ⟨γ, Θ, β, w⟩ ⟨δ, Ψ, ε, wf⟩).wf, ?_⟩
  exact Eq_t.cons (Eq_t.cons hbind hbd (Wf_t.refl hΨ))
    (Wf_bd.refl (Wf_bd.concatenate hε)) Eq_t.nil

/-- The type binding a type over a context and a type over its extension. -/
def bindEntry (Γ : Ctx) :
    (a : Ty₁ Γ.toOb) → Ty₁ (Ob.extend Γ.toOb a.toTy) → Ty₁ Γ.toOb :=
  fun a => Quotient.hrecOn
    (motive := fun (a : Ty₁ Γ.toOb) =>
      Ty₁ (Ob.extend Γ.toOb (Ty₁.toTy a)) → Ty₁ Γ.toOb) a
    (fun e c => Quotient.liftOn c
      (fun f => Quotient.mk (Ob.Entry.setoid Γ.toOb) (bind Γ e f))
      (fun _ _ h => by exact Quotient.sound (bind_congr_right Γ e h)))
    (by
      intro e e' he
      have hZ : Ctx.extend Γ e.toTele = Ctx.extend Γ e'.toTele :=
        congrArg (Ob.extend Γ.toOb) (Quotient.sound he)
      refine Function.hfunext (congrArg Ty₁ hZ) ?_
      intro c c' hc
      apply heq_of_eq
      obtain ⟨f⟩ := c
      obtain rfl : cast (congrArg Ty₁ hZ) (Quotient.mk (Ob.Entry.setoid _) f) = c' :=
        cast_eq_iff_heq.mpr hc
      rw [Ty₁.mk_cast]
      · exact Quotient.sound (bind_congr Γ he (Ob.Entry.arity_cast hZ f).symm
          (Ob.Entry.binding_cast hZ f).symm (Ob.Entry.declaration_cast hZ f).symm)
      · exact hZ)

/-- The type whose slot takes the arguments of a type and then those of a type
over its extension, and declares what the latter declares. -/
def Bind {X : Ob} (a : Ty₁ X) (c : Ty₁ (Ob.extend X a.toTy)) : Ty₁ X :=
  Quotient.hrecOn
    (motive := fun X => (a : Ty₁ X) → Ty₁ (Ob.extend X (Ty₁.toTy a)) → Ty₁ X)
    X bindEntry
    (by
      intro Γ Γ' hΓ
      have hX : Γ.toOb = Γ'.toOb := Quotient.sound hΓ
      refine Function.hfunext (congrArg Ty₁ hX) ?_
      intro a a' ha
      refine Function.hfunext (congrArg Ty₁ (Ty₁.extend_heq hX ha)) ?_
      intro c c' hc
      obtain ⟨Ω, A, hA⟩ := Γ
      obtain ⟨Ω', A', hA'⟩ := Γ'
      obtain ⟨rfl, -⟩ := hΓ
      obtain ⟨e⟩ := a
      obtain ⟨e'⟩ := a'
      obtain ⟨γ, Θ, β, w⟩ := e
      obtain ⟨γ', Θ', β', w'⟩ := e'
      obtain ⟨rfl, hea⟩ := Ty₁.eq_of_heq_mk hX ha
      obtain ⟨f⟩ := c
      obtain ⟨f'⟩ := c'
      obtain ⟨δ, Ψ, ε, wΨ⟩ := f
      obtain ⟨δ', Ψ', ε', wΨ'⟩ := f'
      obtain ⟨rfl, hef⟩ := Ty₁.eq_of_heq_mk (Ty₁.extend_heq hX ha) hc
      obtain ⟨hwa, heqa⟩ := hea rfl
      obtain ⟨hwf, heqf⟩ := hef rfl
      have hmove : Eq_t (.nil : Ambient 1) (A' ⋈ dTel.cons Θ' β' .nil)
          (A' ⋈ dTel.cons Θ β .nil) :=
        Eq_t.concatenate (Wf_t.refl hA') (Eq_t.symm hA' heqa)
      refine Ty₁.heq_mk hX ?_
      intro _
      exact ⟨bind_wf hwa (Wf_t.ofEq hmove hwf),
        bind_eq heqa (Eq_t.ofEq hmove hwf heqf)⟩)
    a c

theorem Bind_mk (Γ : Ctx) (e : Ob.Entry Γ.toOb) (f : Ob.Entry (Ctx.extend Γ e.toTele)) :
    Bind (Quotient.mk (Ob.Entry.setoid Γ.toOb) e)
        (Quotient.mk (Ob.Entry.setoid (Ctx.extend Γ e.toTele)) f)
      = Quotient.mk (Ob.Entry.setoid Γ.toOb) (bind Γ e f) :=
  rfl

/-! ## Abstraction -/

/-- The filling of a bound entry supplying what a filling of the entry over the
extension supplies. -/
def lamFill (Γ : Ctx) (e : Ob.Entry Γ.toOb) (f : Ob.Entry (Ctx.extend Γ e.toTele))
    (τ : Ob.Fill (Ctx.extend Γ e.toTele) f.toTele) :
    Ob.Fill Γ.toOb (bind Γ e f).toTele :=
  ⟨Subst.single τ.filler, (bind Γ e f).wf,
    (lam_wf_iff τ.filler).mp
      (Eq.mp (congrArg (fun σ => Wf_s (Γ.ambient ⋈ e.toTele.telescope)
        f.toTele.telescope σ) (Subst.single_eta τ.1).symm) τ.2.2)⟩

/-- The filling of the entry over an extension supplying what a filling of the
bound entry supplies. -/
def unlamFill (Γ : Ctx) (e : Ob.Entry Γ.toOb) (f : Ob.Entry (Ctx.extend Γ e.toTele))
    (τ : Ob.Fill Γ.toOb (bind Γ e f).toTele) :
    Ob.Fill (Ctx.extend Γ e.toTele) f.toTele :=
  ⟨Subst.single τ.filler, f.wf,
    (lam_wf_iff τ.filler).mpr
      (Eq.mp (congrArg (fun σ => Wf_s Γ.ambient (bind Γ e f).toTele.telescope σ)
        (Subst.single_eta τ.1).symm) τ.2.2)⟩

theorem unlamFill_lamFill (Γ : Ctx) (e : Ob.Entry Γ.toOb)
    (f : Ob.Entry (Ctx.extend Γ e.toTele))
    (τ : Ob.Fill (Ctx.extend Γ e.toTele) f.toTele) :
    unlamFill Γ e f (lamFill Γ e f τ) = τ :=
  Subtype.ext ((congrArg Subst.single (Subst.single_head τ.filler)).trans
    (Subst.single_eta τ.1))

theorem lamFill_unlamFill (Γ : Ctx) (e : Ob.Entry Γ.toOb)
    (f : Ob.Entry (Ctx.extend Γ e.toTele))
    (τ : Ob.Fill Γ.toOb (bind Γ e f).toTele) :
    lamFill Γ e f (unlamFill Γ e f τ) = τ :=
  Subtype.ext ((congrArg Subst.single (Subst.single_head τ.filler)).trans
    (Subst.single_eta τ.1))

/-- 13.1: the fillings of the entry over an extension are the fillings of the
bound entry. -/
def lamFillEquiv (Γ : Ctx) (e : Ob.Entry Γ.toOb)
    (f : Ob.Entry (Ctx.extend Γ e.toTele)) :
    Ob.Fill (Ctx.extend Γ e.toTele) f.toTele ≃ Ob.Fill Γ.toOb (bind Γ e f).toTele where
  toFun := lamFill Γ e f
  invFun := unlamFill Γ e f
  left_inv := unlamFill_lamFill Γ e f
  right_inv := lamFill_unlamFill Γ e f

theorem lamFill_rel (Γ : Ctx) (e : Ob.Entry Γ.toOb)
    (f : Ob.Entry (Ctx.extend Γ e.toTele))
    (τ τ' : Ob.Fill (Ctx.extend Γ e.toTele) f.toTele) :
    Ob.Fill.Rel τ τ' ↔ Ob.Fill.Rel (lamFill Γ e f τ) (lamFill Γ e f τ') := by
  constructor
  · rintro ⟨-, -, heq⟩
    refine ⟨(bind Γ e f).wf, (lamFill Γ e f τ).2.2, ?_⟩
    refine (lam_eq_iff τ.filler τ'.filler).mp ?_
    exact Eq.mp (congrArg₂ (fun σ σ' => Eq_s (Γ.ambient ⋈ e.toTele.telescope)
        f.toTele.telescope σ σ')
      (Subst.single_eta τ.1).symm (Subst.single_eta τ'.1).symm) heq
  · rintro ⟨-, -, heq⟩
    refine ⟨f.wf, τ.2.2, ?_⟩
    refine Eq.mp (congrArg₂ (fun σ σ' => Eq_s (Γ.ambient ⋈ e.toTele.telescope)
        f.toTele.telescope σ σ')
      (Subst.single_eta τ.1) (Subst.single_eta τ'.1)) ?_
    exact (lam_eq_iff τ.filler τ'.filler).mpr heq

/-- 13.2: the terms of the entry over an extension are the terms of the bound
entry. -/
def bindEquiv (Γ : Ctx) (e : Ob.Entry Γ.toOb)
    (f : Ob.Entry (Ctx.extend Γ e.toTele)) :
    Tm₁ (Ctx.extend Γ e.toTele)
        (Quotient.mk (Ob.Entry.setoid (Ctx.extend Γ e.toTele)) f)
      ≃ Tm₁ Γ.toOb (Quotient.mk (Ob.Entry.setoid Γ.toOb) (bind Γ e f)) :=
  (Tm₁.fillEquiv f).trans
    ((Quotient.congr (lamFillEquiv Γ e f) (fun _ _ => lamFill_rel Γ e f _ _)).trans
      (Tm₁.fillEquiv (bind Γ e f)).symm)

theorem bindEquiv_ofFill (Γ : Ctx) (e : Ob.Entry Γ.toOb)
    (f : Ob.Entry (Ctx.extend Γ e.toTele))
    (τ : Ob.Fill (Ctx.extend Γ e.toTele) f.toTele) :
    bindEquiv Γ e f (Tm₁.ofFill τ) = Tm₁.ofFill (lamFill Γ e f τ) :=
  rfl

/-- 13.2 on a type class over an entry. -/
def bindEquivEntry (Γ : Ctx) (e : Ob.Entry Γ.toOb) :
    (c : Ty₁ (Ctx.extend Γ e.toTele)) →
      (Tm₁ (Ctx.extend Γ e.toTele) c
        ≃ Tm₁ Γ.toOb (Bind (Quotient.mk (Ob.Entry.setoid Γ.toOb) e) c)) :=
  fun c => Quotient.hrecOn
    (motive := fun (c : Ty₁ (Ctx.extend Γ e.toTele)) =>
      Tm₁ (Ctx.extend Γ e.toTele) c
        ≃ Tm₁ Γ.toOb (Bind (Quotient.mk (Ob.Entry.setoid Γ.toOb) e) c))
    c (bindEquiv Γ e)
    (by
      intro f f' h
      obtain ⟨δ, Ψ, ε, w⟩ := f
      obtain ⟨δ', Ψ', ε', w'⟩ := f'
      have hrel : Ob.Tele.Rel
          (⟨δ, Ψ, ε, w⟩ : Ob.Entry (Ctx.extend Γ e.toTele)).toTele
          (⟨δ', Ψ', ε', w'⟩ : Ob.Entry (Ctx.extend Γ e.toTele)).toTele := h
      have hδ : C.single δ = C.single δ' := Ob.Tele.Rel.arity hrel
      obtain rfl := C.single_injective hδ
      have hb := bind_congr_right Γ e hrel
      obtain ⟨hba, hbwf, hbeq⟩ := hb
      refine Equiv.heq_congr
        (congrArg (Tm₁ (Ctx.extend Γ e.toTele)) (Quotient.sound h))
        (congrArg (Tm₁ Γ.toOb) (Quotient.sound (bind_congr_right Γ e h))) ?_
      intro x x' hx
      refine Tm₁.heq_of_eq ?_
      have hval : x.1 = x'.1 := Tm₁.eq_of_heq (Quotient.sound h) hx
      revert hval
      refine Tm₁.ind (motive := fun x => x.1 = x'.1 →
        (bindEquiv Γ e ⟨δ, Ψ, ε, w⟩ x).1
          = (bindEquiv Γ e ⟨δ, Ψ', ε', w'⟩ x').1) ?_ x
      intro τ hval
      revert hval
      refine Tm₁.ind (motive := fun x' => (Tm₁.ofFill τ).1 = x'.1 →
        (bindEquiv Γ e ⟨δ, Ψ, ε, w⟩ (Tm₁.ofFill τ)).1
          = (bindEquiv Γ e ⟨δ, Ψ', ε', w'⟩ x').1) ?_ x'
      intro τ' hval
      have hf := Quotient.exact hval
      obtain ⟨hfa, hftele, hfill⟩ := hf
      refine Quotient.sound (Exists.intro
        (rfl : (bind Γ e ⟨δ, Ψ, ε, w⟩).toTele.arity
          = (bind Γ e ⟨δ, Ψ', ε', w'⟩).toTele.arity) ?_)
      refine ⟨⟨hbwf, hbeq⟩, (lamFill Γ e ⟨δ, Ψ, ε, w⟩ τ).2.1,
        (lamFill Γ e ⟨δ, Ψ, ε, w⟩ τ).2.2, ?_⟩
      refine (lam_eq_iff τ.filler τ'.filler).mp ?_
      exact Eq.mp (congrArg₂ (fun σ σ' => Eq_s (Γ.ambient ⋈ e.toTele.telescope)
          (dTel.cons Ψ ε .nil) σ σ')
        (Subst.single_eta τ.1).symm (Subst.single_eta τ'.1).symm) hfill.2.2)

theorem Bind_congr {X : Ob} {a a' : Ty₁ X} (ha : a = a')
    {c : Ty₁ (Ob.extend X a.toTy)} {c' : Ty₁ (Ob.extend X a'.toTy)} (hc : HEq c c') :
    Bind a c = Bind a' c' := by
  subst ha
  obtain rfl := eq_of_heq hc
  rfl

/-- 13.2 on a type class over a context. -/
def bindEquivObj (Γ : Ctx) :
    (a : Ty₁ Γ.toOb) → (c : Ty₁ (Ob.extend Γ.toOb (Ty₁.toTy a))) →
      (Tm₁ (Ob.extend Γ.toOb (Ty₁.toTy a)) c ≃ Tm₁ Γ.toOb (Bind a c)) :=
  fun a => Quotient.hrecOn
    (motive := fun (a : Ty₁ Γ.toOb) =>
      (c : Ty₁ (Ob.extend Γ.toOb (Ty₁.toTy a))) →
        (Tm₁ (Ob.extend Γ.toOb (Ty₁.toTy a)) c ≃ Tm₁ Γ.toOb (Bind a c)))
    a (bindEquivEntry Γ)
    (by
      intro e e' h
      obtain ⟨γ, Θ, β, w⟩ := e
      obtain ⟨γ', Θ', β', w'⟩ := e'
      have hrel : Ob.Tele.Rel (⟨γ, Θ, β, w⟩ : Ob.Entry Γ.toOb).toTele
          (⟨γ', Θ', β', w'⟩ : Ob.Entry Γ.toOb).toTele := h
      have hγ : C.single γ = C.single γ' := Ob.Tele.Rel.arity hrel
      obtain rfl := C.single_injective hγ
      obtain ⟨hγa, hewf, hbase⟩ := hrel
      have hZ : Ctx.extend Γ (⟨γ, Θ, β, w⟩ : Ob.Entry Γ.toOb).toTele
          = Ctx.extend Γ (⟨γ, Θ', β', w'⟩ : Ob.Entry Γ.toOb).toTele :=
        congrArg (Ob.extend Γ.toOb) (Quotient.sound h)
      have hamb : Eq_t (.nil : Ambient 1)
          (Γ.ambient ⋈ dTel.cons Θ' β' .nil) (Γ.ambient ⋈ dTel.cons Θ β .nil) :=
        Eq_t.concatenate (Wf_t.refl Γ.wf) (Eq_t.symm Γ.wf hbase)
      refine Function.hfunext (congrArg Ty₁ hZ) ?_
      intro c c' hc
      induction c using Quotient.ind with
      | _ f =>
      induction c' using Quotient.ind with
      | _ f' =>
      obtain ⟨δ, Ψ, ε, wf⟩ := f
      obtain ⟨δ', Ψ', ε', wf'⟩ := f'
      obtain ⟨rfl, hcrel⟩ := Ty₁.eq_of_heq_mk hZ hc
      refine Equiv.heq_congr (Tm₁.type_congr hZ hc)
        (congrArg (Tm₁ Γ.toOb) (Bind_congr (Quotient.sound h) hc)) ?_
      intro x x' hx
      refine Tm₁.heq_of_eq ?_
      revert hx
      refine Tm₁.ind (motive := fun x => HEq x x' →
        (bindEquiv Γ ⟨γ, Θ, β, w⟩ ⟨δ, Ψ, ε, wf⟩ x).1
          = (bindEquiv Γ ⟨γ, Θ', β', w'⟩ ⟨δ, Ψ', ε', wf'⟩ x').1) ?_ x
      intro τ hx
      revert hx
      refine Tm₁.ind (motive := fun x' => HEq (Tm₁.ofFill τ) x' →
        (bindEquiv Γ ⟨γ, Θ, β, w⟩ ⟨δ, Ψ, ε, wf⟩ (Tm₁.ofFill τ)).1
          = (bindEquiv Γ ⟨γ, Θ', β', w'⟩ ⟨δ, Ψ', ε', wf'⟩ x').1) ?_ x'
      intro τ' hx
      have hterm := Ob.Term.eq_of_heq_mk hZ (Tm₁.heq_val hZ hc hx) rfl
      have hover : Eq_t (Γ.ambient ⋈ dTel.cons Θ β .nil)
          (dTel.cons Ψ ε .nil) (dTel.cons Ψ' ε' .nil) :=
        Eq_t.ofEq hamb hterm.1.1 hterm.1.2
      refine Quotient.sound (Exists.intro
        (rfl : (bind Γ ⟨γ, Θ, β, w⟩ ⟨δ, Ψ, ε, wf⟩).toTele.arity
          = (bind Γ ⟨γ, Θ', β', w'⟩ ⟨δ, Ψ', ε', wf'⟩).toTele.arity) ?_)
      refine ⟨⟨(bind Γ ⟨γ, Θ, β, w⟩ ⟨δ, Ψ, ε, wf⟩).wf, bind_eq hbase hover⟩,
        (lamFill Γ ⟨γ, Θ, β, w⟩ ⟨δ, Ψ, ε, wf⟩ τ).2.1,
        (lamFill Γ ⟨γ, Θ, β, w⟩ ⟨δ, Ψ, ε, wf⟩ τ).2.2, ?_⟩
      have hboth := Eq_t.toBoth Eq_t.Both.nil hamb
      have hes : Eq_s (Γ.ambient ⋈ dTel.cons Θ β .nil) (dTel.cons Ψ ε .nil)
          τ.1 τ'.1 :=
        Eq_s.ofBoth hboth hterm.2.2.2 (Eq_t.Both.refl hboth hterm.2.1)
          hterm.2.2.1 (Wf_s.ofEq hamb hterm.2.2.1 (Wf_t.refl hterm.2.1))
      refine (lam_eq_iff τ.filler τ'.filler).mp ?_
      exact Eq.mp (congrArg₂ (fun σ σ' => Eq_s (Γ.ambient ⋈ dTel.cons Θ β .nil)
          (dTel.cons Ψ ε .nil) σ σ')
        (Subst.single_eta τ.1).symm (Subst.single_eta τ'.1).symm) hes)

theorem Bind_heq {X X' : Ob} (hX : X = X') {a : Ty₁ X} {a' : Ty₁ X'} (ha : HEq a a')
    {c : Ty₁ (Ob.extend X a.toTy)} {c' : Ty₁ (Ob.extend X' a'.toTy)} (hc : HEq c c') :
    HEq (Bind a c) (Bind a' c') := by
  subst hX
  obtain rfl := eq_of_heq ha
  obtain rfl := eq_of_heq hc
  rfl

/-- 13.2: the terms of a type over an extension are the terms of the bound
type. -/
def Tm₁.bindEquiv {X : Ob} (a : Ty₁ X) (c : Ty₁ (Ob.extend X a.toTy)) :
    Tm₁ (Ob.extend X a.toTy) c ≃ Tm₁ X (Bind a c) :=
  Quotient.hrecOn
    (motive := fun X => (a : Ty₁ X) → (c : Ty₁ (Ob.extend X (Ty₁.toTy a))) →
      (Tm₁ (Ob.extend X (Ty₁.toTy a)) c ≃ Tm₁ X (Bind a c)))
    X bindEquivObj
    (by
      intro Γ Γ' hΓ
      have hX : Γ.toOb = Γ'.toOb := Quotient.sound hΓ
      refine Function.hfunext (congrArg Ty₁ hX) ?_
      intro a a' ha
      refine Function.hfunext (congrArg Ty₁ (Ty₁.extend_heq hX ha)) ?_
      intro c c' hc
      refine Equiv.heq_congr (Tm₁.type_congr (Ty₁.extend_heq hX ha) hc)
        (Tm₁.type_congr hX (Bind_heq hX ha hc)) ?_
      intro x x' hx
      refine Tm₁.heq_of_heq_val hX ?_
      obtain ⟨Ω, A, hA⟩ := Γ
      obtain ⟨Ω', A', hA'⟩ := Γ'
      obtain ⟨rfl, hAA⟩ := hΓ
      induction a using Quotient.ind with
      | _ e =>
      induction a' using Quotient.ind with
      | _ e' =>
      obtain ⟨γ, Θ, β, w⟩ := e
      obtain ⟨γ', Θ', β', w'⟩ := e'
      obtain ⟨rfl, hea⟩ := Ty₁.eq_of_heq_mk hX ha
      induction c using Quotient.ind with
      | _ f =>
      induction c' using Quotient.ind with
      | _ f' =>
      obtain ⟨δ, Ψ, ε, wf⟩ := f
      obtain ⟨δ', Ψ', ε', wf'⟩ := f'
      obtain ⟨rfl, hec⟩ := Ty₁.eq_of_heq_mk (Ty₁.extend_heq hX ha) hc
      revert hx
      refine Tm₁.ind (motive := fun x => HEq x x' →
        HEq (bindEquivObj ⟨Ω, A, hA⟩ _ _ x).1
          (bindEquivObj ⟨Ω, A', hA'⟩ _ _ x').1) ?_ x
      intro τ hx
      revert hx
      refine Tm₁.ind (motive := fun x' => HEq (Tm₁.ofFill τ) x' →
        HEq (bindEquivObj ⟨Ω, A, hA⟩ _ _ (Tm₁.ofFill τ)).1
          (bindEquivObj ⟨Ω, A', hA'⟩ _ _ x').1) ?_ x'
      intro τ' hx
      have hterm := Ob.Term.eq_of_heq_mk (Ty₁.extend_heq hX ha)
        (Tm₁.heq_val (Ty₁.extend_heq hX ha) hc hx) rfl
      have hbase := (hea rfl).2
      have hamb : Eq_t (.nil : Ambient 1) (A' ⋈ dTel.cons Θ' β' .nil)
          (A' ⋈ dTel.cons Θ β .nil) :=
        Eq_t.concatenate (Wf_t.refl hA') (Eq_t.symm hA' hbase)
      have hboth := Eq_t.toBoth Eq_t.Both.nil hamb
      have hwover : Wf_t (A' ⋈ dTel.cons Θ β .nil) (dTel.cons Ψ ε .nil) :=
        Wf_t.ofEq hamb hterm.1.1
      have hsover : Wf_s (A' ⋈ dTel.cons Θ β .nil) (dTel.cons Ψ ε .nil) τ.1 :=
        Wf_s.ofEq hamb hterm.2.2.1 (Wf_t.refl hterm.2.1)
      refine Ob.Term.heq_mk_of_rel hX _ _ _ _ ?_
      intro _
      refine ⟨⟨bind_wf (hea rfl).1 hwover,
        bind_eq hbase (Eq_t.ofEq hamb hterm.1.1 hterm.1.2)⟩,
        bind_wf (hea rfl).1 hwover, ?_, ?_⟩
      · refine (lam_wf_iff τ.filler).mp ?_
        exact Eq.mp (congrArg (fun σ => Wf_s (A' ⋈ dTel.cons Θ β .nil)
          (dTel.cons Ψ ε .nil) σ) (Subst.single_eta τ.1).symm) hsover
      · refine (lam_eq_iff τ.filler τ'.filler).mp ?_
        refine Eq.mp (congrArg₂ (fun σ σ' => Eq_s (A' ⋈ dTel.cons Θ β .nil)
            (dTel.cons Ψ ε .nil) σ σ')
          (Subst.single_eta τ.1).symm (Subst.single_eta τ'.1).symm) ?_
        exact Eq_s.ofBoth hboth hterm.2.2.2 (Eq_t.Both.refl hboth hterm.2.1)
          hterm.2.2.1 hsover)
    a c

/-- The term of the bound type a term over the extension gives. -/
def lam {X : Ob} {a : Ty₁ X} {c : Ty₁ (Ob.extend X a.toTy)}
    (t : Tm₁ (Ob.extend X a.toTy) c) : Tm₁ X (Bind a c) :=
  Tm₁.bindEquiv a c t

/-- The term over the extension a term of the bound type gives. -/
def unlam {X : Ob} {a : Ty₁ X} {c : Ty₁ (Ob.extend X a.toTy)}
    (t : Tm₁ X (Bind a c)) : Tm₁ (Ob.extend X a.toTy) c :=
  (Tm₁.bindEquiv a c).symm t

theorem lam_unlam {X : Ob} {a : Ty₁ X} {c : Ty₁ (Ob.extend X a.toTy)}
    (t : Tm₁ X (Bind a c)) : lam (unlam t) = t :=
  (Tm₁.bindEquiv a c).apply_symm_apply t

theorem unlam_lam {X : Ob} {a : Ty₁ X} {c : Ty₁ (Ob.extend X a.toTy)}
    (t : Tm₁ (Ob.extend X a.toTy) c) : unlam (lam t) = t :=
  (Tm₁.bindEquiv a c).symm_apply_apply t

theorem lam_mk (Γ : Ctx) (e : Ob.Entry Γ.toOb)
    (f : Ob.Entry (Ctx.extend Γ e.toTele))
    (τ : Ob.Fill (Ctx.extend Γ e.toTele) f.toTele) :
    lam (a := Quotient.mk (Ob.Entry.setoid Γ.toOb) e)
        (c := Quotient.mk (Ob.Entry.setoid (Ctx.extend Γ e.toTele)) f) (Tm₁.ofFill τ)
      = Tm₁.ofFill (lamFill Γ e f τ) :=
  rfl

theorem Bind_subst {X Y : Ob} (a : Ty₁ X) (c : Ty₁ (Ob.extend X a.toTy)) (σ : Y ⟶ X) :
    (Bind a c).subst σ = Bind (a.subst σ) (c.subst (a.lift σ)) := by
  induction Y using Quotient.ind with
  | _ Ξ =>
  induction X using Quotient.ind with
  | _ Γ =>
  induction a using Quotient.ind with
  | _ e =>
  induction c using Quotient.ind with
  | _ f =>
  induction σ using Quotient.ind with
  | _ σ =>
  refine Eq.trans ?_ (congrArg
    (fun κ => Bind (Ty₁.subst ⟦e⟧ ⟦σ⟧) (Ty₁.subst ⟦f⟧ κ))
    (Ty₁.lift_mk e σ).symm)
  obtain ⟨γ, Θ, β, w⟩ := e
  obtain ⟨δ, Ψ, ε, wΨ⟩ := f
  have hwf := (Ob.Entry.subst σ (bind Γ ⟨γ, Θ, β, w⟩ ⟨δ, Ψ, ε, wΨ⟩)).wf
  refine Quotient.sound ⟨rfl, hwf, ?_⟩
  exact Eq.mp (congrArg (fun T => Eq_t Ξ.ambient _ T) (bind_actBase σ.1))
    (Wf_t.refl hwf)

theorem lam_subst {X Y : Ob} {a : Ty₁ X} {c : Ty₁ (Ob.extend X a.toTy)}
    (t : Tm₁ (Ob.extend X a.toTy) c) (σ : Y ⟶ X) :
    Bind_subst a c σ ▸ (lam t).subst σ = lam (t.subst (a.lift σ)) := by
  refine Tm₁.cast_eq (Bind_subst a c σ) ?_
  induction X using Quotient.ind with
  | _ Γ =>
  induction Y using Quotient.ind with
  | _ Ξ =>
  induction a using Quotient.ind with
  | _ e =>
  induction c using Quotient.ind with
  | _ f =>
  induction σ using Quotient.ind with
  | _ σ =>
  refine Tm₁.ind (motive := fun t =>
    ((lam (a := Quotient.mk (Ob.Entry.setoid Γ.toOb) e)
        (c := Quotient.mk (Ob.Entry.setoid (Ctx.extend Γ e.toTele)) f) t).subst
      (Quotient.mk (Ob.Subst.setoid Ξ.toOb Γ.toOb) σ)).1
    = (lam (a := Ty₁.subst (Quotient.mk (Ob.Entry.setoid Γ.toOb) e)
          (Quotient.mk (Ob.Subst.setoid Ξ.toOb Γ.toOb) σ))
        (t.subst (Ty₁.lift (Quotient.mk (Ob.Entry.setoid Γ.toOb) e)
          (Quotient.mk (Ob.Subst.setoid Ξ.toOb Γ.toOb) σ)))).1) ?_ t
  intro τ
  obtain ⟨γ, Θ, β, w⟩ := e
  obtain ⟨δ, Ψ, ε, wf⟩ := f
  rw [Ty₁.lift_mk]
  refine Quotient.sound ?_
  have hwf := (Ob.Entry.subst σ (bind Γ ⟨γ, Θ, β, w⟩ ⟨δ, Ψ, ε, wf⟩)).wf
  have hws := (Ob.Term.subst σ ⟨(bind Γ ⟨γ, Θ, β, w⟩ ⟨δ, Ψ, ε, wf⟩).toTele,
    lamFill Γ ⟨γ, Θ, β, w⟩ ⟨δ, Ψ, ε, wf⟩ τ⟩).2.2
  refine Exists.intro
    (rfl : C.single (C.single γ ⋈ δ) ⋈ 1 = C.single (C.single γ ⋈ δ) ⋈ 1) ?_
  refine ⟨⟨hwf, ?_⟩, hwf, hws.2, ?_⟩
  · exact Eq.mp (congrArg (fun T => Eq_t Ξ.ambient _ T) (bind_actBase σ.1))
      (Wf_t.refl hwf)
  · have hfill : _root_.Subst.applyEach σ.1 (_root_.Subst.single τ.filler)
        = _root_.Subst.single (Δ := Ξ.arity) (α := C.single γ ⋈ δ)
          (_root_.Subst.act (Γ := 1)
            (Δ := Γ.arity ⋈ (C.single γ ⋈ 1)) (Ξ := Ξ.arity ⋈ (C.single γ ⋈ 1))
            (_root_.Subst.lift σ.1 (C.single γ ⋈ 1)) δ τ.filler) := by
      rw [Subst.applyEach_single]
      exact congrArg _root_.Subst.single
        (Subst.act_lift σ.1 (C.single γ) δ τ.filler).symm
    exact Eq.mp (congrArg (fun s => Eq_s Ξ.ambient _ _ s) hfill) (Eq_s.refl hws.2)

end Ctx
