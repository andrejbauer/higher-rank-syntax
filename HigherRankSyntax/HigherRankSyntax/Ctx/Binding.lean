import HigherRankSyntax.Ctx.Universe

/-!
# Binding

For an entry `e` over `Γ` and an entry `f` over the extension of `Γ` by `e`, the
entry `bind Γ e f` whose slot binds the entry `e` followed by the entries `f`
binds, and declares what `f` declares; the type `Bind a c`, the class of
`bind Γ e f` for representatives `e` of `a` and `f` of `c`; and the equivalence
`lam`/`unlam` between the terms of `c` over the extension by `a` and the terms of
`Bind a c`.  `Bind` and `lam` commute with reindexing.
-/

open CategoryTheory

namespace Ctx

/-- If `dTel.cons Θ β .nil` is well formed over `A` and `dTel.cons Ψ ε .nil` over
`A ⋈ dTel.cons Θ β .nil`, then the one-entry telescope whose slot binds
`dTel.cons Θ β Ψ` and declares `ε` is well formed over `A`. -/
theorem bind_wf
    {Ω γ δ : C.Arity} {A : Ambient Ω} {Θ : dTel Ω γ} {β : Bd (Ω ⋈ γ)}
    {Ψ : dTel (Ω ⋈ (C.single γ ⋈ 1)) δ} {ε : Bd ((Ω ⋈ (C.single γ ⋈ 1)) ⋈ δ)}
    (hbase : Wf_t A (dTel.cons Θ β .nil))
    (hover : Wf_t (A ⋈ dTel.cons Θ β .nil) (dTel.cons Ψ ε .nil)) :
  Wf_t A (dTel.cons (dTel.cons Θ β Ψ) ε .nil)
  := by
  obtain ⟨hΘ, hβ, -⟩ := Wf_t.cons_inv hbase
  obtain ⟨hΨ, hε, -⟩ := Wf_t.cons_inv hover
  apply Wf_t.cons (Wf_t.cons hΘ hβ hΨ) (Wf_bd.concatenate hε) Wf_t.nil

/-- If `dTel.cons Θ β .nil` and `dTel.cons Θ' β' .nil` are equal over `A`, and
`dTel.cons Ψ ε .nil` and `dTel.cons Ψ' ε' .nil` are equal over
`A ⋈ dTel.cons Θ β .nil`, then the one-entry telescopes whose slots bind
`dTel.cons Θ β Ψ` and `dTel.cons Θ' β' Ψ'` and declare `ε` and `ε'` are equal
over `A`. -/
theorem bind_eq
    {Ω γ δ : C.Arity} {A : Ambient Ω} {Θ Θ' : dTel Ω γ} {β β' : Bd (Ω ⋈ γ)}
    {Ψ Ψ' : dTel (Ω ⋈ (C.single γ ⋈ 1)) δ} {ε ε' : Bd ((Ω ⋈ (C.single γ ⋈ 1)) ⋈ δ)}
    (hbase : Eq_t A (dTel.cons Θ β .nil) (dTel.cons Θ' β' .nil))
    (hover : Eq_t (A ⋈ dTel.cons Θ β .nil) (dTel.cons Ψ ε .nil)
      (dTel.cons Ψ' ε' .nil)) :
  Eq_t A (dTel.cons (dTel.cons Θ β Ψ) ε .nil)
    (dTel.cons (dTel.cons Θ' β' Ψ') ε' .nil)
  := by
  obtain ⟨_, _, _, ⟨⟩, hΘ, hβ, -⟩ := Eq_t.cons_inv hbase
  obtain ⟨_, _, _, ⟨⟩, hΨ, hε, -⟩ := Eq_t.cons_inv hover
  rw [dTel.concatenate_assoc] at hε
  apply Eq_t.cons (Eq_t.cons hΘ hβ hΨ) hε Eq_t.nil

/-- `dTel.actBase σ` on the one-entry telescope whose slot binds `dTel.cons Θ β Ψ`
and declares `ε` acts by `σ` on `Θ` and `β`, and by `Subst.lift σ (C.single γ ⋈ 1)`
on `Ψ` and `ε`. -/
theorem bind_actBase
    {Ω Ω' γ δ : C.Arity} (σ : Subst Ω Ω')
    {Θ : dTel Ω γ} {β : Bd (Ω ⋈ γ)}
    {Ψ : dTel (Ω ⋈ (C.single γ ⋈ 1)) δ} {ε : Bd ((Ω ⋈ (C.single γ ⋈ 1)) ⋈ δ)} :
  dTel.actBase σ (dTel.cons (dTel.cons Θ β Ψ) ε .nil)
    = dTel.cons (dTel.cons (dTel.actBase σ Θ) (Bd.act (Γ := 1) σ γ β)
        (dTel.actBase (Subst.lift σ (C.single γ ⋈ 1)) Ψ))
        (Bd.act (Γ := 1) (Δ := Ω ⋈ (C.single γ ⋈ 1)) (Ξ := Ω' ⋈ (C.single γ ⋈ 1))
          (Subst.lift σ (C.single γ ⋈ 1)) δ ε) .nil
  := by
  rw [Bd.act_lift]
  rfl

/-- `Subst.single t` fills `dTel.cons Ψ ε .nil` over `A ⋈ dTel.cons Θ β .nil`
exactly when it fills the one-entry telescope over `A` whose slot binds
`dTel.cons Θ β Ψ` and declares `ε`. -/
theorem lam_wf_iff
    {Ω γ δ : C.Arity} {A : Ambient Ω} {Θ : dTel Ω γ} {β : Bd (Ω ⋈ γ)}
    {Ψ : dTel (Ω ⋈ (C.single γ ⋈ 1)) δ} {ε : Bd ((Ω ⋈ (C.single γ ⋈ 1)) ⋈ δ)}
    (t : Expr ((Ω ⋈ (C.single γ ⋈ 1)) ⋈ δ)) :
  Wf_s (A ⋈ dTel.cons Θ β .nil) (dTel.cons Ψ ε .nil)
      (Subst.single (Δ := Ω ⋈ (C.single γ ⋈ 1)) (α := δ) t)
    ↔ Wf_s A (dTel.cons (dTel.cons Θ β Ψ) ε .nil)
      (Subst.single (Δ := Ω) (α := C.single γ ⋈ δ) t)
  := by
  rw [Wf_s.single_iff, Wf_s.single_iff, dTel.concatenate_assoc]
  exact Iff.rfl

/-- `Subst.single t` and `Subst.single t'` agree as fillings of
`dTel.cons Ψ ε .nil` over `A ⋈ dTel.cons Θ β .nil` exactly when they agree as
fillings of the one-entry telescope over `A` whose slot binds `dTel.cons Θ β Ψ`
and declares `ε`. -/
theorem lam_eq_iff
    {Ω γ δ : C.Arity} {A : Ambient Ω} {Θ : dTel Ω γ} {β : Bd (Ω ⋈ γ)}
    {Ψ : dTel (Ω ⋈ (C.single γ ⋈ 1)) δ} {ε : Bd ((Ω ⋈ (C.single γ ⋈ 1)) ⋈ δ)}
    (t t' : Expr ((Ω ⋈ (C.single γ ⋈ 1)) ⋈ δ)) :
  Eq_s (A ⋈ dTel.cons Θ β .nil) (dTel.cons Ψ ε .nil)
      (Subst.single (Δ := Ω ⋈ (C.single γ ⋈ 1)) (α := δ) t)
      (Subst.single (Δ := Ω ⋈ (C.single γ ⋈ 1)) (α := δ) t')
    ↔ Eq_s A (dTel.cons (dTel.cons Θ β Ψ) ε .nil)
      (Subst.single (Δ := Ω) (α := C.single γ ⋈ δ) t)
      (Subst.single (Δ := Ω) (α := C.single γ ⋈ δ) t')
  := by
  rw [Eq_s.single_iff, Eq_s.single_iff, dTel.concatenate_assoc]
  exact Iff.rfl

/-- The entry over `Γ` whose slot binds the entry `e` followed by the entries `f`
binds, and declares what `f` declares. -/
def bind (Γ : Ctx) (e : Ob.Entry Γ.toOb) (f : Ob.Entry (extend Γ e.toTele)) :
    Ob.Entry Γ.toOb where
  arity := C.single e.arity ⋈ f.arity
  binding := dTel.cons e.binding e.declaration f.binding
  declaration := f.declaration
  wf := bind_wf e.wf f.wf

/-- `bind Γ e f` and `bind Γ e f'` are related when `f` and `f'` are. -/
theorem bind_congr_right
    (Γ : Ctx) (e : Ob.Entry Γ.toOb)
    {f f' : Ob.Entry (extend Γ e.toTele)} (h : Ob.Entry.Rel f f') :
  Ob.Entry.Rel (bind Γ e f) (bind Γ e f')
  := by
  obtain ⟨δ, Ψ, ε, wf⟩ := f
  obtain ⟨δ', Ψ', ε', wf'⟩ := f'
  obtain ⟨ha, -, heq⟩ := h
  obtain rfl := C.single_injective ha
  use rfl, (bind Γ _ _).wf
  apply bind_eq (Wf_t.refl e.wf) heq

/-- `bind Γ e f` and `bind Γ e' f'` are related when `e` and `e'` are and `f`,
`f'` have the same arity, binding and declaration. -/
theorem bind_congr
    (Γ : Ctx) {e e' : Ob.Entry Γ.toOb} (he : Ob.Entry.Rel e e')
    {f : Ob.Entry (extend Γ e.toTele)} {f' : Ob.Entry (extend Γ e'.toTele)}
    (harity : f.arity = f'.arity) (hbinding : HEq f.binding f'.binding)
    (hdeclaration : HEq f.declaration f'.declaration) :
  Ob.Entry.Rel (bind Γ e f) (bind Γ e' f')
  := by
  obtain ⟨γ, Θ, β, w⟩ := e
  obtain ⟨γ', Θ', β', w'⟩ := e'
  obtain ⟨ha, -, heq⟩ := he
  obtain rfl := C.single_injective ha
  obtain ⟨δ, Ψ, ε, wf⟩ := f
  obtain ⟨δ', Ψ', ε', wf'⟩ := f'
  obtain rfl := harity
  obtain rfl := eq_of_heq hbinding
  obtain rfl := eq_of_heq hdeclaration
  use rfl, (bind Γ _ _).wf
  apply bind_eq heq (Wf_t.refl wf)

/-- For a type `a` over `Γ` and a type over its extension by `a`, the class of
`bind Γ e f` for representatives `e` and `f` of the two. -/
def bindEntry (Γ : Ctx) :
    (a : Ty₁ Γ.toOb) → Ty₁ (Ob.extend Γ.toOb a.toTy) → Ty₁ Γ.toOb :=
  fun a => Quotient.hrecOn
    (motive := fun (a : Ty₁ Γ.toOb) =>
      Ty₁ (Ob.extend Γ.toOb (Ty₁.toTy a)) → Ty₁ Γ.toOb) a
    (fun e c => Quotient.liftOn c
      (fun f => Quotient.mk (Ob.Entry.setoid Γ.toOb) (bind Γ e f))
      (fun _ _ h => Quotient.sound (bind_congr_right Γ e h)))
    (by
      intro e e' he
      have hZ := congrArg (Ob.extend Γ.toOb) (Quotient.sound he)
      apply Function.hfunext (congrArg Ty₁ hZ)
      intro c c' hc
      apply heq_of_eq
      obtain ⟨f⟩ := c
      obtain rfl : cast (congrArg Ty₁ hZ) (Quotient.mk (Ob.Entry.setoid _) f) = c' :=
        cast_eq_iff_heq.mpr hc
      rw [Ty₁.mk_cast hZ]
      apply Quotient.sound
      apply bind_congr Γ he
      · symm
        apply Ob.Entry.arity_cast
      · symm
        apply Ob.Entry.binding_cast
      · symm
        apply Ob.Entry.declaration_cast)

/-- The class of `bind Γ e f` for representatives `Γ` of `X`, `e` of `a` and `f`
of `c`. -/
def Bind {X : Ob} (a : Ty₁ X) (c : Ty₁ (Ob.extend X a.toTy)) : Ty₁ X :=
  Quotient.hrecOn
    (motive := fun X => (a : Ty₁ X) → Ty₁ (Ob.extend X (Ty₁.toTy a)) → Ty₁ X)
    X bindEntry
    (by
      intro Γ Γ' hΓ
      have hX := Quotient.sound hΓ
      apply Function.hfunext (congrArg Ty₁ hX)
      intro a a' ha
      apply Function.hfunext (congrArg Ty₁ (Ty₁.extend_heq hX ha))
      intro c c' hc
      obtain ⟨Ω, A, hA⟩ := Γ
      obtain ⟨Ω', A', hA'⟩ := Γ'
      obtain ⟨rfl, -⟩ := hΓ
      obtain ⟨⟨γ, Θ, β, w⟩⟩ := a
      obtain ⟨⟨γ', Θ', β', w'⟩⟩ := a'
      obtain ⟨rfl, hea⟩ := Ty₁.eq_of_heq_mk hX ha
      obtain ⟨⟨δ, Ψ, ε, wΨ⟩⟩ := c
      obtain ⟨⟨δ', Ψ', ε', wΨ'⟩⟩ := c'
      obtain ⟨rfl, hef⟩ := Ty₁.eq_of_heq_mk (Ty₁.extend_heq hX ha) hc
      obtain ⟨hwa, heqa⟩ := hea rfl
      obtain ⟨hwf, heqf⟩ := hef rfl
      have hamb := Eq_t.concatenate (Wf_t.refl hA') (Eq_t.symm hA' heqa)
      apply Ty₁.heq_mk hX
      intro _
      constructor
      · apply bind_wf hwa (Wf_t.ofEq hamb hwf)
      · apply bind_eq heqa (Eq_t.ofEq hamb hwf heqf))
    a c

/-! ## Abstraction -/

/-- The filling of `bind Γ e f` supplying what the filling `τ` of `f` supplies. -/
def lamFill (Γ : Ctx) (e : Ob.Entry Γ.toOb) (f : Ob.Entry (extend Γ e.toTele))
    (τ : Ob.Fill (extend Γ e.toTele) f.toTele) :
    Ob.Fill Γ.toOb (bind Γ e f).toTele :=
  ⟨Subst.single τ.filler, by
    constructor
    · apply (bind Γ e f).wf
    · apply (lam_wf_iff τ.filler).mp
      convert τ.2.2
      apply Subst.single_eta⟩

/-- The filling of `f` supplying what the filling `τ` of `bind Γ e f` supplies. -/
def unlamFill (Γ : Ctx) (e : Ob.Entry Γ.toOb) (f : Ob.Entry (extend Γ e.toTele))
    (τ : Ob.Fill Γ.toOb (bind Γ e f).toTele) :
    Ob.Fill (extend Γ e.toTele) f.toTele :=
  ⟨Subst.single τ.filler, by
    constructor
    · apply f.wf
    · apply (lam_wf_iff τ.filler).mpr
      convert τ.2.2
      apply Subst.single_eta⟩

theorem unlamFill_lamFill
    (Γ : Ctx) (e : Ob.Entry Γ.toOb) (f : Ob.Entry (extend Γ e.toTele))
    (τ : Ob.Fill (extend Γ e.toTele) f.toTele) :
  unlamFill Γ e f (lamFill Γ e f τ) = τ
  := by
  apply Subtype.ext
  apply Subst.single_eta

theorem lamFill_unlamFill
    (Γ : Ctx) (e : Ob.Entry Γ.toOb) (f : Ob.Entry (extend Γ e.toTele))
    (τ : Ob.Fill Γ.toOb (bind Γ e f).toTele) :
  lamFill Γ e f (unlamFill Γ e f τ) = τ
  := by
  apply Subtype.ext
  apply Subst.single_eta

/-- `lamFill` and `unlamFill` as an equivalence between the fillings of `f` and
those of `bind Γ e f`. -/
def lamFillEquiv (Γ : Ctx) (e : Ob.Entry Γ.toOb)
    (f : Ob.Entry (extend Γ e.toTele)) :
    Ob.Fill (extend Γ e.toTele) f.toTele ≃ Ob.Fill Γ.toOb (bind Γ e f).toTele where
  toFun := lamFill Γ e f
  invFun := unlamFill Γ e f
  left_inv := unlamFill_lamFill Γ e f
  right_inv := lamFill_unlamFill Γ e f

/-- Fillings `τ`, `τ'` of `f` agree exactly when `lamFill Γ e f τ` and
`lamFill Γ e f τ'` agree. -/
theorem lamFill_rel
    (Γ : Ctx) (e : Ob.Entry Γ.toOb) (f : Ob.Entry (extend Γ e.toTele))
    (τ τ' : Ob.Fill (extend Γ e.toTele) f.toTele) :
  Ob.Fill.Rel τ τ' ↔ Ob.Fill.Rel (lamFill Γ e f τ) (lamFill Γ e f τ')
  := by
  constructor
  · rintro ⟨-, -, heq⟩
    use (bind Γ e f).wf, (lamFill Γ e f τ).2.2
    apply (lam_eq_iff τ.filler τ'.filler).mp
    convert heq using 1
    · apply Subst.single_eta
    · apply Subst.single_eta
  · rintro ⟨-, -, heq⟩
    use f.wf, τ.2.2
    convert (lam_eq_iff τ.filler τ'.filler).mpr heq using 1
    · symm
      apply Subst.single_eta
    · symm
      apply Subst.single_eta

/-- `lamFillEquiv` on classes of fillings, as an equivalence between the terms of
the class of `f` and those of the class of `bind Γ e f`. -/
def bindEquiv (Γ : Ctx) (e : Ob.Entry Γ.toOb)
    (f : Ob.Entry (extend Γ e.toTele)) :
    Tm₁ (extend Γ e.toTele)
        (Quotient.mk (Ob.Entry.setoid (extend Γ e.toTele)) f)
      ≃ Tm₁ Γ.toOb (Quotient.mk (Ob.Entry.setoid Γ.toOb) (bind Γ e f)) :=
  (Tm₁.fillEquiv f).trans
    ((Quotient.congr (lamFillEquiv Γ e f) (fun _ _ => lamFill_rel Γ e f _ _)).trans
      (Tm₁.fillEquiv (bind Γ e f)).symm)

/-- `bindEquiv Γ e f` for representatives `f` of `c`, as an equivalence between
the terms of `c` and those of `Bind` of the class of `e` and `c`. -/
def bindEquivEntry (Γ : Ctx) (e : Ob.Entry Γ.toOb) :
    (c : Ty₁ (extend Γ e.toTele)) →
      (Tm₁ (extend Γ e.toTele) c
        ≃ Tm₁ Γ.toOb (Bind (Quotient.mk (Ob.Entry.setoid Γ.toOb) e) c)) :=
  fun c => Quotient.hrecOn
    (motive := fun (c : Ty₁ (extend Γ e.toTele)) =>
      Tm₁ (extend Γ e.toTele) c
        ≃ Tm₁ Γ.toOb (Bind (Quotient.mk (Ob.Entry.setoid Γ.toOb) e) c))
    c (bindEquiv Γ e)
    (by
      intro f f' h
      obtain ⟨δ, Ψ, ε, w⟩ := f
      obtain ⟨δ', Ψ', ε', w'⟩ := f'
      have ⟨hδ, _⟩ := h
      obtain rfl := C.single_injective hδ
      have hbind := bind_congr_right Γ e h
      apply Equiv.heq_congr
        (congrArg (Tm₁ (extend Γ e.toTele)) (Quotient.sound h))
        (congrArg (Tm₁ Γ.toOb) (Quotient.sound hbind))
      intro x x' hx
      apply Tm₁.heq_of_eq
      induction x using Tm₁.ind with
      | _ τ =>
      induction x' using Tm₁.ind with
      | _ τ' =>
      obtain ⟨_, _, -, -, hττ⟩ := Quotient.exact (Tm₁.eq_of_heq (Quotient.sound h) hx)
      apply Quotient.sound
      use rfl, hbind.2, (lamFill Γ e _ τ).2.1, (lamFill Γ e _ τ).2.2
      apply (lam_eq_iff τ.filler τ'.filler).mp
      convert hττ using 1
      · apply Subst.single_eta
      · apply Subst.single_eta)

/-- `Bind a c = Bind a' c'` when `a = a'` and `c` and `c'` are heterogeneously
equal. -/
theorem Bind_congr
    {X : Ob} {a a' : Ty₁ X} (ha : a = a')
    {c : Ty₁ (Ob.extend X a.toTy)} {c' : Ty₁ (Ob.extend X a'.toTy)} (hc : HEq c c') :
  Bind a c = Bind a' c'
  := by
  subst ha
  obtain rfl := eq_of_heq hc
  rfl

/-- `bindEquivEntry Γ e` for representatives `e` of `a`, as an equivalence between
the terms of `c` and those of `Bind a c`. -/
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
      have ⟨hγ, _⟩ := h
      obtain rfl := C.single_injective hγ
      have ⟨_, _, hbase⟩ := h
      have hZ := congrArg (Ob.extend Γ.toOb) (Quotient.sound h)
      have hamb := Eq_t.concatenate (Wf_t.refl Γ.wf) (Eq_t.symm Γ.wf hbase)
      apply Function.hfunext (congrArg Ty₁ hZ)
      intro c c' hc
      obtain ⟨⟨δ, Ψ, ε, wf⟩⟩ := c
      obtain ⟨⟨δ', Ψ', ε', wf'⟩⟩ := c'
      obtain ⟨rfl, -⟩ := Ty₁.eq_of_heq_mk hZ hc
      apply Equiv.heq_congr (Tm₁.type_congr hZ hc)
        (congrArg (Tm₁ Γ.toOb) (Bind_congr (Quotient.sound h) hc))
      intro x x' hx
      apply Tm₁.heq_of_eq
      induction x using Tm₁.ind with
      | _ τ =>
      induction x' using Tm₁.ind with
      | _ τ' =>
      obtain ⟨⟨hwover, hover⟩, -, hwτ, hττ⟩ :=
        Ob.Term.eq_of_heq_mk hZ (Tm₁.heq_val hZ hc hx) rfl
      have hboth := Eq_t.toBoth Eq_t.Both.nil hamb
      apply Quotient.sound
      use rfl, ⟨(bind Γ _ _).wf, bind_eq hbase (Eq_t.ofEq hamb hwover hover)⟩,
        (lamFill Γ _ _ τ).2.1, (lamFill Γ _ _ τ).2.2
      apply (lam_eq_iff τ.filler τ'.filler).mp
      convert Eq_s.ofBoth hboth hττ (Eq_t.Both.refl hboth hwover) hwτ
        (Wf_s.ofEq hamb hwτ (Wf_t.refl hwover)) using 1
      · apply Subst.single_eta
      · apply Subst.single_eta)

/-- `Bind a c` and `Bind a' c'` are heterogeneously equal when `X = X'`, `a` and
`a'` are heterogeneously equal, and `c` and `c'` are. -/
theorem Bind_heq
    {X X' : Ob} (hX : X = X') {a : Ty₁ X} {a' : Ty₁ X'} (ha : HEq a a')
    {c : Ty₁ (Ob.extend X a.toTy)} {c' : Ty₁ (Ob.extend X' a'.toTy)} (hc : HEq c c') :
  HEq (Bind a c) (Bind a' c')
  := by
  subst hX
  obtain rfl := eq_of_heq ha
  obtain rfl := eq_of_heq hc
  rfl

/-- The equivalence between the terms of `c` and those of `Bind a c` that, for
representatives `Γ`, `e`, `f` of `X`, `a`, `c`, sends the term of a filling `τ` of
`f` to the term of `lamFill Γ e f τ`. -/
def Tm₁.bindEquiv {X : Ob} (a : Ty₁ X) (c : Ty₁ (Ob.extend X a.toTy)) :
    Tm₁ (Ob.extend X a.toTy) c ≃ Tm₁ X (Bind a c) :=
  Quotient.hrecOn
    (motive := fun X => (a : Ty₁ X) → (c : Ty₁ (Ob.extend X (Ty₁.toTy a))) →
      (Tm₁ (Ob.extend X (Ty₁.toTy a)) c ≃ Tm₁ X (Bind a c)))
    X bindEquivObj
    (by
      intro Γ Γ' hΓ
      have hX := Quotient.sound hΓ
      apply Function.hfunext (congrArg Ty₁ hX)
      intro a a' ha
      apply Function.hfunext (congrArg Ty₁ (Ty₁.extend_heq hX ha))
      intro c c' hc
      apply Equiv.heq_congr (Tm₁.type_congr (Ty₁.extend_heq hX ha) hc)
        (Tm₁.type_congr hX (Bind_heq hX ha hc))
      intro x x' hx
      apply Tm₁.heq_of_heq_val hX
      obtain ⟨Ω, A, hA⟩ := Γ
      obtain ⟨Ω', A', hA'⟩ := Γ'
      obtain ⟨rfl, -⟩ := hΓ
      obtain ⟨⟨γ, Θ, β, w⟩⟩ := a
      obtain ⟨⟨γ', Θ', β', w'⟩⟩ := a'
      obtain ⟨rfl, hea⟩ := Ty₁.eq_of_heq_mk hX ha
      obtain ⟨⟨δ, Ψ, ε, wf⟩⟩ := c
      obtain ⟨⟨δ', Ψ', ε', wf'⟩⟩ := c'
      obtain ⟨rfl, -⟩ := Ty₁.eq_of_heq_mk (Ty₁.extend_heq hX ha) hc
      induction x using Tm₁.ind with
      | _ τ =>
      induction x' using Tm₁.ind with
      | _ τ' =>
      obtain ⟨⟨hwover, hover⟩, -, hwτ, hττ⟩ := Ob.Term.eq_of_heq_mk
        (Ty₁.extend_heq hX ha) (Tm₁.heq_val (Ty₁.extend_heq hX ha) hc hx) rfl
      obtain ⟨hwbase, hbase⟩ := hea rfl
      have hamb := Eq_t.concatenate (Wf_t.refl hA') (Eq_t.symm hA' hbase)
      have hboth := Eq_t.toBoth Eq_t.Both.nil hamb
      have hwbind := bind_wf hwbase (Wf_t.ofEq hamb hwover)
      have hwτ' := Wf_s.ofEq hamb hwτ (Wf_t.refl hwover)
      apply Ob.Term.heq_mk_of_rel hX
      intro _
      use ⟨hwbind, bind_eq hbase (Eq_t.ofEq hamb hwover hover)⟩, hwbind
      constructor
      · apply (lam_wf_iff τ.filler).mp
        convert hwτ'
        apply Subst.single_eta
      · apply (lam_eq_iff τ.filler τ'.filler).mp
        convert Eq_s.ofBoth hboth hττ (Eq_t.Both.refl hboth hwover) hwτ hwτ' using 1
        · apply Subst.single_eta
        · apply Subst.single_eta)
    a c

/-- The term of `Bind a c` corresponding to `t` under `Tm₁.bindEquiv a c`. -/
def lam {X : Ob} {a : Ty₁ X} {c : Ty₁ (Ob.extend X a.toTy)}
    (t : Tm₁ (Ob.extend X a.toTy) c) : Tm₁ X (Bind a c) :=
  Tm₁.bindEquiv a c t

/-- The term of `c` corresponding to `t` under `Tm₁.bindEquiv a c`. -/
def unlam {X : Ob} {a : Ty₁ X} {c : Ty₁ (Ob.extend X a.toTy)}
    (t : Tm₁ X (Bind a c)) : Tm₁ (Ob.extend X a.toTy) c :=
  (Tm₁.bindEquiv a c).symm t

theorem lam_unlam
    {X : Ob} {a : Ty₁ X} {c : Ty₁ (Ob.extend X a.toTy)}
    (t : Tm₁ X (Bind a c)) :
  lam (unlam t) = t
  := (Tm₁.bindEquiv a c).apply_symm_apply t

theorem unlam_lam
    {X : Ob} {a : Ty₁ X} {c : Ty₁ (Ob.extend X a.toTy)}
    (t : Tm₁ (Ob.extend X a.toTy) c) :
  unlam (lam t) = t
  := (Tm₁.bindEquiv a c).symm_apply_apply t

/-- Reindexing `Bind a c` along `σ` gives `Bind` of `a` reindexed along `σ` and
`c` reindexed along `a.lift σ`. -/
theorem Bind_subst
    {X Y : Ob} (a : Ty₁ X) (c : Ty₁ (Ob.extend X a.toTy)) (σ : Y ⟶ X) :
  (Bind a c).subst σ = Bind (a.subst σ) (c.subst (a.lift σ))
  := by
  induction Y using Ob.ind with
  | _ Ξ =>
  induction X using Ob.ind with
  | _ Γ =>
  induction a using Quotient.ind with
  | _ e =>
  induction c using Quotient.ind with
  | _ f =>
  induction σ using Quotient.ind with
  | _ σ =>
  rw [Ty₁.lift_mk]
  have hwf := (Ob.Entry.subst σ (bind Γ e f)).wf
  obtain ⟨γ, Θ, β, w⟩ := e
  obtain ⟨δ, Ψ, ε, wf⟩ := f
  apply Quotient.sound
  use rfl, hwf
  convert Wf_t.refl hwf using 1
  symm
  apply bind_actBase σ.1 (Θ := Θ) (β := β) (Ψ := Ψ) (ε := ε)

/-- Reindexing `lam t` along `σ` and transporting along `Bind_subst a c σ` gives
`lam` of `t` reindexed along `a.lift σ`. -/
theorem lam_subst
    {X Y : Ob} {a : Ty₁ X} {c : Ty₁ (Ob.extend X a.toTy)}
    (t : Tm₁ (Ob.extend X a.toTy) c) (σ : Y ⟶ X) :
  Bind_subst a c σ ▸ (lam t).subst σ = lam (t.subst (a.lift σ))
  := by
  apply Tm₁.cast_eq (Bind_subst a c σ)
  induction X using Ob.ind with
  | _ Γ =>
  induction Y using Ob.ind with
  | _ Ξ =>
  induction a using Quotient.ind with
  | _ e =>
  induction c using Quotient.ind with
  | _ f =>
  induction σ using Quotient.ind with
  | _ σ =>
  induction t using Tm₁.ind with
  | _ τ =>
  rw [Ty₁.lift_mk]
  have hwf := (Ob.Entry.subst σ (bind Γ e f)).wf
  have hws := (Ob.Term.subst σ ⟨(bind Γ e f).toTele, lamFill Γ e f τ⟩).2.2.2
  obtain ⟨γ, Θ, β, w⟩ := e
  obtain ⟨δ, Ψ, ε, wf⟩ := f
  apply Quotient.sound
  use rfl
  constructor
  · use hwf
    convert Wf_t.refl hwf using 1
    symm
    apply bind_actBase σ.1 (Θ := Θ) (β := β) (Ψ := Ψ) (ε := ε)
  · use hwf, hws
    have hfill : Subst.applyEach σ.1 (Subst.single τ.filler)
        = Subst.single (Δ := Ξ.arity) (α := C.single γ ⋈ δ)
          (Subst.act (Γ := 1) (Δ := Γ.arity ⋈ (C.single γ ⋈ 1))
            (Ξ := Ξ.arity ⋈ (C.single γ ⋈ 1)) (Subst.lift σ.1 (C.single γ ⋈ 1)) δ τ.filler)
      := by
      rw [Subst.applyEach_single]
      congr 1
      symm
      apply Subst.act_lift σ.1 (C.single γ) δ τ.filler
    convert Eq_s.refl hws using 1
    symm
    apply hfill

end Ctx
