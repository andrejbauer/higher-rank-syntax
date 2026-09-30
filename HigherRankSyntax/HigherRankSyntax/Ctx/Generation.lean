import HigherRankSyntax.Ctx.Model
import HigherRankSyntax.HrS.Closed

/-!
# `Ctx.model` is generated

A family of predicates on the objects, substitutions, types and terms of `Ctx.model` closed
under its operations holds of all of them (`generated`).  For such a family, predicates on raw
ambients, telescopes, declarations and expressions (`CtxGood`, `TelGood`, `AtomGood`,
`ExprGood`) hold of all well-formed ones (`CtxGood.of_wf`, `Wf_t.good`, `Wf_bd.good`,
`Wf_e.good`), and for every filling `σ` of a telescope `Θ` over `Ξ`, the substitution from `Ξ`
to `Ξ ⋈ Θ` pairing the identity with `σ` satisfies the predicate on substitutions
(`Wf_s.good`).
-/

open CategoryTheory

/-! ## Well-formedness -/

/-- If `Θ ⋈ Ψ` is well formed over `Ξ`, then `Θ` is well formed over `Ξ` and `Ψ` over
`Ξ ⋈ Θ`. -/
theorem Wf_t.concatenate_inv {Δ : C.Arity} {Ξ : Ambient Δ} :
  ∀ {Ω Φ : C.Arity} (Θ : dTel Δ Ω) {Ψ : dTel (Δ ⋈ Ω) Φ},
    Wf_t Ξ (Θ ⋈ Ψ) → Wf_t Ξ Θ ∧ Wf_t (Ξ ⋈ Θ) Ψ
  | _, _, .nil, _, h => by
      erw [dTel.concatenate_nil]
      exact ⟨Wf_t.nil, h⟩
  | _, _, .cons _ _ Θ, _, h => by
      obtain ⟨hbind, hboundary, hrest⟩ := Wf_t.cons_inv h
      obtain ⟨hΘ, hΨ⟩ := Wf_t.concatenate_inv Θ hrest
      erw [dTel.concatenate_assoc] at hΨ
      exact ⟨Wf_t.cons hbind hboundary hΘ, hΨ⟩

/-- A declaration well formed over `Ξ` with bound entries `Θ ⋈ Ψ` is well formed over
`Ξ ⋈ Θ` with bound entries `Ψ`. -/
theorem Wf_bd.split
    {Δ Λ Φ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Λ} {Ψ : dTel (Δ ⋈ Λ) Φ}
    {β : Bd ((Δ ⋈ Λ) ⋈ Φ)}
    (h : Wf_bd Ξ (Θ ⋈ Ψ) β) :
  Wf_bd (Ξ ⋈ Θ) Ψ β
  := by
  cases h with
  | sort => apply Wf_bd.sort
  | of hS hsort =>
      erw [← dTel.concatenate_assoc] at hS hsort
      apply Wf_bd.of hS hsort
  | eq hl hr heq =>
      erw [← dTel.concatenate_assoc] at hl hr heq
      apply Wf_bd.eq hl hr heq

/-- If the entry binding `Θ` and declaring `β` is well formed over `Ξ`, then the entry binding
nothing and declaring `β` is well formed over `Ξ ⋈ Θ`. -/
theorem Wf_t.atom {Δ γ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ γ} {β : Bd (Δ ⋈ γ)}
    (h : Wf_t Ξ (dTel.cons Θ β .nil)) :
  Wf_t (Ξ ⋈ Θ) (dTel.cons .nil β .nil)
  := by
  obtain ⟨-, hβ, -⟩ := Wf_t.cons_inv h
  apply Wf_t.cons Wf_t.nil _ Wf_t.nil
  apply Wf_bd.split (Θ := Θ) (Ψ := .nil)
  rw [dTel.concatenate_nil]
  apply hβ

/-- An equation well formed over `Ξ` with no bound entries has sides well formed over `Ξ` with
equal computed boundaries. -/
theorem Wf_bd.nil_eq {Δ : C.Arity} {Ξ : Ambient Δ} {l r : Expr Δ}
    (h : Wf_bd Ξ .nil (.eq l r)) :
  Wf_e Ξ l ∧ Wf_e Ξ r ∧ Eq_bd Ξ (Ξ.boundaryOf l) (Ξ.boundaryOf r)
  := by
  cases h with
  | eq hl hr heq =>
    erw [dTel.concatenate_nil] at hl hr heq
    exact ⟨hl, hr, heq⟩

/-- A declaration `of S` well formed over `Ξ` with no bound entries has `S` well formed over
`Ξ` with computed boundary equal to `sort`. -/
theorem Wf_bd.nil_of {Δ : C.Arity} {Ξ : Ambient Δ} {S : Expr Δ}
    (h : Wf_bd Ξ .nil (.of S)) :
  Wf_e Ξ S ∧ Eq_bd Ξ (Ξ.boundaryOf S) .sort
  := by
  cases h with
  | of hS hsort =>
    erw [dTel.concatenate_nil] at hS hsort
    exact ⟨hS, hsort⟩

/-- The computed boundary of a well-formed expression over a well-formed ambient is well
formed with no bound entries. -/
theorem Wf_e.boundary {Δ : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ) :
  ∀ {e : Expr Δ}, Wf_e Ξ e → Wf_bd Ξ .nil (Ξ.boundaryOf e)
  | _, .ap x _ _ fill => by
      have wa := Wf_t.atom (Wf_t.cons (Wf_t.binding hΞ x) (Wf_t.declaration hΞ x) Wf_t.nil)
      obtain ⟨-, hβ, -⟩ := Wf_t.cons_inv (Wf_t.instantiate fill wa)
      erw [Bd.act_copair_prefix] at hβ
      apply hβ

/-- The computed boundary of a well-formed expression is not an equation. -/
theorem Wf_e.boundary_not_isEq {Δ : C.Arity} {Ξ : Ambient Δ} :
  ∀ {e : Expr Δ}, Wf_e Ξ e → ¬ (Ξ.boundaryOf e).isEq
  | _, .ap _ _ head _ => by
      intro hEq
      apply head
      apply (Bd.isEq_act _ _ _).mp hEq

/-- A boundary whose action by `σ` at depth `Φ` is `of S` is `of S₀` with
`S = σ.act Φ S₀`. -/
theorem Bd.act_of_inv {Γ Δ Ξ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity) :
  ∀ {β : Bd (Γ ⋈ Δ ⋈ Φ)} {S : Expr (Γ ⋈ Ξ ⋈ Φ)}, Bd.act σ Φ β = .of S →
    ∃ S₀, β = .of S₀ ∧ S = σ.act Φ S₀
  | .of S₀, _, rfl => ⟨S₀, rfl, rfl⟩

/-- An equation is `.eq l r` for some sides `l` and `r`. -/
theorem Bd.eq_of_isEq {Δ : C.Arity} :
  ∀ {β : Bd Δ}, β.isEq → ∃ l r, β = .eq l r
  | .eq l r, _ => ⟨l, r, rfl⟩

/-- A well-formed expression whose computed boundary is equal to `β` fills the entry binding
nothing and declaring `β`. -/
theorem Wf_e.fill
    {Δ : C.Arity} {Ξ : Ambient Δ} {e : Expr Δ} {β : Bd Δ}
    (he : Wf_e Ξ e) (hβ : Eq_bd Ξ (Ξ.boundaryOf e) β) :
  Wf_s Ξ (dTel.cons .nil β .nil) (Subst.single (Δ := Δ) (α := 1) e)
  := by
  apply (Wf_s.single_iff (Δ := Δ) (α := 1) e).mpr
  erw [dTel.concatenate_nil]
  constructor
  · rintro l r rfl
    apply absurd _ (Wf_e.boundary_not_isEq he)
    apply (Eq_bd.isEq hβ).mpr trivial
  · exact ⟨fun _ => he, fun _ => hβ⟩

/-- If the entry binding nothing and declaring `.of S` is well formed over `Ξ`, then the entry
binding nothing and declaring a sort is well formed over `Ξ` and filled by `Subst.single S`. -/
theorem Wf_t.sort_fill {Δ : C.Arity} {Ξ : Ambient Δ} {S : Expr Δ}
    (h : Wf_t Ξ (dTel.cons .nil (.of S) .nil)) :
  Wf_t Ξ (dTel.cons .nil .sort .nil) ∧
    Wf_s Ξ (dTel.cons .nil .sort .nil) (Subst.single (Δ := Δ) (α := 1) S)
  := by
  obtain ⟨-, hβ, -⟩ := Wf_t.cons_inv h
  obtain ⟨hS, hsort⟩ := Wf_bd.nil_of hβ
  use Wf_t.cons Wf_t.nil Wf_bd.sort Wf_t.nil
  apply Wf_e.fill hS hsort

/-- For a slot `x` of a well-formed ambient `Ξ` whose declaration is not an equation,
`Subst.single (Expr.η x)` fills the entry binding `Ξ.binding x` and declaring
`Ξ.declaration x`. -/
theorem Wf_s.eta_single {Δ α : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ) (x : Δ ∋ α)
    (hne : ¬ (Ξ.declaration x).isEq) :
  Wf_s Ξ (dTel.cons (Ξ.binding x) (Ξ.declaration x) .nil) (Subst.single (Expr.η x))
  := by
  apply (Wf_s.single_iff (Expr.η x)).mpr
  and_intros
  · intro l r he
    rw [he] at hne
    exact absurd trivial hne
  · intro _
    apply Wf_e.eta Ξ x (Wf_t.binding hΞ x) hne
  · intro _
    rw [dTel.boundaryOf_eta]
    apply Wf_bd.refl (Wf_t.declaration hΞ x)

/-- Instantiating the η-expansion of `x` by `args` gives the application of `x` to `args`. -/
theorem act_copair_eta {Δ α : C.Arity} (x : Δ ∋ α) (args : Subst α Δ) :
  Subst.act (Γ := 1) (Subst.copair (Subst.id Δ) args) 1 (Expr.η x : Expr (Δ ⋈ α))
    = Expr.ap x args
  := by
  rw [Expr.η.eq_1]
  apply Eq.trans (act_ap_eta (Subst.copair (Subst.id Δ) args) (C.inl x) x
    (Subst.copair_inl _ _ x) _)
  congr 1
  funext Λ i
  apply Eq.trans (act_η _ Λ (C.inr i))
  apply Subst.copair_inr

/-- `Subst.single` of the value of `σ` on the first slot is the restriction of `σ` to
`C.single α`. -/
theorem Subst.single_restrict {Δ α Ω : C.Arity} (σ : Subst (C.single α ⋈ Ω) Δ) :
  Subst.single (σ (C.inl (C.singleSlot α)))
    = fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)
  := by
  rw [← Subst.single_eta (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)), C.unit_right]

namespace Ctx

/-- If the entry whose slot binds `dTel.cons Θ β Ψ` and declares `ε` is well formed over
`Ξ`, then so are `dTel.cons Θ β .nil` over `Ξ` and `dTel.cons Ψ ε .nil` over
`Ξ ⋈ dTel.cons Θ β .nil`. -/
theorem bind_wf_inv
    {Ω γ δ : C.Arity} {Ξ : Ambient Ω} {Θ : dTel Ω γ} {β : Bd (Ω ⋈ γ)}
    {Ψ : dTel (Ω ⋈ (C.single γ ⋈ 1)) δ} {ε : Bd ((Ω ⋈ (C.single γ ⋈ 1)) ⋈ δ)}
    (h : Wf_t Ξ (dTel.cons (dTel.cons Θ β Ψ) ε .nil)) :
  Wf_t Ξ (dTel.cons Θ β .nil) ∧ Wf_t (Ξ ⋈ dTel.cons Θ β .nil) (dTel.cons Ψ ε .nil)
  := by
  obtain ⟨hbind, hε, -⟩ := Wf_t.cons_inv h
  obtain ⟨hΘ, hβ, hΨ⟩ := Wf_t.cons_inv hbind
  constructor
  · apply Wf_t.cons hΘ hβ Wf_t.nil
  · apply Wf_t.cons hΨ (Wf_bd.split (Θ := dTel.cons Θ β .nil) hε) Wf_t.nil

/-! ## Families of predicates on raw syntax -/

section Good

variable (P_Ob : Ob → Prop) (P_Ty : ∀ {X : Ob}, Ty₁ X → Prop)
  (P_Tm : ∀ {X : Ob} {a : Ty₁ X}, Tm₁ X a → Prop)

/-- Every context with ambient `Ξ` satisfies `P_Ob`. -/
def ObGood {Δ : C.Arity} (Ξ : Ambient Δ) : Prop :=
  ∀ hΞ : Ambient.Wf Ξ, P_Ob (toOb ⟨Δ, Ξ, hΞ⟩)

/-- If `β` is `.of S`, then over every context with ambient `Ξ` the term of the type of sorts
filled by `S` satisfies `P_Tm`. -/
def SortGood {Δ : C.Arity} (Ξ : Ambient Δ) (β : Bd Δ) : Prop :=
  ∀ S : Expr Δ, β = .of S → ∀ (hΞ : Ambient.Wf Ξ)
    (τw : Ob.Fill.Wf (toOb ⟨Δ, Ξ, hΞ⟩) (dTel.cons .nil .sort .nil)
      (Subst.single (Δ := Δ) (α := 1) S)),
    P_Tm (Tm₁.ofFill (e := Ob.Entry.sort (toOb ⟨Δ, Ξ, hΞ⟩)) ⟨Subst.single S, τw⟩)

/-- Over every context with ambient `Ξ`, the type of the entry binding nothing and declaring
`β` satisfies `P_Ty`, and `β` satisfies `SortGood`. -/
def AtomGood {Δ : C.Arity} (Ξ : Ambient Δ) (β : Bd Δ) : Prop :=
  (∀ (hΞ : Ambient.Wf Ξ) (w : Wf_t Ξ (dTel.cons .nil β .nil)),
      P_Ty (Quotient.mk (Ob.Entry.setoid (toOb ⟨Δ, Ξ, hΞ⟩)) ⟨1, .nil, β, w⟩)) ∧
    SortGood P_Tm Ξ β

/-- For every entry of `Θ`, the entries its slot binds satisfy `TelGood` over `Ξ` followed by
the entries of `Θ` before it, and its declaration satisfies `AtomGood` over those followed by
the entries its slot binds. -/
def TelGood : {Δ Ω : C.Arity} → Ambient Δ → dTel Δ Ω → Prop
  | _, _, _, .nil => True
  | _, _, Ξ, .cons Θ β Ψ =>
      TelGood Ξ Θ ∧ AtomGood P_Ty P_Tm (Ξ ⋈ Θ) β ∧ TelGood (Ξ ⋈ dTel.cons Θ β .nil) Ψ

/-- Over every context with ambient `Ξ`, the term of the type of the entry binding nothing and
declaring `β` filled by `t` satisfies `P_Tm`. -/
def AtomTermGood {Δ : C.Arity} (Ξ : Ambient Δ) (β : Bd Δ) (t : Expr Δ) : Prop :=
  ∀ (hΞ : Ambient.Wf Ξ) (w : Wf_t Ξ (dTel.cons .nil β .nil))
    (τw : Ob.Fill.Wf (toOb ⟨Δ, Ξ, hΞ⟩) (dTel.cons .nil β .nil)
      (Subst.single (Δ := Δ) (α := 1) t)),
    P_Tm (Tm₁.ofFill (e := (⟨1, .nil, β, w⟩ : Ob.Entry (toOb ⟨Δ, Ξ, hΞ⟩)))
      ⟨Subst.single (Δ := Δ) (α := 1) t, τw⟩)

/-- The entries the slot `x` of `Ξ` binds satisfy `TelGood` over `Ξ`, its declaration
satisfies `AtomGood` over `Ξ` followed by those entries, and, if the declaration is not an
equation, over every context with ambient `Ξ` the term of the type of the entry of `x` filled
by the η-expansion of `x` satisfies `P_Tm`. -/
def SlotGood {Δ α : C.Arity} (Ξ : Ambient Δ) (x : Δ ∋ α) : Prop :=
  TelGood P_Ty P_Tm Ξ (Ξ.binding x) ∧
    AtomGood P_Ty P_Tm (Ξ ⋈ Ξ.binding x) (Ξ.declaration x) ∧
    (¬ (Ξ.declaration x).isEq → ∀ (hΞ : Ambient.Wf Ξ)
      (w : Wf_t Ξ (dTel.cons (Ξ.binding x) (Ξ.declaration x) .nil))
      (τw : Ob.Fill.Wf (toOb ⟨Δ, Ξ, hΞ⟩) (dTel.cons (Ξ.binding x) (Ξ.declaration x) .nil)
        (Subst.single (Expr.η x))),
      P_Tm (Tm₁.ofFill
        (e := (⟨α, Ξ.binding x, Ξ.declaration x, w⟩ : Ob.Entry (toOb ⟨Δ, Ξ, hΞ⟩)))
        ⟨Subst.single (Expr.η x), τw⟩))

/-- Every context with ambient `Ξ` satisfies `P_Ob`, and every slot of `Ξ` satisfies
`SlotGood`. -/
def CtxGood {Δ : C.Arity} (Ξ : Ambient Δ) : Prop :=
  ObGood P_Ob Ξ ∧ ∀ ⦃α : C.Arity⦄ (x : Δ ∋ α), SlotGood P_Ty P_Tm Ξ x

/-- `e` satisfies `AtomTermGood` for its computed boundary, and its computed boundary satisfies
`SortGood`. -/
def ExprGood {Δ : C.Arity} (Ξ : Ambient Δ) (e : Expr Δ) : Prop :=
  AtomTermGood P_Tm Ξ (Ξ.boundaryOf e) e ∧ SortGood P_Tm Ξ (Ξ.boundaryOf e)

end Good

/-! ## Consequences of closure -/

section Closure

variable {P_Ob : Ob → Prop} {P_Sub : ∀ {X Y : Ob}, (Y ⟶ X) → Prop}
  {P_Ty : ∀ {X : Ob}, Ty₁ X → Prop} {P_Tm : ∀ {X : Ob} {a : Ty₁ X}, Tm₁ X a → Prop}
  (h : model.Closed P_Ob P_Sub P_Ty P_Tm)

/-- `P_Tm` holds of every term with the same underlying class as a term satisfying `P_Tm`. -/
theorem Tm₁.of_val {X : Ob} {a a' : Ty₁ X} {t : Tm₁ X a} {t' : Tm₁ X a'}
    (e : t.1 = t'.1) (hP : P_Tm t) :
  P_Tm t'
  := by
  obtain rfl : a = a' := by
    apply Ty₁.toTy_injective
    rw [← t.2, ← t'.2, e]
  obtain rfl : t = t' := Subtype.ext e
  apply hP

/-- `P_Sub` holds of the class of `σ'` if it holds of the class of `σ`, when the ambients of
their domains and of their codomains are equal and their underlying substitutions are equal. -/
theorem sub_of_eq
    {Δ Δ' : C.Arity} {Ξ Ξ₁ : Ambient Δ} {Ξ' Ξ₁' : Ambient Δ'} (e : Ξ = Ξ₁) (e' : Ξ' = Ξ₁')
    {hΞ : Ambient.Wf Ξ} {hΞ₁ : Ambient.Wf Ξ₁} {hΞ' : Ambient.Wf Ξ'} {hΞ₁' : Ambient.Wf Ξ₁'}
    {σ : Ob.Subst (toOb ⟨Δ', Ξ', hΞ'⟩) (toOb ⟨Δ, Ξ, hΞ⟩)}
    {σ' : Ob.Subst (toOb ⟨Δ', Ξ₁', hΞ₁'⟩) (toOb ⟨Δ, Ξ₁, hΞ₁⟩)}
    (hσ : σ.1 = σ'.1) (hP : P_Sub (Quotient.mk _ σ)) :
  P_Sub (Quotient.mk _ σ')
  := by
  subst e e'
  obtain rfl : σ = σ' := Subtype.ext hσ
  apply hP

/-- An expression satisfying `ExprGood` over `Ξ`, well formed over `Ξ` with computed boundary
equal to `β`, satisfies `AtomTermGood` for `β`. -/
theorem ExprGood.atom {Δ : C.Arity} {Ξ : Ambient Δ} {e : Expr Δ} {β : Bd Δ}
    (heg : ExprGood P_Tm Ξ e) (he : Wf_e Ξ e) (hβ : Eq_bd Ξ (Ξ.boundaryOf e) β) :
  AtomTermGood P_Tm Ξ β e
  := by
  intro hΞ w τw
  have we := Wf_t.cons Wf_t.nil (Wf_e.boundary hΞ he) Wf_t.nil
  have hfill := Wf_e.fill he (boundaryOf_refl hΞ he)
  apply Tm₁.of_val _ (heg.1 hΞ we ⟨we, hfill⟩)
  have hβ' : Eq_bd (Ξ ⋈ .nil) (Ξ.boundaryOf e) β := by
    rw [dTel.concatenate_nil]
    apply hβ
  apply Quotient.sound
  use rfl, ⟨we, Eq_t.cons Eq_t.nil hβ' Eq_t.nil⟩, we, hfill
  apply Eq_s.refl hfill

include h

/-- Over a context satisfying `P_Ob`, the type of the entry binding nothing and declaring an
equation satisfies `P_Ty` when both sides satisfy `ExprGood`, and every term of that type
satisfies `P_Tm` when the type satisfies `P_Ty`. -/
theorem eq_good
    {Δ : C.Arity} {Ξ : Ambient Δ} {hΞ : Ambient.Wf Ξ} {l r : Expr Δ}
    (w : Wf_t Ξ (dTel.cons .nil (.eq l r) .nil)) (hob : P_Ob (toOb ⟨Δ, Ξ, hΞ⟩))
    {a : Ty₁ (toOb ⟨Δ, Ξ, hΞ⟩)} (ha : Quotient.mk _ ⟨1, .nil, .eq l r, w⟩ = a) :
  (ExprGood P_Tm Ξ l → ExprGood P_Tm Ξ r → P_Ty a) ∧ (P_Ty a → ∀ t : Tm₁ _ a, P_Tm t)
  := by
  subst ha
  obtain ⟨-, hβ, -⟩ := Wf_t.cons_inv w
  obtain ⟨hl, hr, heq⟩ := Wf_bd.nil_eq hβ
  rcases hb : Ξ.boundaryOf l with _ | S | ⟨_, _⟩
  · have hβl : Eq_bd Ξ (Ξ.boundaryOf l) .sort := by
      rw [hb]
      apply Eq_bd.sort
    have hβr := Eq_bd.trans (Eq_bd.symm heq) hβl
    let τl : Ob.Fill (toOb ⟨Δ, Ξ, hΞ⟩) (Ob.Entry.sort _).toTele :=
      ⟨Subst.single l, Wf_t.cons Wf_t.nil Wf_bd.sort Wf_t.nil, Wf_e.fill hl hβl⟩
    let τr : Ob.Fill (toOb ⟨Δ, Ξ, hΞ⟩) (Ob.Entry.sort _).toTele :=
      ⟨Subst.single r, Wf_t.cons Wf_t.nil Wf_bd.sort Wf_t.nil, Wf_e.fill hr hβr⟩
    constructor
    · intro hlg hrg
      apply h.IdSort hob (hlg.atom hl hβl hΞ _ τl.2) (hrg.atom hr hβr hΞ _ τr.2)
    · intro hty t
      apply h.IdSort_term (s := Tm₁.ofFill τl) (s' := Tm₁.ofFill τr) t hob hty
  · obtain ⟨hS, hsortS⟩ := Wf_bd.nil_of (hb ▸ Wf_e.boundary hΞ hl)
    let τS : Ob.Fill (toOb ⟨Δ, Ξ, hΞ⟩) (Ob.Entry.sort _).toTele :=
      ⟨Subst.single S, Wf_t.cons Wf_t.nil Wf_bd.sort Wf_t.nil, Wf_e.fill hS hsortS⟩
    have hβl : Eq_bd Ξ (Ξ.boundaryOf l) (.of S) := by
      rw [hb]
      apply Eq_bd.of (Eq_e.refl hS)
    have hβr := Eq_bd.trans (Eq_bd.symm heq) hβl
    let τl : Ob.Fill (toOb ⟨Δ, Ξ, hΞ⟩) (Ob.Entry.of τS).toTele :=
      ⟨Subst.single l, (Ob.Entry.of τS).wf, Wf_e.fill hl hβl⟩
    let τr : Ob.Fill (toOb ⟨Δ, Ξ, hΞ⟩) (Ob.Entry.of τS).toTele :=
      ⟨Subst.single r, (Ob.Entry.of τS).wf, Wf_e.fill hr hβr⟩
    constructor
    · intro hlg hrg
      apply h.IdElement hob (hlg.2 S hb hΞ τS.2) (hlg.atom hl hβl hΞ _ τl.2)
        (hrg.atom hr hβr hΞ _ τr.2)
    · intro hty t
      apply h.IdElement_term (s := Tm₁.ofFill τS) (l := Tm₁.ofFill τl) (r := Tm₁.ofFill τr) t
        hob hty
  · apply absurd _ (Wf_e.boundary_not_isEq hl)
    rw [hb]
    trivial

/-- Over a context satisfying `P_Ob`, for `Θ` satisfying `TelGood` and `β` satisfying
`AtomGood` over `Ξ ⋈ Θ`, the type of the entry binding `Θ` and declaring `β` satisfies `P_Ty`,
and the term of that type filled by `t` satisfies `P_Tm` exactly when `t` satisfies
`AtomTermGood` for `β` over `Ξ ⋈ Θ`. -/
theorem TelGood.entry :
  ∀ {Δ γ : C.Arity} {Ξ : Ambient Δ} (Θ : dTel Δ γ) {β : Bd (Δ ⋈ γ)},
    ObGood P_Ob Ξ → TelGood P_Ty P_Tm Ξ Θ → AtomGood P_Ty P_Tm (Ξ ⋈ Θ) β →
    ∀ (hΞ : Ambient.Wf Ξ) (w : Wf_t Ξ (dTel.cons Θ β .nil)),
      P_Ty (Quotient.mk (Ob.Entry.setoid (toOb ⟨Δ, Ξ, hΞ⟩)) ⟨γ, Θ, β, w⟩) ∧
      ∀ (t : Expr (Δ ⋈ γ))
        (τw : Ob.Fill.Wf (toOb ⟨Δ, Ξ, hΞ⟩) (dTel.cons Θ β .nil) (Subst.single t)),
        P_Tm (Tm₁.ofFill (e := (⟨γ, Θ, β, w⟩ : Ob.Entry (toOb ⟨Δ, Ξ, hΞ⟩))) ⟨Subst.single t, τw⟩)
          ↔ AtomTermGood P_Tm (Ξ ⋈ Θ) β t
  | _, _, _, .nil, _, _, _, hA, hΞ, w => by
      erw [dTel.concatenate_nil] at hA ⊢
      use hA.1 hΞ w
      intro t τw
      exact ⟨fun hP _ _ _ => hP, fun hP => hP hΞ w τw⟩
  | Δ, _, Ξ, .cons Θ β Ψ, ε, hob, hΘ, hA, hΞ, w => by
      obtain ⟨hΘ, hAβ, hΨ⟩ := hΘ
      obtain ⟨w₁, w₂⟩ := bind_wf_inv w
      have hΞ₁ := Wf_t.concatenate hΞ w₁
      have hty₁ := (TelGood.entry Θ hob hΘ hAβ hΞ w₁).1
      have hob₁ : ObGood P_Ob (Ξ ⋈ dTel.cons Θ β .nil) := fun _ => h.extend (hob hΞ) hty₁
      have hAε : AtomGood P_Ty P_Tm (Ξ ⋈ dTel.cons Θ β .nil ⋈ Ψ) ε := by
        rw [dTel.concatenate_assoc]
        apply hA
      obtain ⟨hty₂, hΨt⟩ := TelGood.entry Ψ hob₁ hΨ hAε hΞ₁ w₂
      use h.Bind (hob hΞ) hty₁ hty₂
      intro t τw
      let e : Ob.Entry (toOb ⟨Δ, Ξ, hΞ⟩) := ⟨_, Θ, β, w₁⟩
      let f : Ob.Entry (extend ⟨Δ, Ξ, hΞ⟩ e.toTele) := ⟨_, Ψ, ε, w₂⟩
      have key := hΨt _ (unlamFill ⟨Δ, Ξ, hΞ⟩ e f ⟨Subst.single t, τw⟩).2
      erw [dTel.concatenate_assoc] at key
      apply Iff.trans _ key
      constructor
      · intro hP
        apply h.unlam (hob hΞ) hty₁ hty₂ hP
      · intro hP
        erw [← lam_unlam (a := Quotient.mk _ e) (c := Quotient.mk _ f)
          (Tm₁.ofFill ⟨Subst.single t, τw⟩)]
        apply h.lam (hob hΞ) hty₁ hty₂ hP

/-- Extending a context satisfying `P_Ob` by a telescope satisfying `TelGood` gives a context
satisfying `P_Ob`. -/
theorem TelGood.ob :
  ∀ {Δ Ω : C.Arity} {Ξ : Ambient Δ} (Θ : dTel Δ Ω),
    ObGood P_Ob Ξ → TelGood P_Ty P_Tm Ξ Θ → ObGood P_Ob (Ξ ⋈ Θ)
  | _, _, _, .nil, hob, _ => by
      erw [dTel.concatenate_nil]
      apply hob
  | _, _, Ξ, .cons Θ β Ψ, hob, hΘ => by
      obtain ⟨hΘ, hA, hΨ⟩ := hΘ
      have hob₁ : ObGood P_Ob (Ξ ⋈ dTel.cons Θ β .nil) := by
        intro hΞ₁
        obtain ⟨hΞ, w⟩ := Wf_t.concatenate_inv (Ξ := .nil) Ξ hΞ₁
        apply h.extend (hob hΞ) (TelGood.entry h Θ hob hΘ hA hΞ w).1
      have hext := TelGood.ob Ψ hob₁ hΨ
      erw [dTel.concatenate_assoc] at hext
      apply hext

/-- The lift of a substitution satisfying `P_Sub` between contexts satisfying `P_Ob` past the
one-entry telescope of an entry whose type satisfies `P_Ty` satisfies `P_Sub`. -/
theorem lift_entry {Γ Ξ : Ctx} (u : Ob.Entry Γ.toOb) (σ : Ob.Subst Ξ.toOb Γ.toOb)
    (hob : P_Ob Γ.toOb) (hob' : P_Ob Ξ.toOb) (hty : P_Ty (Quotient.mk _ u))
    (hσ : P_Sub (Quotient.mk _ σ)) :
  P_Sub (lift σ u.toTele)
  := by
  rw [← Ty₁.lift_mk, Ty₁.lift_eq_pair]
  have hty' := h.substTy hob hob' hty hσ
  have hext := h.extend hob' hty'
  apply h.pair hob hext hty (h.comp hob hob' hext hσ (h.projection hob' hty'))
  apply Tm₁.of_val _ (h.generic hob' hty')
  symm
  apply Tm₁.eq_of_heq (Ty₁.subst_comp _ _ _)
  apply eqRec_heq

/-- For `Ξ` satisfying `ObGood`, `Θ` satisfying `TelGood` over `Ξ`, `β` satisfying `AtomGood`
over `Ξ ⋈ Θ`, and a substitution `σ` whose lift past `Θ` satisfies `P_Sub`, the declaration `β`
reindexed along `σ` satisfies `AtomGood` over `Ξ'` followed by `Θ` reindexed along `σ`, when
that ambient satisfies `ObGood`. -/
theorem AtomGood.subst
    {Δ Δ' γ : C.Arity} {Ξ : Ambient Δ} {Ξ' : Ambient Δ'} {Θ : dTel Δ γ} {β : Bd (Δ ⋈ γ)}
    (hob : ObGood P_Ob Ξ) (hΘ : TelGood P_Ty P_Tm Ξ Θ) (hA : AtomGood P_Ty P_Tm (Ξ ⋈ Θ) β)
    {hΞ : Ambient.Wf Ξ} {hΞ' : Ambient.Wf Ξ'} (w : Wf_t Ξ (dTel.cons Θ β .nil))
    {σ : Ob.Subst (toOb ⟨Δ', Ξ', hΞ'⟩) (toOb ⟨Δ, Ξ, hΞ⟩)} {wΘ : Wf_t Ξ Θ}
    (hlift : P_Sub (lift σ ⟨γ, Θ, wΘ⟩)) (hobΘ' : ObGood P_Ob (Ξ' ⋈ dTel.actBase σ.1 Θ)) :
  AtomGood P_Ty P_Tm (Ξ' ⋈ dTel.actBase σ.1 Θ) (Bd.act (Γ := 1) σ.1 γ β)
  := by
  have hΞΘ := Wf_t.concatenate hΞ wΘ
  have hobΘ := TelGood.ob h Θ hob hΘ hΞΘ
  constructor
  · intro hΞ₁ w₁
    convert h.substTy hobΘ (hobΘ' hΞ₁) (hA.1 hΞΘ (Wf_t.atom w)) hlift using 1
    apply congrArg (Quotient.mk _)
    congr 1
    symm
    apply Bd.act_lift_depth
  · intro S hS hΞ₁ τw
    obtain ⟨S₀, rfl, rfl⟩ := Bd.act_of_inv _ _ hS
    have hsort := hA.2 S₀ rfl hΞΘ (Wf_t.sort_fill (Wf_t.atom w))
    apply Tm₁.of_val _ (h.substTm hobΘ (hobΘ' hΞ₁) (h.U hobΘ) hsort hlift)
    apply congrArg (Quotient.mk _)
    apply Ob.Term.ext rfl
    apply Eq.trans (Subst.applyEach_single (α := 1) (Subst.lift σ.1 γ) S₀)
    rw [Subst.act_lift_depth]
    rfl

/-- Reindexing a telescope `Θ` satisfying `TelGood` along a substitution satisfying `P_Sub`
between contexts satisfying `P_Ob` gives a telescope satisfying `TelGood`, and the lift of the
substitution past `Θ` satisfies `P_Sub`. -/
theorem TelGood.subst :
  ∀ {Δ Δ' γ : C.Arity} {Ξ : Ambient Δ} {Ξ' : Ambient Δ'} (Θ : dTel Δ γ),
    ObGood P_Ob Ξ → ObGood P_Ob Ξ' → TelGood P_Ty P_Tm Ξ Θ →
    ∀ (hΞ : Ambient.Wf Ξ) (hΞ' : Ambient.Wf Ξ') (wΘ : Wf_t Ξ Θ)
      (σ : Ob.Subst (toOb ⟨Δ', Ξ', hΞ'⟩) (toOb ⟨Δ, Ξ, hΞ⟩)), P_Sub (Quotient.mk _ σ) →
      TelGood P_Ty P_Tm Ξ' (dTel.actBase σ.1 Θ) ∧ P_Sub (lift σ ⟨γ, Θ, wΘ⟩)
  | _, _, _, Ξ, Ξ', .nil, _, _, _, _, _, _, σ, hσ => by
      use trivial
      apply sub_of_eq _ _ _ hσ
      · symm
        apply dTel.concatenate_nil
      · symm
        apply dTel.concatenate_nil
      · symm
        apply Subst.lift_one
  | Δ, Δ', _, Ξ, Ξ', .cons (α := α) (Δ := Ω) Θ β Ψ, hob, hob', hΘ, hΞ, hΞ', wΘ, σ, hσ => by
      obtain ⟨hΘ, hA, hΨ⟩ := hΘ
      obtain ⟨wΘ, wβ, wΨ⟩ := Wf_t.cons_inv wΘ
      have w := Wf_t.cons wΘ wβ Wf_t.nil
      have hty := (TelGood.entry h Θ hob hΘ hA hΞ w).1
      have hob₁ : ObGood P_Ob (Ξ ⋈ dTel.cons Θ β .nil) := fun _ => h.extend (hob hΞ) hty
      have hob₁' : ObGood P_Ob (Ξ' ⋈ dTel.actBase σ.1 (dTel.cons Θ β .nil)) :=
        fun _ => h.extend (hob' hΞ') (h.substTy (hob hΞ) (hob' hΞ') hty hσ)
      obtain ⟨hΘ', hliftΘ⟩ := TelGood.subst Θ hob hob' hΘ hΞ hΞ' wΘ σ hσ
      obtain ⟨hΨ', hliftΨ⟩ := TelGood.subst Ψ hob₁ hob₁' hΨ _ _ wΨ _
        (lift_entry h (Γ := ⟨Δ, Ξ, hΞ⟩) (Ξ := ⟨Δ', Ξ', hΞ'⟩) ⟨_, Θ, β, w⟩ σ (hob hΞ)
          (hob' hΞ') hty hσ)
      constructor
      · use hΘ', AtomGood.subst h hob hΘ hA w hliftΘ (TelGood.ob h _ hob' hΘ')
        apply hΨ'
      · apply sub_of_eq (dTel.concatenate_assoc _ _ _) (dTel.concatenate_assoc _ _ _) _ hliftΨ
        symm
        exact Subst.lift_assoc σ.1 (C.single α) Ω

/-- Extending a context satisfying `CtxGood` by an entry whose binding satisfies `TelGood` and
whose declaration satisfies `AtomGood` gives a context satisfying `CtxGood`. -/
theorem CtxGood.extend
    {Δ γ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ γ} {β : Bd (Δ ⋈ γ)}
    (hΞg : CtxGood P_Ob P_Ty P_Tm Ξ) (hΘ : TelGood P_Ty P_Tm Ξ Θ)
    (hA : AtomGood P_Ty P_Tm (Ξ ⋈ Θ) β) (hΞ : Ambient.Wf Ξ) (w : Wf_t Ξ (dTel.cons Θ β .nil)) :
  CtxGood P_Ob P_Ty P_Tm (Ξ ⋈ dTel.cons Θ β .nil)
  := by
  obtain ⟨hob, hslot⟩ := hΞg
  have hty := (TelGood.entry h Θ hob hΘ hA hΞ w).1
  have hΞ₁ := Wf_t.concatenate hΞ w
  have hob₁ : ObGood P_Ob (Ξ ⋈ dTel.cons Θ β .nil) := fun _ => h.extend (hob hΞ) hty
  have wθ := Ob.Subst.Wf.left (Γ := ⟨Δ, Ξ, hΞ⟩)
    (Θ := (⟨γ, Θ, β, w⟩ : Ob.Entry (toOb ⟨Δ, Ξ, hΞ⟩)).toTele) (Ob.Subst.id _)
  let θ : Ob.Subst (toOb ⟨_, Ξ ⋈ dTel.cons Θ β .nil, hΞ₁⟩) (toOb ⟨Δ, Ξ, hΞ⟩) :=
    ⟨Subst.ofRenaming (Renaming.inl Δ (C.single γ ⋈ 1)), wθ⟩
  have hθ : P_Sub (Quotient.mk _ θ) := h.projection (hob hΞ) hty
  apply And.intro hob₁
  intro α x
  rcases C.cover Δ (C.single γ ⋈ 1) x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · obtain ⟨hΘy, hAy, hVy⟩ := hslot y
    have wy := Wf_t.cons (Wf_t.binding hΞ y) (Wf_t.declaration hΞ y) Wf_t.nil
    obtain ⟨⟨hΘy', hAy', -⟩, -⟩ := TelGood.subst h (dTel.cons (Ξ.binding y) (Ξ.declaration y) .nil)
      hob hob₁ ⟨hΘy, hAy, trivial⟩ hΞ hΞ₁ wy θ hθ
    erw [dTel.actBase_ofRenaming] at hΘy' hAy'
    erw [Bd.act_ofRenaming] at hAy'
    rw [SlotGood, dTel.binding_concatenate_inl, dTel.declaration_concatenate_inl]
    use hΘy', hAy'
    intro hne hΞ₁' w' τw'
    have hne' : ¬ (Ξ.declaration y).isEq := fun he => hne ((Bd.isEq_rename _ _).mpr he)
    have hvar := hVy hne' hΞ wy ⟨wy, Wf_s.eta_single hΞ y hne'⟩
    apply Tm₁.of_val _
      (h.substTm (hob hΞ) (hob₁ hΞ₁) (TelGood.entry h _ hob hΘy hAy hΞ wy).1 hvar hθ)
    apply congrArg (Quotient.mk _)
    apply Ob.Term.ext
    · apply dTel.actBase_ofRenaming
    · apply Eq.trans (Subst.applyEach_single _ _)
      apply congrArg Subst.single
      apply Eq.trans (act_ofRenaming (Renaming.inl Δ (C.single γ ⋈ 1)) (Expr.η y))
      apply Renaming.act_eta
  · induction z using slotCases with
    | head =>
      obtain ⟨⟨hΘ', hA', -⟩, -⟩ := TelGood.subst h (dTel.cons Θ β .nil) hob hob₁
        ⟨hΘ, hA, trivial⟩ hΞ hΞ₁ w θ hθ
      erw [dTel.actBase_ofRenaming] at hΘ' hA'
      erw [Bd.act_ofRenaming] at hA'
      rw [SlotGood, dTel.binding_concatenate_inr, dTel.declaration_concatenate_inr,
        dTel.binding_head, dTel.declaration_head]
      use hΘ', hA'
      intro _ hΞ₁' w' τw'
      apply Tm₁.of_val _ (h.generic (hob hΞ) hty)
      apply congrArg (Quotient.mk _)
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Subtype.ext
        symm
        exact Subst.single_eta (Subst.instId Δ (C.single γ ⋈ 1))
    | tail v => exact (C.unit_is_empty v).elim

/-- Extending a context satisfying `CtxGood` by a telescope satisfying `TelGood` gives a
context satisfying `CtxGood`. -/
theorem CtxGood.append :
  ∀ {Δ Ω : C.Arity} {Ξ : Ambient Δ} (Θ : dTel Δ Ω), CtxGood P_Ob P_Ty P_Tm Ξ →
    TelGood P_Ty P_Tm Ξ Θ → Ambient.Wf Ξ → Wf_t Ξ Θ → CtxGood P_Ob P_Ty P_Tm (Ξ ⋈ Θ)
  | _, _, _, .nil, hΞg, _, _, _ => by
      erw [dTel.concatenate_nil]
      apply hΞg
  | _, _, _, .cons _ _ Ψ, hΞg, hΘ, hΞ, wΘ => by
      obtain ⟨hΘ, hA, hΨ⟩ := hΘ
      obtain ⟨wΘ, wβ, wΨ⟩ := Wf_t.cons_inv wΘ
      have w := Wf_t.cons wΘ wβ Wf_t.nil
      have hext := CtxGood.append Ψ (CtxGood.extend h hΞg hΘ hA hΞ w) hΨ
        (Wf_t.concatenate hΞ w) wΨ
      erw [dTel.concatenate_assoc] at hext
      apply hext

/-! ## Generation along derivations -/

mutual

/-- Over a well-formed ambient satisfying `CtxGood`, a well-formed telescope satisfies
`TelGood`. -/
theorem Wf_t.good :
  ∀ {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω}, Wf_t Ξ Θ → Ambient.Wf Ξ →
    CtxGood P_Ob P_Ty P_Tm Ξ → TelGood P_Ty P_Tm Ξ Θ
  | _, _, _, _, .nil, _, _ => trivial
  | _, _, _, _, .cons wΘ wβ wΨ, hΞ, hΞg => by
      have hΘ := Wf_t.good wΘ hΞ hΞg
      have w := Wf_t.cons wΘ wβ Wf_t.nil
      have hA := Wf_bd.good wβ (Wf_t.concatenate hΞ wΘ) (CtxGood.append h _ hΞg hΘ hΞ wΘ)
      have hΨ := Wf_t.good wΨ (Wf_t.concatenate hΞ w) (CtxGood.extend h hΞg hΘ hA hΞ w)
      exact ⟨hΘ, hA, hΨ⟩

/-- Over a well-formed ambient `Ξ ⋈ Θ` satisfying `CtxGood`, a declaration well formed over
`Ξ` with bound entries `Θ` satisfies `AtomGood` over `Ξ ⋈ Θ`. -/
theorem Wf_bd.good :
  ∀ {Δ Λ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Λ} {β : Bd (Δ ⋈ Λ)}, Wf_bd Ξ Θ β →
    Ambient.Wf (Ξ ⋈ Θ) → CtxGood P_Ob P_Ty P_Tm (Ξ ⋈ Θ) → AtomGood P_Ty P_Tm (Ξ ⋈ Θ) β
  | _, _, _, _, _, .sort, _, hΞg => ⟨fun hΞ' _ => h.U (hΞg.1 hΞ'), fun _ he => nomatch he⟩
  | _, _, Ξ, Θ, _, .of (S := S) hS hsort, hΞ, hΞg => by
      have hU : SortGood P_Tm (Ξ ⋈ Θ) (.of S) := by
        rintro _ ⟨⟩ hΞ' τw
        apply (Wf_e.good hS hΞ hΞg).atom hS hsort hΞ' _ τw
      constructor
      · intro hΞ' w
        apply h.El (hΞg.1 hΞ') (hU S rfl hΞ' (Wf_t.sort_fill w))
      · apply hU
  | _, _, _, _, _, .eq hl hr _, hΞ, hΞg => by
      constructor
      · intro hΞ' w
        apply (eq_good h w (hΞg.1 hΞ') rfl).1 (Wf_e.good hl hΞ hΞg) (Wf_e.good hr hΞ hΞg)
      · intro _ he
        nomatch he

/-- Over a well-formed ambient satisfying `CtxGood`, a well-formed expression satisfies
`ExprGood`. -/
theorem Wf_e.good :
  ∀ {Δ : C.Arity} {Ξ : Ambient Δ} {e : Expr Δ}, Wf_e Ξ e → Ambient.Wf Ξ →
    CtxGood P_Ob P_Ty P_Tm Ξ → ExprGood P_Tm Ξ e
  | Δ, Ξ, _, .ap (α := α) x args head fill, hΞ, hΞg => by
      obtain ⟨hΘx, hAx, hVx⟩ := hΞg.2 x
      have hob := hΞg.1
      have wΘ := Wf_t.binding hΞ x
      have wx := Wf_t.cons wΘ (Wf_t.declaration hΞ x) Wf_t.nil
      have hΞΘ := Wf_t.concatenate hΞ wΘ
      have hobΘ := TelGood.ob h _ hob hΘx hΞΘ
      have heta := Wf_s.eta_single hΞ x head
      have hatom := ((TelGood.entry h _ hob hΘx hAx hΞ wx).2 (Expr.η x) ⟨wx, heta⟩).mp
        (hVx head hΞ wx ⟨wx, heta⟩)
      have wa := Wf_t.atom wx
      have hηfill : Wf_s (Ξ ⋈ Ξ.binding x) (dTel.cons .nil (Ξ.declaration x) .nil)
          (Subst.single (Δ := Δ ⋈ α) (α := 1) (Expr.η x : Expr (Δ ⋈ α))) := by
        apply Wf_e.fill (Wf_e.eta Ξ x wΘ head)
        rw [dTel.boundaryOf_eta]
        apply Wf_bd.refl (Wf_t.declaration hΞ x)
      have hslot := hatom hΞΘ wa ⟨wa, hηfill⟩
      have hsec := Wf_s.good fill hΞ hΞg hΘx wΘ
      constructor
      · intro hΞ' w' τw'
        apply Tm₁.of_val _ (h.substTm hobΘ (hob hΞ) (hAx.1 hΞΘ wa) hslot hsec)
        apply congrArg (Quotient.mk _)
        apply Ob.Term.ext
        · apply congrArg (fun β => dTel.cons .nil β .nil)
          apply Bd.act_copair_prefix
        · apply Eq.trans (Subst.applyEach_single _ _)
          apply congrArg Subst.single
          apply act_copair_eta
      · intro S hS hΞ' τw'
        obtain ⟨S₀, hS₀, rfl⟩ := Bd.act_of_inv (Ξ := 1) args 1 (β := Ξ.declaration x) hS
        have hsort := hAx.2 S₀ hS₀ hΞΘ (Wf_t.sort_fill (hS₀ ▸ wa))
        apply Tm₁.of_val _ (h.substTm hobΘ (hob hΞ) (h.U hobΘ) hsort hsec)
        apply congrArg (Quotient.mk _)
        apply Ob.Term.ext rfl
        apply Eq.trans (Subst.applyEach_single _ S₀)
        apply congrArg Subst.single
        apply act_copair_prefix

/-- Over a well-formed ambient `Ξ` satisfying `CtxGood`, for a filling `σ` of a well-formed
telescope `Θ` satisfying `TelGood`, the substitution `Subst.copair (Subst.id Δ) σ` from `Ξ` into
`Ξ ⋈ Θ` satisfies `P_Sub`. -/
theorem Wf_s.good :
  ∀ {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω} {σ : Subst Ω Δ} (hσ : Wf_s Ξ Θ σ)
    (hΞ : Ambient.Wf Ξ), CtxGood P_Ob P_Ty P_Tm Ξ → TelGood P_Ty P_Tm Ξ Θ →
    ∀ (wΘ : Wf_t Ξ Θ),
      P_Sub (Quotient.mk _ (⟨Subst.copair (Subst.id Δ) σ, (Wf_s.toSub hΞ hσ).toFilling⟩ :
        Ob.Subst (toOb ⟨Δ, Ξ, hΞ⟩) (toOb ⟨_, Ξ ⋈ Θ, Wf_t.concatenate hΞ wΘ⟩)))
  | Δ, _, Ξ, _, σ, .nil, hΞ, hΞg, _, _ => by
      apply sub_of_eq _ rfl _ (h.identity (hΞg.1 hΞ))
      · symm
        apply dTel.concatenate_nil
      · funext α x
        rcases C.cover Δ 1 x with ⟨y, rfl⟩ | ⟨z, rfl⟩
        · symm
          apply Eq.trans (Subst.copair_inl _ _ y)
          rw [C.unit_right]
          rfl
        · exact (C.unit_is_empty z).elim
  | Δ, _, Ξ, .cons (α := α) Θ β Ψ, σ, hσ@(.cons _ filler declared hrest), hΞ, hΞg,
      hΘ, wΘ => by
      obtain ⟨hΘ, hA, hΨ⟩ := hΘ
      obtain ⟨wΘ, wβ, wΨ⟩ := Wf_t.cons_inv wΘ
      have w := Wf_t.cons wΘ wβ Wf_t.nil
      have hΞΘ := Wf_t.concatenate hΞ wΘ
      have hΞ₁ := Wf_t.concatenate hΞ w
      have hob := hΞg.1
      obtain ⟨hty, hΘt⟩ := TelGood.entry h Θ hob hΘ hA hΞ w
      have hob₁ : ObGood P_Ob (Ξ ⋈ dTel.cons Θ β .nil) := fun _ => h.extend (hob hΞ) hty
      have hatom : AtomTermGood P_Tm (Ξ ⋈ Θ) β (σ (C.inl (C.singleSlot α))) := by
        by_cases hne : β.isEq
        · obtain ⟨l, r, rfl⟩ := Bd.eq_of_isEq hne
          intro hΞ' w' τw'
          apply (eq_good h w' (TelGood.ob h Θ hob hΘ hΞ') rfl).2 (hA.1 hΞ' w')
        · apply (Wf_e.good (filler hne) hΞΘ (CtxGood.append h Θ hΞg hΘ hΞ wΘ)).atom (filler hne)
            (declared hne)
      have τw : Ob.Fill.Wf (toOb ⟨Δ, Ξ, hΞ⟩) (dTel.cons Θ β .nil)
          (Subst.single (σ (C.inl (C.singleSlot α)))) := by
        rw [Subst.single_restrict]
        exact ⟨w, Wf_s.head hσ⟩
      let u : Ob.Entry (toOb ⟨Δ, Ξ, hΞ⟩) := ⟨α, Θ, β, w⟩
      have τ₀w : Ob.Fill.Wf (toOb ⟨Δ, Ξ, hΞ⟩)
          (dTel.cons (dTel.actBase (Subst.id Δ) Θ) (Bd.act (Γ := 1) (Subst.id Δ) α β) .nil)
          (fun ⦃γ⦄ (i : C.single α ∋ γ) => σ (C.inl i)) := by
        erw [dTel.actBase_id, Bd.act_id]
        exact ⟨w, Wf_s.head hσ⟩
      have ht₀ : P_Tm (Tm₁.ofFill (e := Ob.Entry.subst (Ob.Subst.id _) u)
          ⟨fun ⦃γ⦄ (i : C.single α ∋ γ) => σ (C.inl i), τ₀w⟩) := by
        apply Tm₁.of_val _ ((hΘt _ τw).mpr hatom)
        apply congrArg (Quotient.mk _)
        apply Ob.Term.ext
        · congr 1
          · symm
            apply dTel.actBase_id
          · symm
            apply Bd.act_id
        · apply Subst.single_restrict
      have wθ := Ob.Subst.Wf.pair (Γ := ⟨Δ, Ξ, hΞ⟩) (Θ := u.toTele) (Ob.Subst.id _) _ τ₀w
      let θ : Ob.Subst (toOb ⟨Δ, Ξ, hΞ⟩) (toOb ⟨_, Ξ ⋈ dTel.cons Θ β .nil, hΞ₁⟩) :=
        ⟨Subst.copair (Subst.id Δ) (fun ⦃γ⦄ (i : C.single α ∋ γ) => σ (C.inl i)), wθ⟩
      have hθ : P_Sub (Quotient.mk _ θ) :=
        h.pair (a := Quotient.mk _ u) (hob hΞ) (hob hΞ) hty (h.identity (hob hΞ)) ht₀
      obtain ⟨hΨ', hliftΨ⟩ := TelGood.subst h Ψ hob₁ hob hΨ hΞ₁ hΞ wΨ θ hθ
      have wΨ' := Wf_t.subst_ambient θ.2.toWf_sub wΨ
      have hcomp := h.comp (TelGood.ob h Ψ hob₁ hΨ (Wf_t.concatenate hΞ₁ wΨ))
        (TelGood.ob h _ hob hΨ' (Wf_t.concatenate hΞ wΨ')) (hob hΞ) hliftΨ
        (Wf_s.good hrest hΞ hΞg hΨ' wΨ')
      apply sub_of_eq (dTel.concatenate_assoc _ _ _) rfl _ hcomp
      apply Subst.copair_split

end

/-- Every well-formed ambient satisfies `CtxGood`. -/
theorem CtxGood.of_wf {Δ : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ) :
  CtxGood P_Ob P_Ty P_Tm Ξ
  := by
  have hnil : CtxGood P_Ob P_Ty P_Tm (.nil : Ambient 1) :=
    ⟨fun _ => h.empty, fun _ x => (C.unit_is_empty x).elim⟩
  apply CtxGood.append h Ξ hnil (Wf_t.good h hΞ Wf_t.nil hnil) Wf_t.nil hΞ

/-- A family of predicates on the objects, substitutions, types and terms of `Ctx.model`
closed under its operations holds of every object, substitution, type and term. -/
theorem generated :
  (∀ X, P_Ob X) ∧ (∀ {X Y : Ob} (f : Y ⟶ X), P_Sub f) ∧ (∀ {X : Ob} (a : Ty₁ X), P_Ty a) ∧
    ∀ {X : Ob} {a : Ty₁ X} (t : Tm₁ X a), P_Tm t
  := by
  have hOb : ∀ X, P_Ob X := by
    intro X
    induction X using Ob.ind with
    | h Γ =>
    apply (CtxGood.of_wf h Γ.wf).1 Γ.wf
  have hSub : ∀ {X Y : Ob} (f : Y ⟶ X), P_Sub f := by
    intro X Y
    induction X using Ob.ind with
    | h Γ' =>
    induction Y using Ob.ind with
    | h Γ =>
    intro f
    induction f using Quotient.ind with
    | _ σ =>
    obtain ⟨Δ', Ξ', hΞ'⟩ := Γ'
    obtain ⟨Δ, Ξ, hΞ⟩ := Γ
    obtain ⟨σ, hσ⟩ := σ
    let κ : Ob.Subst (toOb ⟨Δ, Ξ, hΞ⟩) (toOb ⟨1, .nil, Wf_t.nil⟩) :=
      ⟨fun ⦃_⦄ x => (C.unit_is_empty x).elim, Wf_s.nil⟩
    have eΘ : dTel.actBase κ.1 Ξ' = dTel.rename (Renaming.fromUnit Δ) Ξ' := by
      rw [← dTel.actBase_ofRenaming]
      congr 1
      funext α x
      exact (C.unit_is_empty x).elim
    have hσ' : Wf_s Ξ (dTel.actBase κ.1 Ξ') σ := eΘ ▸ hσ
    have wΘ : Wf_t Ξ (dTel.actBase κ.1 Ξ') := eΘ ▸ Ambient.Wf.weaken hΞ' Ξ
    have hctx := CtxGood.of_wf h hΞ
    have hΘ := Wf_t.good h hΞ' Wf_t.nil (CtxGood.of_wf h Wf_t.nil)
    obtain ⟨-, hlift⟩ := TelGood.subst h Ξ' (fun _ => hOb _) hctx.1 hΘ Wf_t.nil hΞ hΞ' κ
      (h.toEmpty (hOb _))
    have hsec := Wf_s.good h hσ' hΞ hctx (Wf_t.good h wΘ hΞ hctx) wΘ
    apply sub_of_eq rfl rfl _ (h.comp (hOb _) (hOb _) (hOb _) hlift hsec)
    funext α x
    rcases C.cover 1 Δ' x with ⟨z, rfl⟩ | ⟨y, rfl⟩
    · exact (C.unit_is_empty z).elim
    · apply Eq.trans (congrArg (Subst.act (Γ := 1) (Subst.copair (Subst.id Δ) σ) α)
        (Subst.lift_inr κ.1 y))
      apply Eq.trans (act_η _ α (C.inr y))
      apply Eq.trans (Subst.copair_inr _ _ y)
      rw [C.unit_left]
  have hTy : ∀ {X : Ob} (a : Ty₁ X), P_Ty a := by
    intro X
    induction X using Ob.ind with
    | h Γ =>
    intro a
    induction a using Quotient.ind with
    | _ u =>
    obtain ⟨γ, Θ, β, w⟩ := u
    have hctx := CtxGood.of_wf h Γ.wf
    obtain ⟨hΘ, hA, -⟩ := Wf_t.good h w Γ.wf hctx
    apply (TelGood.entry h Θ hctx.1 hΘ hA Γ.wf w).1
  use hOb, hSub, hTy
  intro X a t
  have ht : Ob.Term.tele t.1 = Ty.map (𝟙 X).op a.toTy := by
    rw [t.2, op_id, Functor.map_id_apply]
  apply Tm₁.of_val _ (h.substTm (σ := Ob.pair (𝟙 X) t.1 ht) (hOb _) (hOb X) (hTy _)
    (h.generic (hOb X) (hTy a)) (hSub _))
  apply Ob.pair_generic

end Closure

end Ctx
