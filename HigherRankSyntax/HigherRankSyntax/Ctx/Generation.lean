import HigherRankSyntax.Ctx.Model
import HigherRankSyntax.HrS.Closed

/-!
# `Ctx.model` is generated

A family of predicates on the objects, substitutions, types and terms of `Ctx.model` closed
under its operations holds of all of them (`generated`).  For such a family, predicates on raw
ambients, telescopes, declarations and expressions (`CtxGood`, `TelGood`, `AtomGood`,
`ExprGood`) hold along every well-formedness derivation (`Wf_t.good`, `Wf_bd.good`,
`Wf_e.good`, `Wf_s.good`).
-/

open CategoryTheory

/-! ## Well-formedness -/

/-- If `Θ ⋈ Ψ` is well formed over `Ξ`, then `Θ` is well formed over `Ξ` and `Ψ` over
`Ξ ⋈ Θ`. -/
theorem Wf_t.concatenate_inv {Δ : C.Arity} {Ξ : Ambient Δ} :
  ∀ {Ω Φ : C.Arity} (Θ : dTel Δ Ω) {Ψ : dTel (Δ ⋈ Ω) Φ},
    Wf_t Ξ (dTel.concatenate Θ Ψ) → Wf_t Ξ Θ ∧ Wf_t (Ξ ⋈ Θ) Ψ
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
    (h : Wf_bd Ξ (dTel.concatenate Θ Ψ) β) :
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
  erw [dTel.concatenate_nil]
  apply hβ

/-- An equation well formed over `Ξ` with no bound entries has sides well formed over `Ξ` with
equal computed boundaries. -/
theorem Wf_bd.nil_eq {Δ : C.Arity} {Ξ : Ambient Δ} {l r : Expr Δ}
    (h : Wf_bd Ξ .nil (.eq l r)) :
  Wf_e Ξ l ∧ Wf_e Ξ r ∧ Eq_bd Ξ (Ξ.boundaryOf l) (Ξ.boundaryOf r)
  := by
  have hl := h.eq_left
  have hr := h.eq_right
  have heq := h.eq_boundary
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
      have hatom := Wf_t.atom (Wf_t.cons (Wf_t.binding hΞ x) (Wf_t.declaration hΞ x) Wf_t.nil)
      obtain ⟨-, hβ, -⟩ := Wf_t.cons_inv (Wf_t.instantiate fill hatom)
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

/-- A boundary equal to `sort` is `sort`. -/
theorem Eq_bd.sort_inv {Δ : C.Arity} {Ξ : Ambient Δ} :
  ∀ {β : Bd Δ}, Eq_bd Ξ .sort β → β = .sort
  | _, .sort => rfl

/-- A boundary equal to `of S` is `of S'` with `S` equal to `S'`. -/
theorem Eq_bd.of_inv {Δ : C.Arity} {Ξ : Ambient Δ} {S : Expr Δ} :
  ∀ {β : Bd Δ}, Eq_bd Ξ (.of S) β → ∃ S', β = .of S' ∧ Eq_e Ξ S S'
  | _, .of h => ⟨_, rfl, h⟩

/-- A well-formed expression whose computed boundary is equal to `β` fills the entry binding
nothing and declaring `β`. -/
theorem Wf_e.fill {Δ : C.Arity} {Ξ : Ambient Δ} {e : Expr Δ} {β : Bd Δ} (he : Wf_e Ξ e)
    (hβ : Eq_bd Ξ (Ξ.boundaryOf e) β) :
  Wf_s Ξ (dTel.cons .nil β .nil) (Subst.single (Δ := Δ) (α := 1) e)
  := by
  apply (Wf_s.single_iff (Δ := Δ) (α := 1) e).mpr
  erw [dTel.concatenate_nil]
  constructor
  · intro l r hlr
    subst hlr
    exact absurd ((Eq_bd.isEq hβ).mpr trivial) (Wf_e.boundary_not_isEq he)
  · exact ⟨fun _ => he, fun _ => hβ⟩

/-- An entry binding nothing and declaring `.of S`, well formed over `Ξ`, makes
`Subst.single S` a filling of the entry binding nothing and declaring a sort. -/
theorem Wf_t.sort_fill {Δ : C.Arity} {Ξ : Ambient Δ} {S : Expr Δ}
    (h : Wf_t Ξ (dTel.cons .nil (.of S) .nil)) :
  Wf_t Ξ (dTel.cons .nil .sort .nil) ∧
    Wf_s Ξ (dTel.cons .nil .sort .nil) (Subst.single (Δ := Δ) (α := 1) S)
  := by
  obtain ⟨-, hβ, -⟩ := Wf_t.cons_inv h
  obtain ⟨hS, hsort⟩ := Wf_bd.nil_of hβ
  exact ⟨Wf_t.cons Wf_t.nil Wf_bd.sort Wf_t.nil, Wf_e.fill hS hsort⟩

/-- For a slot `x` of a well-formed ambient `Ξ` whose declaration is not an equation,
`Subst.single (Expr.η x)` fills the entry binding `Ξ.binding x` and declaring
`Ξ.declaration x`. -/
theorem Wf_s.eta_single {Δ α : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ) (x : Δ ∋ α)
    (hne : ¬ (Ξ.declaration x).isEq) :
  Wf_s Ξ (dTel.cons (Ξ.binding x) (Ξ.declaration x) .nil) (Subst.single (Expr.η x))
  := by
  apply (Wf_s.single_iff (Expr.η x)).mpr
  constructor
  · intro l r he
    rw [he] at hne
    exact absurd trivial hne
  constructor
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

/-- The first filler of a filling of `C.single α ⋈ Ω`, as a filling of `C.single α ⋈ 1`, is
its restriction to `C.single α`. -/
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

/-- Entries with the same binding and equal declarations are equal. -/
theorem Ob.Entry.congr_declaration {X : Ob} {γ : C.Arity} {Θ : dTel X.arity γ}
    {β β' : Bd (X.arity ⋈ γ)} (e : β = β') {w : Ob.Tele.Wf X (dTel.cons Θ β .nil)}
    {w' : Ob.Tele.Wf X (dTel.cons Θ β' .nil)} :
  (⟨γ, Θ, β, w⟩ : Ob.Entry X) = ⟨γ, Θ, β', w'⟩
  := by
  subst e
  rfl

/-- Contexts with equal ambients have the same class. -/
theorem toOb_congr {Δ : C.Arity} {Ξ Ξ' : Ambient Δ} (e : Ξ = Ξ')
    {h : Ambient.Wf Ξ} {h' : Ambient.Wf Ξ'} :
  toOb ⟨Δ, Ξ, h⟩ = toOb ⟨Δ, Ξ', h'⟩
  := by
  subst e
  rfl

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

/-- For every entry of `Θ`, the entries its slot binds satisfy `TelGood` over the entries
before it, and its declaration satisfies `AtomGood` over the entries before it followed by
the entries its slot binds. -/
def TelGood : {Δ Ω : C.Arity} → Ambient Δ → dTel Δ Ω → Prop
  | _, _, _, .nil => True
  | _, _, Ξ, .cons Θ β Ψ =>
      TelGood Ξ Θ ∧ AtomGood P_Ty P_Tm (Ξ ⋈ Θ) β ∧ TelGood (Ξ ⋈ dTel.cons Θ β .nil) Ψ

/-- Over every context with ambient `Ξ`, every term of the type of the entry binding nothing
and declaring `β` filled by `t` satisfies `P_Tm`. -/
def AtomTermGood {Δ : C.Arity} (Ξ : Ambient Δ) (β : Bd Δ) (t : Expr Δ) : Prop :=
  ∀ (hΞ : Ambient.Wf Ξ) (w : Wf_t Ξ (dTel.cons .nil β .nil))
    (τw : Ob.Fill.Wf (toOb ⟨Δ, Ξ, hΞ⟩) (dTel.cons .nil β .nil)
      (Subst.single (Δ := Δ) (α := 1) t)),
    P_Tm (Tm₁.ofFill (e := (⟨1, .nil, β, w⟩ : Ob.Entry (toOb ⟨Δ, Ξ, hΞ⟩)))
      ⟨Subst.single (Δ := Δ) (α := 1) t, τw⟩)

/-- The entries the slot `x` of `Ξ` binds satisfy `TelGood` over `Ξ`, its declaration
satisfies `AtomGood` over `Ξ` followed by those entries, and, if the declaration is not an
equation, the term of the type of the entry of `x` filled by the η-expansion of `x`
satisfies `P_Tm`. -/
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

/-- Every term of the type of the entry binding nothing and declaring the computed boundary of
`e`, filled by `e`, satisfies `P_Tm`, and the computed boundary of `e` satisfies
`SortGood`. -/
def ExprGood {Δ : C.Arity} (Ξ : Ambient Δ) (e : Expr Δ) : Prop :=
  AtomTermGood P_Tm Ξ (Ξ.boundaryOf e) e ∧ SortGood P_Tm Ξ (Ξ.boundaryOf e)

end Good

/-! ## Consequences of closure -/

section Closure

variable {P_Ob : Ob → Prop} {P_Sub : ∀ {X Y : Ob}, (Y ⟶ X) → Prop}
  {P_Ty : ∀ {X : Ob}, Ty₁ X → Prop} {P_Tm : ∀ {X : Ob} {a : Ty₁ X}, Tm₁ X a → Prop}
  (h : model.Closed P_Ob P_Sub P_Ty P_Tm)

/-- A term satisfying `P_Tm` transports to every term with the same underlying class. -/
theorem Tm₁.of_val {X : Ob} {a a' : Ty₁ X} {t : Tm₁ X a} {t' : Tm₁ X a'}
    (e : t.1 = t'.1) (hP : P_Tm t) :
  P_Tm t'
  := by
  obtain rfl : a = a' := by
    apply Ty₁.toTy_injective
    rw [← t.2, ← t'.2, e]
  obtain rfl : t = t' := Subtype.ext e
  apply hP

/-- `P_Sub` transports along heterogeneous equality of morphisms between equal objects. -/
theorem sub_of_heq {X X' Y Y' : Ob} (eX : X = X') (eY : Y = Y') {f : Y ⟶ X} {f' : Y' ⟶ X'}
    (hf : HEq f f') (hP : P_Sub f) :
  P_Sub f'
  := by
  subst eX eY
  cases hf
  apply hP

/-- `P_Ty` transports along heterogeneous equality of types over equal objects. -/
theorem ty_of_heq {X X' : Ob} (eX : X = X') {a : Ty₁ X} {a' : Ty₁ X'} (ha : HEq a a')
    (hP : P_Ty a) :
  P_Ty a'
  := by
  subst eX
  cases ha
  apply hP

/-- Terms of the types of entries binding nothing with equal declarations, filled by the same
expression, have the same underlying class. -/
theorem atom_val_eq {Δ : C.Arity} {Ξ : Ambient Δ} {hΞ : Ambient.Wf Ξ} {β β' : Bd Δ}
    (hββ : Eq_bd Ξ β β') {t : Expr Δ} {w : Wf_t Ξ (dTel.cons .nil β .nil)}
    {w' : Wf_t Ξ (dTel.cons .nil β' .nil)}
    {τw : Ob.Fill.Wf (toOb ⟨Δ, Ξ, hΞ⟩) (dTel.cons .nil β .nil)
      (Subst.single (Δ := Δ) (α := 1) t)}
    {τw' : Ob.Fill.Wf (toOb ⟨Δ, Ξ, hΞ⟩) (dTel.cons .nil β' .nil)
      (Subst.single (Δ := Δ) (α := 1) t)} :
  (Tm₁.ofFill (e := (⟨1, .nil, β, w⟩ : Ob.Entry (toOb ⟨Δ, Ξ, hΞ⟩))) ⟨Subst.single t, τw⟩).1
    = (Tm₁.ofFill (e := (⟨1, .nil, β', w'⟩ : Ob.Entry (toOb ⟨Δ, Ξ, hΞ⟩)))
        ⟨Subst.single t, τw'⟩).1
  := by
  have hββ' : Eq_bd (Ξ ⋈ .nil) β β' := by
    erw [dTel.concatenate_nil]
    apply hββ
  apply Quotient.sound
  exact ⟨rfl, ⟨w, Eq_t.cons Eq_t.nil hββ' Eq_t.nil⟩, w, τw.2, Eq_s.refl τw.2⟩

include h

/-- Over a context satisfying `P_Ob`, every term of a type presented by an entry binding
nothing and declaring an equation satisfies `P_Tm` when the type satisfies `P_Ty`. -/
theorem eq_term {Δ : C.Arity} {Ξ : Ambient Δ} {hΞ : Ambient.Wf Ξ} {l r : Expr Δ}
    (w : Wf_t Ξ (dTel.cons .nil (.eq l r) .nil)) (hob : P_Ob (toOb ⟨Δ, Ξ, hΞ⟩))
    {a : Ty₁ (toOb ⟨Δ, Ξ, hΞ⟩)} (ha : Quotient.mk _ ⟨1, .nil, .eq l r, w⟩ = a) (hty : P_Ty a)
    (t : Tm₁ _ a) :
  P_Tm t
  := by
  obtain ⟨-, hβ, -⟩ := Wf_t.cons_inv w
  obtain ⟨hl, hr, heq⟩ := Wf_bd.nil_eq hβ
  have hbl := Wf_e.boundary hΞ hl
  have hne := Wf_e.boundary_not_isEq hl
  rcases hb : Ξ.boundaryOf l with _ | S | ⟨_, _⟩
  · rw [hb] at heq
    have hβl : Eq_bd Ξ (Ξ.boundaryOf l) .sort := by
      rw [hb]
      apply Eq_bd.sort
    have hβr : Eq_bd Ξ (Ξ.boundaryOf r) .sort := by
      rw [Eq_bd.sort_inv heq]
      apply Eq_bd.sort
    have hsort : Wf_t Ξ (dTel.cons .nil .sort .nil) := Wf_t.cons Wf_t.nil Wf_bd.sort Wf_t.nil
    let τl : Ob.Fill (toOb ⟨Δ, Ξ, hΞ⟩) (Ob.Entry.sort _).toTele :=
      ⟨Subst.single l, hsort, Wf_e.fill hl hβl⟩
    let τr : Ob.Fill (toOb ⟨Δ, Ξ, hΞ⟩) (Ob.Entry.sort _).toTele :=
      ⟨Subst.single r, hsort, Wf_e.fill hr hβr⟩
    obtain rfl : a = model.IdSort (Tm₁.ofFill τl) (Tm₁.ofFill τr) := by
      rw [← ha]
      apply congrArg (Quotient.mk _)
      apply Ob.Entry.congr_declaration
      symm
      exact congrArg₂ Bd.eq (Subst.single_head (Δ := Δ) (α := 1) l)
        (Subst.single_head (Δ := Δ) (α := 1) r)
    apply h.IdSort_term _ hob hty
  · rw [hb] at heq hbl
    obtain ⟨S', hS', hSS'⟩ := Eq_bd.of_inv heq
    obtain ⟨hS, hsortS⟩ := Wf_bd.nil_of hbl
    let τS : Ob.Fill (toOb ⟨Δ, Ξ, hΞ⟩) (Ob.Entry.sort _).toTele :=
      ⟨Subst.single S, Wf_t.cons Wf_t.nil Wf_bd.sort Wf_t.nil, Wf_e.fill hS hsortS⟩
    have hdecl : (Ob.Entry.of τS).declaration = .of S :=
      congrArg Bd.of (Subst.single_head (Δ := Δ) (α := 1) S)
    have hβl : Eq_bd Ξ (Ξ.boundaryOf l) (Ob.Entry.of τS).declaration := by
      rw [hb, hdecl]
      apply Eq_bd.of (Eq_e.refl hS)
    have hβr : Eq_bd Ξ (Ξ.boundaryOf r) (Ob.Entry.of τS).declaration := by
      rw [hS', hdecl]
      apply Eq_bd.of (Eq_e.symm hSS')
    let τl : Ob.Fill (toOb ⟨Δ, Ξ, hΞ⟩) (Ob.Entry.of τS).toTele :=
      ⟨Subst.single l, (Ob.Entry.of τS).wf, Wf_e.fill hl hβl⟩
    let τr : Ob.Fill (toOb ⟨Δ, Ξ, hΞ⟩) (Ob.Entry.of τS).toTele :=
      ⟨Subst.single r, (Ob.Entry.of τS).wf, Wf_e.fill hr hβr⟩
    obtain rfl : a = model.IdElement (S := Tm₁.ofFill τS) (Tm₁.ofFill τl) (Tm₁.ofFill τr) := by
      rw [← ha]
      apply congrArg (Quotient.mk _)
      apply Ob.Entry.congr_declaration
      symm
      exact congrArg₂ Bd.eq (Subst.single_head (Δ := Δ) (α := 1) l)
        (Subst.single_head (Δ := Δ) (α := 1) r)
    apply h.IdElement_term _ hob hty
  · rw [hb] at hne
    exact absurd trivial hne

/-- Over a context satisfying `P_Ob`, the type of the entry binding `Θ` and declaring `β`
satisfies `P_Ty` when `Θ` satisfies `TelGood` and `β` satisfies `AtomGood` over `Ξ ⋈ Θ`. -/
theorem TelGood.entry :
  ∀ {Δ γ : C.Arity} {Ξ : Ambient Δ} (Θ : dTel Δ γ) {β : Bd (Δ ⋈ γ)},
    ObGood P_Ob Ξ → TelGood P_Ty P_Tm Ξ Θ → AtomGood P_Ty P_Tm (Ξ ⋈ Θ) β →
    ∀ (hΞ : Ambient.Wf Ξ) (w : Wf_t Ξ (dTel.cons Θ β .nil)),
      P_Ty (Quotient.mk (Ob.Entry.setoid (toOb ⟨Δ, Ξ, hΞ⟩)) ⟨γ, Θ, β, w⟩)
  | _, _, _, .nil, _, _, _, hA => by
      erw [dTel.concatenate_nil] at hA
      apply hA.1
  | _, _, Ξ, .cons Θ β Ψ, ε, hob, hΘ, hA => by
      intro hΞ w
      obtain ⟨hΘ, hAβ, hΨ⟩ := hΘ
      obtain ⟨w₁, w₂⟩ := bind_wf_inv w
      have hty := TelGood.entry Θ hob hΘ hAβ hΞ w₁
      have hob₁ : ObGood P_Ob (Ξ ⋈ dTel.cons Θ β .nil) := fun _ => h.extend (hob hΞ) hty
      have hAε : AtomGood P_Ty P_Tm (Ξ ⋈ dTel.cons Θ β .nil ⋈ Ψ) ε := by
        rw [dTel.concatenate_assoc]
        apply hA
      have hty₂ := TelGood.entry Ψ hob₁ hΨ hAε (Wf_t.concatenate hΞ w₁) w₂
      exact h.Bind (hob hΞ) hty hty₂

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
        apply h.extend (hob hΞ) (TelGood.entry h Θ hob hΘ hA hΞ w)
      have hext := TelGood.ob Ψ hob₁ hΨ
      erw [dTel.concatenate_assoc] at hext
      apply hext

/-- The term of the entry binding `Θ` and declaring `β` filled by `t` satisfies `P_Tm` exactly
when every term of the entry binding nothing and declaring `β` over `Ξ ⋈ Θ` filled by `t`
does. -/
theorem TelGood.unlam :
  ∀ {Δ γ : C.Arity} {Ξ : Ambient Δ} (Θ : dTel Δ γ) {β : Bd (Δ ⋈ γ)} (t : Expr (Δ ⋈ γ)),
    ObGood P_Ob Ξ → TelGood P_Ty P_Tm Ξ Θ → AtomGood P_Ty P_Tm (Ξ ⋈ Θ) β →
    ∀ (hΞ : Ambient.Wf Ξ) (w : Wf_t Ξ (dTel.cons Θ β .nil))
      (τw : Ob.Fill.Wf (toOb ⟨Δ, Ξ, hΞ⟩) (dTel.cons Θ β .nil) (Subst.single t)),
      P_Tm (Tm₁.ofFill (e := (⟨γ, Θ, β, w⟩ : Ob.Entry (toOb ⟨Δ, Ξ, hΞ⟩))) ⟨Subst.single t, τw⟩)
        ↔ AtomTermGood P_Tm (Ξ ⋈ Θ) β t
  | _, _, Ξ, .nil, β, t, _, _, _, hΞ, w, τw => by
      erw [dTel.concatenate_nil]
      constructor
      · intro hP hΞ' w' τw'
        apply hP
      · intro hP
        apply hP hΞ w τw
  | Δ, _, Ξ, .cons Θ β Ψ, ε, t, hob, hΘ, hA, hΞ, w, τw => by
      obtain ⟨hΘ, hAβ, hΨ⟩ := hΘ
      obtain ⟨w₁, w₂⟩ := bind_wf_inv w
      have hΞ₁ := Wf_t.concatenate hΞ w₁
      have hty₁ := TelGood.entry h Θ hob hΘ hAβ hΞ w₁
      have hob₁ : ObGood P_Ob (Ξ ⋈ dTel.cons Θ β .nil) := fun _ => h.extend (hob hΞ) hty₁
      have hAε : AtomGood P_Ty P_Tm (Ξ ⋈ dTel.cons Θ β .nil ⋈ Ψ) ε := by
        rw [dTel.concatenate_assoc]
        apply hA
      have hty₂ := TelGood.entry h Ψ hob₁ hΨ hAε hΞ₁ w₂
      let e : Ob.Entry (toOb ⟨Δ, Ξ, hΞ⟩) := ⟨_, Θ, β, w₁⟩
      let f : Ob.Entry (extend ⟨Δ, Ξ, hΞ⟩ e.toTele) := ⟨_, Ψ, ε, w₂⟩
      have hcongr : AtomTermGood P_Tm (Ξ ⋈ dTel.cons Θ β .nil ⋈ Ψ) ε
            ((Subst.single t) (C.inl (C.singleSlot _)))
          ↔ AtomTermGood P_Tm (Ξ ⋈ dTel.cons Θ β Ψ) ε t := by
        rw [Subst.single_head]
        erw [dTel.concatenate_assoc]
        rfl
      apply Iff.trans _ hcongr
      apply Iff.trans _ (TelGood.unlam Ψ _ hob₁ hΨ hAε hΞ₁ w₂
        (unlamFill ⟨Δ, Ξ, hΞ⟩ e f ⟨Subst.single t, τw⟩).2)
      constructor
      · intro hP
        apply h.unlam (a := Quotient.mk _ e) (c := Quotient.mk _ f) (hob hΞ) hty₁ hty₂ hP
      · intro hP
        have hT := model.lam_unlam (Γ := toOb ⟨Δ, Ξ, hΞ⟩) (a := Quotient.mk _ e)
          (c := Quotient.mk _ f)
          (Tm₁.ofFill (e := (⟨_, dTel.cons Θ β Ψ, ε, w⟩ : Ob.Entry (toOb ⟨Δ, Ξ, hΞ⟩)))
            ⟨Subst.single t, τw⟩)
        erw [← hT]
        apply h.lam (a := Quotient.mk _ e) (c := Quotient.mk _ f) (hob hΞ) hty₁ hty₂ hP

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

/-- The lift of a substitution satisfying `P_Sub` between contexts satisfying `P_Ob` past a
telescope satisfying `TelGood` satisfies `P_Sub`. -/
theorem TelGood.lift :
  ∀ {Δ Δ' γ : C.Arity} {Ξ : Ambient Δ} {Ξ' : Ambient Δ'} (Θ : dTel Δ γ),
    ObGood P_Ob Ξ → ObGood P_Ob Ξ' → TelGood P_Ty P_Tm Ξ Θ →
    ∀ (hΞ : Ambient.Wf Ξ) (hΞ' : Ambient.Wf Ξ') (wΘ : Wf_t Ξ Θ)
      (σ : Ob.Subst (toOb ⟨Δ', Ξ', hΞ'⟩) (toOb ⟨Δ, Ξ, hΞ⟩)),
      P_Sub (Quotient.mk _ σ) → P_Sub (lift σ ⟨γ, Θ, wΘ⟩)
  | _, _, _, Ξ, Ξ', .nil, _, _, _, _, _, _, σ, hσ => by
      apply sub_of_heq (toOb_congr (Eq.symm (dTel.concatenate_nil Ξ)))
        (toOb_congr (Eq.symm (dTel.concatenate_nil Ξ'))) _ hσ
      apply Ob.Subst.heq_mk (toOb_congr (Eq.symm (dTel.concatenate_nil Ξ')))
        (toOb_congr (Eq.symm (dTel.concatenate_nil Ξ)))
      apply heq_of_eq
      symm
      apply Subst.lift_one
  | Δ, Δ', _, Ξ, Ξ', .cons (α := α) (Δ := Ω) Θ β Ψ, hob, hob', hΘ, hΞ, hΞ', wΘ, σ, hσ => by
      obtain ⟨hΘ, hA, hΨ⟩ := hΘ
      obtain ⟨wΘ, wβ, wΨ⟩ := Wf_t.cons_inv wΘ
      have w := Wf_t.cons wΘ wβ Wf_t.nil
      have hty := TelGood.entry h Θ hob hΘ hA hΞ w
      have hob₁ : ObGood P_Ob (Ξ ⋈ dTel.cons Θ β .nil) := fun _ => h.extend (hob hΞ) hty
      have hob₁' : ObGood P_Ob (Ξ' ⋈ dTel.actBase σ.1 (dTel.cons Θ β .nil)) :=
        fun _ => h.extend (hob' hΞ') (h.substTy (hob hΞ) (hob' hΞ') hty hσ)
      have key := TelGood.lift Ψ hob₁ hob₁' hΨ (Wf_t.concatenate hΞ w)
        (Wf_t.concatenate hΞ' (Wf_t.subst_ambient σ.2.toWf_sub w)) wΨ
        ⟨Subst.lift σ.1 _, (Wf_sub.lift σ.2.toWf_sub w).toFilling⟩
        (lift_entry h (Γ := ⟨Δ, Ξ, hΞ⟩) (Ξ := ⟨Δ', Ξ', hΞ'⟩) ⟨_, Θ, β, w⟩ σ (hob hΞ)
          (hob' hΞ') hty hσ)
      apply sub_of_heq (toOb_congr (dTel.concatenate_assoc _ _ _))
        (toOb_congr (dTel.concatenate_assoc _ _ _)) _ key
      apply Ob.Subst.heq_mk (toOb_congr (dTel.concatenate_assoc _ _ _))
        (toOb_congr (dTel.concatenate_assoc _ _ _))
      apply heq_of_eq
      symm
      exact Subst.lift_assoc σ.1 (C.single α) Ω

/-- For `Θ` satisfying `TelGood` over `Ξ` and `β` satisfying `AtomGood` over `Ξ ⋈ Θ`, the
declaration `β` reindexed along a substitution satisfying `P_Sub` satisfies `AtomGood` over
`Ξ'` followed by `Θ` reindexed. -/
theorem AtomGood.subst {Δ Δ' γ : C.Arity} {Ξ : Ambient Δ} {Ξ' : Ambient Δ'} {Θ : dTel Δ γ}
    {β : Bd (Δ ⋈ γ)} (hob : ObGood P_Ob Ξ) (hob' : ObGood P_Ob Ξ')
    (hΘ : TelGood P_Ty P_Tm Ξ Θ) (hA : AtomGood P_Ty P_Tm (Ξ ⋈ Θ) β)
    (hΞ : Ambient.Wf Ξ) (hΞ' : Ambient.Wf Ξ') (w : Wf_t Ξ (dTel.cons Θ β .nil))
    (σ : Ob.Subst (toOb ⟨Δ', Ξ', hΞ'⟩) (toOb ⟨Δ, Ξ, hΞ⟩)) (hσ : P_Sub (Quotient.mk _ σ))
    (hobΘ' : ObGood P_Ob (Ξ' ⋈ dTel.actBase σ.1 Θ)) :
  AtomGood P_Ty P_Tm (Ξ' ⋈ dTel.actBase σ.1 Θ) (Bd.act (Γ := 1) σ.1 γ β)
  := by
  obtain ⟨wΘ, -, -⟩ := Wf_t.cons_inv w
  have hlift := TelGood.lift h Θ hob hob' hΘ hΞ hΞ' wΘ σ hσ
  have hobΘ := TelGood.ob h Θ hob hΘ (Wf_t.concatenate hΞ wΘ)
  constructor
  · intro hΞ₁ w₁
    apply ty_of_heq rfl _
      (h.substTy hobΘ (hobΘ' hΞ₁) (hA.1 (Wf_t.concatenate hΞ wΘ) (Wf_t.atom w)) hlift)
    apply heq_of_eq
    apply congrArg (Quotient.mk _)
    apply Ob.Entry.congr_declaration
    apply Bd.act_lift_depth
  · intro S hS hΞ₁ τw
    obtain ⟨S₀, rfl, rfl⟩ := Bd.act_of_inv _ _ hS
    have hsort := hA.2 S₀ rfl (Wf_t.concatenate hΞ wΘ) (Wf_t.sort_fill (Wf_t.atom w))
    apply Tm₁.of_val _ (h.substTm hobΘ (hobΘ' hΞ₁) (h.U hobΘ) hsort hlift)
    apply congrArg (Quotient.mk _)
    apply Ob.Term.ext rfl
    apply Eq.trans (Subst.applyEach_single (α := 1) (Subst.lift σ.1 γ) S₀)
    rw [Subst.act_lift_depth]
    rfl

/-- Reindexing a telescope satisfying `TelGood` along a substitution satisfying `P_Sub`
between contexts satisfying `P_Ob` gives a telescope satisfying `TelGood`. -/
theorem TelGood.subst :
  ∀ {Δ Δ' Ω : C.Arity} {Ξ : Ambient Δ} {Ξ' : Ambient Δ'} (Θ : dTel Δ Ω),
    ObGood P_Ob Ξ → ObGood P_Ob Ξ' → TelGood P_Ty P_Tm Ξ Θ →
    ∀ (hΞ : Ambient.Wf Ξ) (hΞ' : Ambient.Wf Ξ'), Wf_t Ξ Θ →
      ∀ σ : Ob.Subst (toOb ⟨Δ', Ξ', hΞ'⟩) (toOb ⟨Δ, Ξ, hΞ⟩),
        P_Sub (Quotient.mk _ σ) → TelGood P_Ty P_Tm Ξ' (dTel.actBase σ.1 Θ)
  | _, _, _, _, _, .nil, _, _, _, _, _, _, _, _ => trivial
  | Δ, Δ', _, Ξ, Ξ', .cons Θ β Ψ, hob, hob', hΘ, hΞ, hΞ', wΘ, σ, hσ => by
      obtain ⟨hΘ, hA, hΨ⟩ := hΘ
      obtain ⟨wΘ, wβ, wΨ⟩ := Wf_t.cons_inv wΘ
      have w := Wf_t.cons wΘ wβ Wf_t.nil
      have hΘ' := TelGood.subst Θ hob hob' hΘ hΞ hΞ' wΘ σ hσ
      have hty := TelGood.entry h Θ hob hΘ hA hΞ w
      have hob₁ : ObGood P_Ob (Ξ ⋈ dTel.cons Θ β .nil) := fun _ => h.extend (hob hΞ) hty
      have hob₁' : ObGood P_Ob (Ξ' ⋈ dTel.actBase σ.1 (dTel.cons Θ β .nil)) :=
        fun _ => h.extend (hob' hΞ') (h.substTy (hob hΞ) (hob' hΞ') hty hσ)
      apply And.intro hΘ'
      apply And.intro (AtomGood.subst h hob hob' hΘ hA hΞ hΞ' w σ hσ (TelGood.ob h _ hob' hΘ'))
      apply TelGood.subst Ψ hob₁ hob₁' hΨ (Wf_t.concatenate hΞ w)
        (Wf_t.concatenate hΞ' (Wf_t.subst_ambient σ.2.toWf_sub w)) wΨ
        ⟨Subst.lift σ.1 _, (Wf_sub.lift σ.2.toWf_sub w).toFilling⟩
      apply lift_entry h (Γ := ⟨Δ, Ξ, hΞ⟩) (Ξ := ⟨Δ', Ξ', hΞ'⟩) ⟨_, Θ, β, w⟩ σ (hob hΞ)
        (hob' hΞ') hty hσ

/-- Extending a context satisfying `CtxGood` by an entry whose binding satisfies `TelGood` and
whose declaration satisfies `AtomGood` gives a context satisfying `CtxGood`. -/
theorem CtxGood.extend {Δ γ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ γ} {β : Bd (Δ ⋈ γ)}
    (hΞg : CtxGood P_Ob P_Ty P_Tm Ξ) (hΘ : TelGood P_Ty P_Tm Ξ Θ)
    (hA : AtomGood P_Ty P_Tm (Ξ ⋈ Θ) β) (hΞ : Ambient.Wf Ξ) (w : Wf_t Ξ (dTel.cons Θ β .nil)) :
  CtxGood P_Ob P_Ty P_Tm (Ξ ⋈ dTel.cons Θ β .nil)
  := by
  obtain ⟨hob, hslot⟩ := hΞg
  have hty := TelGood.entry h Θ hob hΘ hA hΞ w
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
    have hΘy' := TelGood.subst h _ hob hob₁ hΘy hΞ hΞ₁ (Wf_t.binding hΞ y) θ hθ
    have hAy' := AtomGood.subst h hob hob₁ hΘy hAy hΞ hΞ₁ wy θ hθ (TelGood.ob h _ hob₁ hΘy')
    erw [dTel.actBase_ofRenaming] at hΘy' hAy'
    erw [Bd.act_ofRenaming] at hAy'
    apply And.intro
    · erw [dTel.binding_concatenate_inl]
      apply hΘy'
    apply And.intro
    · erw [dTel.binding_concatenate_inl, dTel.declaration_concatenate_inl]
      apply hAy'
    erw [dTel.binding_concatenate_inl, dTel.declaration_concatenate_inl]
    intro hne hΞ₁' w' τw'
    have hne' : ¬ (Ξ.declaration y).isEq := fun he => hne ((Bd.isEq_rename _ _).mpr he)
    have hvar := hVy hne' hΞ wy ⟨wy, Wf_s.eta_single hΞ y hne'⟩
    apply Tm₁.of_val _
      (h.substTm (hob hΞ) (hob₁ hΞ₁) (TelGood.entry h _ hob hΘy hAy hΞ wy) hvar hθ)
    apply congrArg (Quotient.mk _)
    apply Ob.Term.ext
    · exact dTel.actBase_ofRenaming _ _
    · apply Eq.trans (Subst.applyEach_single _ _)
      apply congrArg Subst.single
      apply Eq.trans (act_ofRenaming (Renaming.inl Δ (C.single γ ⋈ 1)) (Expr.η y))
      apply Renaming.act_eta
  · induction z using slotCases with
    | head =>
      have hΘ' := TelGood.subst h Θ hob hob₁ hΘ hΞ hΞ₁ (Wf_t.cons_inv w).1 θ hθ
      have hA' := AtomGood.subst h hob hob₁ hΘ hA hΞ hΞ₁ w θ hθ (TelGood.ob h _ hob₁ hΘ')
      erw [dTel.actBase_ofRenaming] at hΘ' hA'
      erw [Bd.act_ofRenaming] at hA'
      apply And.intro
      · erw [dTel.binding_concatenate_inr, dTel.binding_head]
        apply hΘ'
      apply And.intro
      · erw [dTel.binding_concatenate_inr, dTel.declaration_concatenate_inr, dTel.binding_head,
          dTel.declaration_head]
        apply hA'
      erw [dTel.binding_concatenate_inr, dTel.declaration_concatenate_inr, dTel.binding_head,
        dTel.declaration_head]
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
  | Δ, Λ, Ξ, Θ, _, .of (S := S) hS hsort, hΞ, hΞg => by
      have wS := Wf_t.cons Wf_t.nil (Wf_e.boundary hΞ hS) Wf_t.nil
      have hSP := (Wf_e.good hS hΞ hΞg).1 hΞ wS ⟨wS, Wf_e.fill hS (boundaryOf_refl hΞ hS)⟩
      have hU : ∀ (hΞ' : Ambient.Wf (Ξ ⋈ Θ))
          (τw : Ob.Fill.Wf (toOb ⟨Δ ⋈ Λ, Ξ ⋈ Θ, hΞ'⟩) (dTel.cons .nil .sort .nil)
            (Subst.single (Δ := Δ ⋈ Λ) (α := 1) S)),
          P_Tm (Tm₁.ofFill (e := Ob.Entry.sort (toOb ⟨Δ ⋈ Λ, Ξ ⋈ Θ, hΞ'⟩))
            ⟨Subst.single S, τw⟩) := by
        intro hΞ' τw
        apply Tm₁.of_val _ hSP
        apply atom_val_eq hsort
      constructor
      · intro hΞ' w
        apply ty_of_heq rfl _ (h.El (hΞg.1 hΞ') (hU hΞ' (Wf_t.sort_fill w)))
        apply heq_of_eq
        apply congrArg (Quotient.mk _)
        apply Ob.Entry.congr_declaration
        exact congrArg Bd.of (Subst.single_head (Δ := Δ ⋈ Λ) (α := 1) S)
      · intro S' he hΞ' τw
        cases he
        apply hU hΞ' τw
  | Δ, Λ, Ξ, Θ, _, .eq (l := l) (r := r) hl hr heq, hΞ, hΞg => by
      have hlg := Wf_e.good hl hΞ hΞg
      have hbl := Wf_e.boundary hΞ hl
      have hne := Wf_e.boundary_not_isEq hl
      have wl := Wf_t.cons Wf_t.nil hbl Wf_t.nil
      have hlP := hlg.1 hΞ wl ⟨wl, Wf_e.fill hl (boundaryOf_refl hΞ hl)⟩
      have wr := Wf_t.cons Wf_t.nil (Wf_e.boundary hΞ hr) Wf_t.nil
      have hrP := (Wf_e.good hr hΞ hΞg).1 hΞ wr ⟨wr, Wf_e.fill hr (boundaryOf_refl hΞ hr)⟩
      constructor
      · intro hΞ' w
        rcases hb : (Ξ ⋈ Θ).boundaryOf l with _ | S | ⟨_, _⟩
        · rw [hb] at heq
          have hβl : Eq_bd (Ξ ⋈ Θ) ((Ξ ⋈ Θ).boundaryOf l) .sort := by
            rw [hb]
            apply Eq_bd.sort
          have hβr : Eq_bd (Ξ ⋈ Θ) ((Ξ ⋈ Θ).boundaryOf r) .sort := by
            rw [Eq_bd.sort_inv heq]
            apply Eq_bd.sort
          have hsort : Wf_t (Ξ ⋈ Θ) (dTel.cons .nil .sort .nil) :=
            Wf_t.cons Wf_t.nil Wf_bd.sort Wf_t.nil
          let τl : Ob.Fill (toOb ⟨Δ ⋈ Λ, Ξ ⋈ Θ, hΞ'⟩) (Ob.Entry.sort _).toTele :=
            ⟨Subst.single l, hsort, Wf_e.fill hl hβl⟩
          let τr : Ob.Fill (toOb ⟨Δ ⋈ Λ, Ξ ⋈ Θ, hΞ'⟩) (Ob.Entry.sort _).toTele :=
            ⟨Subst.single r, hsort, Wf_e.fill hr hβr⟩
          have htl : P_Tm (Tm₁.ofFill τl) := by
            apply Tm₁.of_val _ hlP
            apply atom_val_eq hβl
          have htr : P_Tm (Tm₁.ofFill τr) := by
            apply Tm₁.of_val _ hrP
            apply atom_val_eq hβr
          apply ty_of_heq rfl _ (h.IdSort (hΞg.1 hΞ') htl htr)
          apply heq_of_eq
          apply congrArg (Quotient.mk _)
          apply Ob.Entry.congr_declaration
          exact congrArg₂ Bd.eq (Subst.single_head (Δ := Δ ⋈ Λ) (α := 1) l)
            (Subst.single_head (Δ := Δ ⋈ Λ) (α := 1) r)
        · rw [hb] at heq hbl
          obtain ⟨S', hS', hSS'⟩ := Eq_bd.of_inv heq
          obtain ⟨hS, hsortS⟩ := Wf_bd.nil_of hbl
          let τS : Ob.Fill (toOb ⟨Δ ⋈ Λ, Ξ ⋈ Θ, hΞ'⟩) (Ob.Entry.sort _).toTele :=
            ⟨Subst.single S, Wf_t.cons Wf_t.nil Wf_bd.sort Wf_t.nil, Wf_e.fill hS hsortS⟩
          have hdecl : (Ob.Entry.of τS).declaration = .of S :=
            congrArg Bd.of (Subst.single_head (Δ := Δ ⋈ Λ) (α := 1) S)
          have hβl : Eq_bd (Ξ ⋈ Θ) ((Ξ ⋈ Θ).boundaryOf l) (Ob.Entry.of τS).declaration := by
            rw [hb, hdecl]
            apply Eq_bd.of (Eq_e.refl hS)
          have hβr : Eq_bd (Ξ ⋈ Θ) ((Ξ ⋈ Θ).boundaryOf r) (Ob.Entry.of τS).declaration := by
            rw [hS', hdecl]
            apply Eq_bd.of (Eq_e.symm hSS')
          let τl : Ob.Fill (toOb ⟨Δ ⋈ Λ, Ξ ⋈ Θ, hΞ'⟩) (Ob.Entry.of τS).toTele :=
            ⟨Subst.single l, (Ob.Entry.of τS).wf, Wf_e.fill hl hβl⟩
          let τr : Ob.Fill (toOb ⟨Δ ⋈ Λ, Ξ ⋈ Θ, hΞ'⟩) (Ob.Entry.of τS).toTele :=
            ⟨Subst.single r, (Ob.Entry.of τS).wf, Wf_e.fill hr hβr⟩
          have htl : P_Tm (Tm₁.ofFill τl) := by
            apply Tm₁.of_val _ hlP
            apply atom_val_eq hβl
          have htr : P_Tm (Tm₁.ofFill τr) := by
            apply Tm₁.of_val _ hrP
            apply atom_val_eq hβr
          apply ty_of_heq rfl _
            (h.IdElement (s := Tm₁.ofFill τS) (hΞg.1 hΞ') (hlg.2 S hb hΞ' τS.2) htl htr)
          apply heq_of_eq
          apply congrArg (Quotient.mk _)
          apply Ob.Entry.congr_declaration
          exact congrArg₂ Bd.eq (Subst.single_head (Δ := Δ ⋈ Λ) (α := 1) l)
            (Subst.single_head (Δ := Δ ⋈ Λ) (α := 1) r)
        · rw [hb] at hne
          exact absurd trivial hne
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
      have τx : Ob.Fill.Wf (toOb ⟨Δ, Ξ, hΞ⟩) (dTel.cons (Ξ.binding x) (Ξ.declaration x) .nil)
          (Subst.single (Expr.η x)) := ⟨wx, Wf_s.eta_single hΞ x head⟩
      have hatom := (TelGood.unlam h _ (Expr.η x) hob hΘx hAx hΞ wx τx).mp (hVx head hΞ wx τx)
      have wa := Wf_t.atom wx
      have hηfill : Wf_s (Ξ ⋈ Ξ.binding x) (dTel.cons .nil (Ξ.declaration x) .nil)
          (Subst.single (Δ := Δ ⋈ α) (α := 1) (Expr.η x : Expr (Δ ⋈ α))) := by
        apply Wf_e.fill (Wf_e.eta Ξ x wΘ head)
        rw [dTel.boundaryOf_eta]
        apply Wf_bd.refl (Wf_t.declaration hΞ x)
      have hslot := hatom hΞΘ wa ⟨wa, hηfill⟩
      have hsec := Wf_s.good fill hΞ hΞg hΘx wΘ (Wf_s.toSub hΞ fill).toFilling
      constructor
      · intro hΞ' w' τw'
        apply Tm₁.of_val _ (h.substTm hobΘ (hob hΞ) (hAx.1 hΞΘ wa) hslot hsec)
        apply congrArg (Quotient.mk _)
        apply Ob.Term.ext
        · exact congrArg (fun β => dTel.cons .nil β .nil)
            (Bd.act_copair_prefix args 1 (Ξ.declaration x))
        · apply Eq.trans (Subst.applyEach_single _ _)
          apply congrArg Subst.single
          apply act_copair_eta
      · intro S hS hΞ' τw'
        obtain ⟨S₀, hS₀, rfl⟩ := Bd.act_of_inv (Γ := Δ) (Ξ := 1) args 1
          (β := Ξ.declaration x) hS
        have wS₀ : Wf_t (Ξ ⋈ Ξ.binding x) (dTel.cons .nil (.of S₀) .nil) := by
          rw [← hS₀]
          apply wa
        have hsort := hAx.2 S₀ hS₀ hΞΘ (Wf_t.sort_fill wS₀)
        apply Tm₁.of_val _ (h.substTm hobΘ (hob hΞ) (h.U hobΘ) hsort hsec)
        apply congrArg (Quotient.mk _)
        apply Ob.Term.ext rfl
        apply Eq.trans (Subst.applyEach_single (α := 1) _ S₀)
        apply congrArg Subst.single
        apply act_copair_prefix

/-- Over a well-formed ambient satisfying `CtxGood`, the section of a filling of a telescope
satisfying `TelGood` satisfies `P_Sub`. -/
theorem Wf_s.good :
  ∀ {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω} {σ : Subst Ω Δ}, Wf_s Ξ Θ σ →
    ∀ (hΞ : Ambient.Wf Ξ), CtxGood P_Ob P_Ty P_Tm Ξ → TelGood P_Ty P_Tm Ξ Θ →
    ∀ (wΘ : Wf_t Ξ Θ)
      (hs : Ob.Subst.Wf (toOb ⟨Δ, Ξ, hΞ⟩) (toOb ⟨_, Ξ ⋈ Θ, Wf_t.concatenate hΞ wΘ⟩)
        (Subst.copair (Subst.id Δ) σ)),
      P_Sub (Quotient.mk _ (⟨Subst.copair (Subst.id Δ) σ, hs⟩ :
        Ob.Subst (toOb ⟨Δ, Ξ, hΞ⟩) (toOb ⟨_, Ξ ⋈ Θ, Wf_t.concatenate hΞ wΘ⟩)))
  | Δ, _, Ξ, _, σ, .nil, hΞ, hΞg, _, _, _ => by
      apply sub_of_heq (toOb_congr (Eq.symm (dTel.concatenate_nil Ξ))) rfl _
        (h.identity (hΞg.1 hΞ))
      apply Ob.Subst.heq_mk rfl (toOb_congr (Eq.symm (dTel.concatenate_nil Ξ)))
      apply heq_of_eq
      funext α x
      rcases C.cover Δ 1 x with ⟨y, rfl⟩ | ⟨z, rfl⟩
      · symm
        apply Eq.trans (Subst.copair_inl _ _ y)
        exact congrArg Expr.η (Eq.symm (C.unit_right Δ y))
      · exact (C.unit_is_empty z).elim
  | Δ, _, Ξ, .cons (α := α) Θ β Ψ, σ, hσ@(.cons _ filler declared hrest), hΞ, hΞg,
      hΘ, wΘ, _ => by
      obtain ⟨hΘ, hA, hΨ⟩ := hΘ
      obtain ⟨wΘ, wβ, wΨ⟩ := Wf_t.cons_inv wΘ
      have w := Wf_t.cons wΘ wβ Wf_t.nil
      have hΞΘ := Wf_t.concatenate hΞ wΘ
      have hΞ₁ := Wf_t.concatenate hΞ w
      have hob := hΞg.1
      have hty := TelGood.entry h Θ hob hΘ hA hΞ w
      have hobΘ := TelGood.ob h Θ hob hΘ
      have hob₁ : ObGood P_Ob (Ξ ⋈ dTel.cons Θ β .nil) := fun _ => h.extend (hob hΞ) hty
      have hatom : AtomTermGood P_Tm (Ξ ⋈ Θ) β (σ (C.inl (C.singleSlot α))) := by
        intro hΞ' w' τw'
        by_cases hne : β.isEq
        · obtain ⟨l, r, rfl⟩ := Bd.eq_of_isEq hne
          apply eq_term h w' (hobΘ hΞ') rfl (hA.1 hΞ' w')
        · have hfill := Wf_e.fill (filler hne) (boundaryOf_refl hΞΘ (filler hne))
          have w₀ := Wf_t.cons Wf_t.nil (Wf_e.boundary hΞΘ (filler hne)) Wf_t.nil
          apply Tm₁.of_val _
            ((Wf_e.good (filler hne) hΞΘ (CtxGood.append h Θ hΞg hΘ hΞ wΘ)).1 hΞΘ w₀
              ⟨w₀, hfill⟩)
          apply atom_val_eq (declared hne)
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
        apply Tm₁.of_val _ ((TelGood.unlam h Θ _ hob hΘ hA hΞ w τw).mpr hatom)
        apply congrArg (Quotient.mk _)
        apply Ob.Term.ext
        · exact congrArg₂ (fun Θ' β' => dTel.cons Θ' β' .nil) (Eq.symm (dTel.actBase_id Θ))
            (Eq.symm (Bd.act_id Δ α β))
        · apply Subst.single_restrict
      have wθ := Ob.Subst.Wf.pair (Γ := ⟨Δ, Ξ, hΞ⟩) (Θ := u.toTele) (Ob.Subst.id _) _ τ₀w
      let θ : Ob.Subst (toOb ⟨Δ, Ξ, hΞ⟩) (toOb ⟨_, Ξ ⋈ dTel.cons Θ β .nil, hΞ₁⟩) :=
        ⟨Subst.copair (Subst.id Δ) (fun ⦃γ⦄ (i : C.single α ∋ γ) => σ (C.inl i)), wθ⟩
      have hθ : P_Sub (Quotient.mk _ θ) :=
        h.pair (a := Quotient.mk _ u) (hob hΞ) (hob hΞ) hty (h.identity (hob hΞ)) ht₀
      have hΨ' := TelGood.subst h Ψ hob₁ hob hΨ hΞ₁ hΞ wΨ θ hθ
      have wΨ' := Wf_t.subst_ambient θ.2.toWf_sub wΨ
      have hcomp := h.comp (TelGood.ob h Ψ hob₁ hΨ (Wf_t.concatenate hΞ₁ wΨ))
        (TelGood.ob h _ hob hΨ' (Wf_t.concatenate hΞ wΨ')) (hob hΞ)
        (TelGood.lift h Ψ hob₁ hob hΨ hΞ₁ hΞ wΨ θ hθ)
        (Wf_s.good hrest hΞ hΞg hΨ' wΨ' (Wf_s.toSub hΞ hrest).toFilling)
      apply sub_of_heq (toOb_congr (dTel.concatenate_assoc _ _ _)) rfl _ hcomp
      apply Ob.Subst.heq_mk rfl (toOb_congr (dTel.concatenate_assoc _ _ _))
      apply heq_of_eq
      exact Subst.copair_split σ

end

/-- Every well-formed ambient satisfies `CtxGood`. -/
theorem CtxGood.of_wf {Δ : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ) :
  CtxGood P_Ob P_Ty P_Tm Ξ
  := by
  have hnil : CtxGood P_Ob P_Ty P_Tm (.nil : Ambient 1) :=
    ⟨fun _ => h.empty, fun _ x => (C.unit_is_empty x).elim⟩
  apply CtxGood.append h Ξ hnil (Wf_t.good h hΞ Wf_t.nil hnil) Wf_t.nil hΞ

/-- Over a well-formed ambient satisfying `CtxGood`, the term given by a filling of the entry
binding `Θ` and declaring `β`, where `Θ` satisfies `TelGood` and `β` satisfies `AtomGood` over
`Ξ ⋈ Θ`, satisfies `P_Tm`. -/
theorem ofFill_good {Δ γ : C.Arity} {Ξ : Ambient Δ} (hΞ : Ambient.Wf Ξ)
    (hΞg : CtxGood P_Ob P_Ty P_Tm Ξ) {Θ : dTel Δ γ} {β : Bd (Δ ⋈ γ)}
    (hΘ : TelGood P_Ty P_Tm Ξ Θ) (hA : AtomGood P_Ty P_Tm (Ξ ⋈ Θ) β)
    (w : Wf_t Ξ (dTel.cons Θ β .nil))
    (τ : Ob.Fill (toOb ⟨Δ, Ξ, hΞ⟩) (⟨γ, Θ, β, w⟩ : Ob.Entry (toOb ⟨Δ, Ξ, hΞ⟩)).toTele) :
  P_Tm (Tm₁.ofFill τ)
  := by
  obtain ⟨τ, wτ, hτ⟩ := τ
  obtain ⟨wΘ, -, -⟩ := Wf_t.cons_inv w
  have hΞΘ := Wf_t.concatenate hΞ wΘ
  have hτs : Wf_s Ξ (dTel.cons Θ β .nil) (Subst.single (τ (C.inl (C.singleSlot γ)))) := by
    rw [Subst.single_eta]
    apply hτ
  have hatom : AtomTermGood P_Tm (Ξ ⋈ Θ) β (τ (C.inl (C.singleSlot γ))) := by
    intro hΞ' w' τw'
    by_cases hne : β.isEq
    · obtain ⟨l, r, rfl⟩ := Bd.eq_of_isEq hne
      apply eq_term h w' (TelGood.ob h Θ hΞg.1 hΘ hΞ') rfl (hA.1 hΞ' w')
    · obtain ⟨-, hfill, hdecl⟩ := (Wf_s.single_iff _).mp hτs
      have w₀ := Wf_t.cons Wf_t.nil (Wf_e.boundary hΞΘ (hfill hne)) Wf_t.nil
      have hfill₀ := Wf_e.fill (hfill hne) (boundaryOf_refl hΞΘ (hfill hne))
      apply Tm₁.of_val _
        ((Wf_e.good h (hfill hne) hΞΘ (CtxGood.append h Θ hΞg hΘ hΞ wΘ)).1 hΞΘ w₀
          ⟨w₀, hfill₀⟩)
      apply atom_val_eq (hdecl hne)
  apply Tm₁.of_val _ ((TelGood.unlam h Θ _ hΞg.1 hΘ hA hΞ w ⟨wτ, hτs⟩).mpr hatom)
  apply congrArg (Quotient.mk _)
  apply Ob.Term.ext rfl
  apply Subst.single_eta

/-- A family of predicates on the objects, substitutions, types and terms of `Ctx.model`
closed under its operations holds of every object, substitution, type and term. -/
theorem generated :
  (∀ X, P_Ob X) ∧ (∀ {X Y : Ob} (f : Y ⟶ X), P_Sub f) ∧ (∀ {X : Ob} (a : Ty₁ X), P_Ty a) ∧
    ∀ {X : Ob} {a : Ty₁ X} (t : Tm₁ X a), P_Tm t
  := by
  have hnil : CtxGood P_Ob P_Ty P_Tm (.nil : Ambient 1) :=
    ⟨fun _ => h.empty, fun _ x => (C.unit_is_empty x).elim⟩
  constructor
  · intro X
    induction X using Ob.ind with
    | h Γ =>
    obtain ⟨Δ, Ξ, hΞ⟩ := Γ
    apply (CtxGood.of_wf h hΞ).1 hΞ
  constructor
  · intro X Y f
    revert f
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
    have hctx := CtxGood.of_wf h hΞ
    let κ : Ob.Subst (toOb ⟨Δ, Ξ, hΞ⟩) (toOb ⟨1, .nil, Wf_t.nil⟩) :=
      ⟨fun ⦃_⦄ x => (C.unit_is_empty x).elim, Wf_s.nil⟩
    have hκ : P_Sub (Quotient.mk _ κ) := h.toEmpty (hctx.1 hΞ)
    have hΘ' := Wf_t.good h hΞ' Wf_t.nil hnil
    have hΘ := TelGood.subst h Ξ' hnil.1 hctx.1 hΘ' Wf_t.nil hΞ hΞ' κ hκ
    have eΘ : dTel.actBase κ.1 Ξ' = dTel.rename (Renaming.fromUnit Δ) Ξ' := by
      rw [← dTel.actBase_ofRenaming]
      congr 1
      funext α x
      exact (C.unit_is_empty x).elim
    have hσ' : Wf_s Ξ (dTel.actBase κ.1 Ξ') σ :=
      Eq.mpr (congrArg (fun Θ => Wf_s Ξ Θ σ) eΘ) hσ
    have wΘ : Wf_t Ξ (dTel.actBase κ.1 Ξ') :=
      Eq.mpr (congrArg (fun Θ => Wf_t Ξ Θ) eΘ) (Ambient.Wf.weaken hΞ' Ξ)
    have hcomp := h.comp ((CtxGood.of_wf h hΞ').1 hΞ')
      (TelGood.ob h _ hctx.1 hΘ (Wf_t.concatenate hΞ wΘ)) (hctx.1 hΞ)
      (TelGood.lift h Ξ' hnil.1 hctx.1 hΘ' Wf_t.nil hΞ hΞ' κ hκ)
      (Wf_s.good h hσ' hΞ hctx hΘ wΘ (Wf_s.toSub hΞ hσ').toFilling)
    apply sub_of_heq rfl rfl _ hcomp
    apply heq_of_eq
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    funext α x
    rcases C.cover 1 Δ' x with ⟨z, rfl⟩ | ⟨y, rfl⟩
    · exact (C.unit_is_empty z).elim
    · apply Eq.trans (congrArg (Subst.act (Γ := 1) (Subst.copair (Subst.id Δ) σ) α)
        (Subst.lift_inr κ.1 y))
      apply Eq.trans (act_η _ α (C.inr y))
      apply Eq.trans (Subst.copair_inr _ _ y)
      exact congrArg (fun z => σ z) (Eq.symm (C.unit_left Δ' y))
  constructor
  · intro X a
    revert a
    induction X using Ob.ind with
    | h Γ =>
    intro a
    induction a using Quotient.ind with
    | _ u =>
    obtain ⟨Δ, Ξ, hΞ⟩ := Γ
    obtain ⟨γ, Θ, β, w⟩ := u
    have hctx := CtxGood.of_wf h hΞ
    obtain ⟨hΘ, hA, -⟩ := Wf_t.good h w hΞ hctx
    apply TelGood.entry h Θ hctx.1 hΘ hA hΞ w
  · intro X a t
    revert a t
    induction X using Ob.ind with
    | h Γ =>
    intro a
    induction a using Quotient.ind with
    | _ u =>
    intro t
    induction t using Tm₁.ind with
    | ofFill τ =>
    obtain ⟨Δ, Ξ, hΞ⟩ := Γ
    obtain ⟨γ, Θ, β, w⟩ := u
    have hctx := CtxGood.of_wf h hΞ
    obtain ⟨hΘ, hA, -⟩ := Wf_t.good h w hΞ hctx
    apply ofFill_good h hΞ hctx hΘ hA w τ

end Closure

end Ctx
