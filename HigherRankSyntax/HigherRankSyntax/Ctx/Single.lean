import HigherRankSyntax.Ctx.Extension

/-!
# One-entry types

The types over a context class in `Ctx.model` are the classes of entries, an
entry being the telescope of entries its slot binds together with the boundary
the slot declares.  The terms of such a type are the classes of telescopes with a
filling lying over the one-entry telescope class it presents.  Extension by such
a type, with its projection, generic term, pairing and lifting, is extension by
that one-entry telescope class.
-/

open CategoryTheory

namespace Ctx

/-- An entry of a telescope over a context class: the telescope of entries its
slot binds and the boundary the slot declares, forming a well-formed one-entry
telescope. -/
structure Ob.Entry (X : Ob) : Type where
  /-- The binding arity of the slot: the arity of the entries it binds. -/
  arity : C.Arity
  /-- The telescope of entries the slot binds. -/
  binding : dTel X.arity arity
  /-- The boundary the slot declares. -/
  declaration : Bd (X.arity ⋈ arity)
  /-- The one-entry telescope with this binding and declaration is well formed
  over `X`. -/
  wf : Ob.Tele.Wf X (dTel.cons binding declaration .nil)

/-- The one-entry telescope an entry presents. -/
def Ob.Entry.toTele {X : Ob} (e : Ob.Entry X) : Ob.Tele X :=
  ⟨C.single e.arity ⋈ 1, dTel.cons e.binding e.declaration .nil, e.wf⟩

/-- Two entries over a context class are related when the one-entry telescopes
they present are equal. -/
def Ob.Entry.Rel {X : Ob} (e e' : Ob.Entry X) : Prop :=
  Ob.Tele.Rel e.toTele e'.toTele

/-- The setoid of entries over `X` under `Ob.Entry.Rel`. -/
def Ob.Entry.setoid (X : Ob) : Setoid (Ob.Entry X) where
  r := Ob.Entry.Rel
  iseqv := ⟨fun e => Ob.Tele.Rel.refl e.toTele, Ob.Tele.Rel.symm, Ob.Tele.Rel.trans⟩

/-- The classes of entries over a context class. -/
def Ty₁ (X : Ob) : Type := Quotient (Ob.Entry.setoid X)

/-- The telescope class an entry class presents. -/
def Ty₁.toTy {X : Ob} (a : Ty₁ X) : Ty.obj (Opposite.op X) :=
  Quotient.map Ob.Entry.toTele (fun _ _ h => h) a

/-- An entry class is determined by the telescope class it presents. -/
theorem Ty₁.toTy_injective {X : Ob} :
  Function.Injective (Ty₁.toTy (X := X))
  := by
  rintro ⟨e⟩ ⟨e'⟩ h
  apply Quotient.sound
  apply Quotient.exact h

/-- The classes of telescopes with a filling over `X` whose telescope class is
the one `a` presents. -/
def Tm₁ (X : Ob) (a : Ty₁ X) : Type :=
  { t : Tm.obj (Opposite.op X) // Ob.Term.tele t = a.toTy }

/-- An entry reindexed along a filling. -/
def Ob.Entry.subst {X Y : Ob} (σ : Ob.Subst X Y) (e : Ob.Entry Y) : Ob.Entry X where
  arity := e.arity
  binding := dTel.actBase σ.1 e.binding
  declaration := Bd.act (Γ := 1) σ.1 e.arity e.declaration
  wf := Ob.Tele.Wf.subst σ e.toTele

/-- Reindexing along related fillings sends related entries to related
entries. -/
theorem Ob.Entry.subst_congr
    {X Y : Ob} {σ σ' : Ob.Subst X Y} {e e' : Ob.Entry Y}
    (hσ : Ob.Subst.Rel X Y σ.1 σ'.1) (h : Ob.Entry.Rel e e') :
  Ob.Entry.Rel (Ob.Entry.subst σ e) (Ob.Entry.subst σ' e')
  := Ob.Tele.Rel.subst hσ h

/-- A type reindexed along a substitution. -/
def Ty₁.subst {X Y : Ob} (a : Ty₁ Y) (σ : X ⟶ Y) : Ty₁ X :=
  Quotient.map₂ Ob.Entry.subst
    (fun _ _ hσ _ _ h => Ob.Entry.subst_congr hσ h) σ a

/-- Reindexing an entry class reindexes the telescope class it presents. -/
theorem Ty₁.toTy_subst {X Y : Ob} (a : Ty₁ Y) (σ : X ⟶ Y) :
  (a.subst σ).toTy = Ty.map σ.op a.toTy
  := by
  obtain ⟨σ⟩ := σ
  obtain ⟨e⟩ := a
  rfl

/-- A term reindexed along a substitution. -/
def Tm₁.subst {X Y : Ob} {a : Ty₁ Y} (t : Tm₁ Y a) (σ : X ⟶ Y) : Tm₁ X (a.subst σ) :=
  ⟨Tm.map σ.op t.1, by rw [Ob.Term.tele_map, t.2, Ty₁.toTy_subst]⟩

theorem Ty₁.subst_id {X : Ob} (a : Ty₁ X) :
  a.subst (𝟙 X) = a
  := by
  apply toTy_injective
  rw [toTy_subst, op_id, Functor.map_id_apply]

theorem Ty₁.subst_comp {X Y Z : Ob} (a : Ty₁ Y) (σ : X ⟶ Y) (θ : Z ⟶ X) :
  a.subst (θ ≫ σ) = (a.subst σ).subst θ
  := by
  apply toTy_injective
  rw [toTy_subst, toTy_subst, toTy_subst, op_comp, Functor.map_comp_apply]

theorem Tm₁.subst_id {X : Ob} {a : Ty₁ X} (t : Tm₁ X a) :
  (t.subst (𝟙 X)).1 = t.1
  := by
  apply Functor.map_id_apply

theorem Tm₁.subst_comp
    {X Y Z : Ob} {a : Ty₁ Y} (t : Tm₁ Y a) (σ : X ⟶ Y) (θ : Z ⟶ X) :
  (t.subst (θ ≫ σ)).1 = ((t.subst σ).subst θ).1
  := by
  apply Functor.map_comp_apply

/-- Terms with the same underlying telescope with a filling are equal, across a
transport of their type. -/
theorem Tm₁.cast_eq
    {X : Ob} {a a' : Ty₁ X} (e : a = a') {t : Tm₁ X a} {t' : Tm₁ X a'}
    (h : t.1 = t'.1) :
  e ▸ t = t'
  := by
  subst e
  apply Subtype.ext h

/-- Terms with the same underlying telescope with a filling are heterogeneously
equal. -/
theorem Tm₁.heq_of_eq
    {X : Ob} {a a' : Ty₁ X} {t : Tm₁ X a} {t' : Tm₁ X a'} (h : t.1 = t'.1) :
  HEq t t'
  := by
  obtain rfl : a = a' := by
    apply Ty₁.toTy_injective
    rw [← t.2, ← t'.2, h]
  apply _root_.heq_of_eq (Subtype.ext h)

/-- The expression a filling of the one-entry telescope of `u` assigns to its
slot. -/
def Ob.Fill.filler {X : Ob} {u : Ob.Entry X} (τ : Ob.Fill X u.toTele) :
    Expr (X.arity ⋈ u.arity) :=
  τ.1 (C.inl (C.singleSlot u.arity))

/-- The term given by a filling of the telescope an entry presents. -/
def Tm₁.ofFill {X : Ob} {e : Ob.Entry X} (τ : Ob.Fill X e.toTele) :
    Tm₁ X (Quotient.mk (Ob.Entry.setoid X) e) :=
  ⟨Quotient.mk (Ob.Term.setoid X) ⟨e.toTele, τ⟩, rfl⟩

/-- The terms of the type an entry presents correspond to the classes of
fillings of its one-entry telescope. -/
def Tm₁.fillEquiv {X : Ob} (e : Ob.Entry X) :
    Tm₁ X (Quotient.mk (Ob.Entry.setoid X) e) ≃ Quotient (Ob.Fill.setoid e.toTele) :=
  (Equiv.subtypeQuotientEquivQuotientSubtype
      (fun s : Ob.Term X => Ob.Tele.Rel s.1 e.toTele)
      (s₂ := Ob.Term.fibreSetoid e.toTele)
      (fun t => Ob.Term.tele t = Quotient.mk (Ob.Tele.setoid X) e.toTele)
      (fun _ => ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩)
      (fun _ _ => Iff.rfl)).trans
    (Ob.Term.fibreEquiv e.toTele)

/-- Induction on a term of the type an entry presents, through the fillings of
its one-entry telescope. -/
theorem Tm₁.ind
    {X : Ob} {e : Ob.Entry X}
    {motive : Tm₁ X (Quotient.mk (Ob.Entry.setoid X) e) → Prop}
    (ofFill : ∀ τ : Ob.Fill X e.toTele, motive (Tm₁.ofFill τ))
    (t : Tm₁ X (Quotient.mk (Ob.Entry.setoid X) e)) :
  motive t
  := by
  obtain ⟨⟨s⟩, hs⟩ := t
  have hrel := Quotient.exact hs
  convert ofFill (Ob.Fill.ofRel hrel s.2) using 1
  apply Subtype.ext
  apply Quotient.sound
  apply Ob.Term.Rel.symm (Ob.Term.fibre_left ⟨s, hrel⟩)

/-- The generic term of a one-entry type, over the extension by that type. -/
def Tm₁.generic {X : Ob} (a : Ty₁ X) :
    Tm₁ (Ob.extend X a.toTy) (a.subst (Ob.projection X a.toTy)) :=
  ⟨Ob.generic X a.toTy, by rw [Ty₁.toTy_subst, Ob.generic_tele]⟩

theorem Ob.Entry.arity_cast {Z Z' : Ob} (h : Z = Z') (u : Ob.Entry Z) :
  (h ▸ u).arity = u.arity
  := by
  subst h
  rfl

theorem Ob.Entry.binding_cast {Z Z' : Ob} (h : Z = Z') (u : Ob.Entry Z) :
  HEq (h ▸ u).binding u.binding
  := by
  subst h
  rfl

theorem Ob.Entry.declaration_cast {Z Z' : Ob} (h : Z = Z') (u : Ob.Entry Z) :
  HEq (h ▸ u).declaration u.declaration
  := by
  subst h
  rfl

theorem Ty₁.mk_cast {Z Z' : Ob} (h : Z = Z') (u : Ob.Entry Z) :
  cast (congrArg Ty₁ h) (Quotient.mk (Ob.Entry.setoid Z) u)
    = Quotient.mk (Ob.Entry.setoid Z') (h ▸ u)
  := by
  subst h
  rfl

/-- Classes of entries over equal objects are heterogeneously equal when the
entries have the same binding arity and, along every identification of the
arities of the objects, equal one-entry telescopes. -/
theorem Ty₁.heq_mk
    {X X' : Ob} (h : X = X') {γ : C.Arity}
    {Θ : dTel X.arity γ} {β : Bd (X.arity ⋈ γ)}
    {w : Ob.Tele.Wf X (dTel.cons Θ β .nil)}
    {Θ' : dTel X'.arity γ} {β' : Bd (X'.arity ⋈ γ)}
    {w' : Ob.Tele.Wf X' (dTel.cons Θ' β' .nil)}
    (hrel : ∀ e : X.arity = X'.arity,
      Ob.Tele.Eq X' (e ▸ dTel.cons Θ β .nil) (dTel.cons Θ' β' .nil)) :
  HEq (Quotient.mk (Ob.Entry.setoid X) ⟨γ, Θ, β, w⟩)
    (Quotient.mk (Ob.Entry.setoid X') ⟨γ, Θ', β', w'⟩)
  := by
  subst h
  apply heq_of_eq
  apply Quotient.sound
  exact ⟨rfl, hrel rfl⟩

/-- Heterogeneously equal classes of entries over equal objects have entries with
the same binding arity and, along every identification of the arities of the
objects, equal one-entry telescopes. -/
theorem Ty₁.eq_of_heq_mk
    {X X' : Ob} (h : X = X') {γ γ' : C.Arity}
    {Θ : dTel X.arity γ} {β : Bd (X.arity ⋈ γ)}
    {w : Ob.Tele.Wf X (dTel.cons Θ β .nil)}
    {Θ' : dTel X'.arity γ'} {β' : Bd (X'.arity ⋈ γ')}
    {w' : Ob.Tele.Wf X' (dTel.cons Θ' β' .nil)}
    (hu : HEq (Quotient.mk (Ob.Entry.setoid X) ⟨γ, Θ, β, w⟩)
      (Quotient.mk (Ob.Entry.setoid X') ⟨γ', Θ', β', w'⟩)) :
  ∃ hγ : γ = γ', ∀ e : X.arity = X'.arity,
    Ob.Tele.Eq X' (e ▸ hγ ▸ dTel.cons Θ β .nil) (dTel.cons Θ' β' .nil)
  := by
  subst h
  obtain ⟨hs, hrel⟩ := Quotient.exact (eq_of_heq hu)
  obtain rfl := C.single_injective hs
  exact ⟨rfl, fun _ => hrel⟩

theorem Ty₁.extend_heq
    {X X' : Ob} (h : X = X') {a : Ty₁ X} {a' : Ty₁ X'} (ha : HEq a a') :
  Ob.extend X a.toTy = Ob.extend X' a'.toTy
  := by
  subst h
  obtain rfl := eq_of_heq ha
  rfl

/-- Equivalences between equal types that send heterogeneously equal arguments
to heterogeneously equal values are heterogeneously equal. -/
theorem Equiv.heq_congr
    {α α' β β' : Type} (hα : α = α') (hβ : β = β')
    {u : α ≃ β} {u' : α' ≃ β'}
    (h : ∀ (x : α) (x' : α'), HEq x x' → HEq (u x) (u' x')) :
  HEq u u'
  := by
  subst hα hβ
  apply heq_of_eq
  ext x
  apply eq_of_heq (h x x HEq.rfl)

theorem Tm₁.eq_of_heq
    {X : Ob} {b b' : Ty₁ X} (hb : b = b')
    {t : Tm₁ X b} {t' : Tm₁ X b'} (h : HEq t t') :
  t.1 = t'.1
  := by
  subst hb
  rw [_root_.eq_of_heq h]

theorem Tm₁.heq_of_heq_val
    {X X' : Ob} (hX : X = X') {b : Ty₁ X} {b' : Ty₁ X'}
    {t : Tm₁ X b} {t' : Tm₁ X' b'} (h : HEq t.1 t'.1) :
  HEq t t'
  := by
  subst hX
  apply Tm₁.heq_of_eq (_root_.eq_of_heq h)

theorem Tm₁.heq_val
    {Z Z' : Ob} (h : Z = Z') {c : Ty₁ Z} {c' : Ty₁ Z'} (hc : HEq c c')
    {x : Tm₁ Z c} {x' : Tm₁ Z' c'} (hx : HEq x x') :
  HEq x.1 x'.1
  := by
  subst h
  obtain rfl := _root_.eq_of_heq hc
  obtain rfl := _root_.eq_of_heq hx
  rfl

theorem Tm₁.type_congr
    {Z Z' : Ob} (h : Z = Z') {c : Ty₁ Z} {c' : Ty₁ Z'} (hc : HEq c c') :
  Tm₁ Z c = Tm₁ Z' c'
  := by
  subst h
  obtain rfl := _root_.eq_of_heq hc
  rfl

/-- A substitution extended past a one-entry type. -/
def Ty₁.lift {X Y : Ob} (a : Ty₁ X) (σ : Y ⟶ X) :
    Ob.extend Y (a.subst σ).toTy ⟶ Ob.extend X a.toTy :=
  (Ty₁.toTy_subst a σ).symm ▸ Ob.lift a.toTy σ

/-- On the classes of a substitution and an entry, `Ty₁.lift` is `Ctx.lift`
along the one-entry telescope the entry presents. -/
theorem Ty₁.lift_mk {Ξ Γ : Ctx} (e : Ob.Entry Γ.toOb) (σ : Ob.Subst Ξ.toOb Γ.toOb) :
  Ty₁.lift (Quotient.mk (Ob.Entry.setoid Γ.toOb) e)
      (Quotient.mk (Ob.Subst.setoid Ξ.toOb Γ.toOb) σ)
    = Ctx.lift σ e.toTele
  := Ob.lift_mk σ e.toTele

/-- `a.lift σ` followed by the projection is the projection followed by `σ`. -/
theorem Ty₁.projection_lift {X Y : Ob} (a : Ty₁ X) (σ : Y ⟶ X) :
  a.lift σ ≫ Ob.projection X a.toTy = Ob.projection Y (a.subst σ).toTy ≫ σ
  := by
  obtain ⟨e⟩ := a
  obtain ⟨σ⟩ := σ
  apply Ob.pair_projection

/-- The generic term reindexed along `a.lift σ` is the generic term of
`a.subst σ`. -/
theorem Ty₁.generic_lift {X Y : Ob} (a : Ty₁ X) (σ : Y ⟶ X) :
  HEq ((Tm₁.generic a).subst (a.lift σ)) (Tm₁.generic (a.subst σ))
  := by
  apply Tm₁.heq_of_eq
  obtain ⟨e⟩ := a
  obtain ⟨σ⟩ := σ
  apply Ob.pair_generic

/-- A substitution paired with a term of the reindexed one-entry type, as a
substitution into the extension by that type. -/
def Ty₁.pair {X Y : Ob} {a : Ty₁ Y} (σ : X ⟶ Y) (t : Tm₁ X (a.subst σ)) :
    X ⟶ Ob.extend Y a.toTy :=
  Ob.pair σ t.1 (by rw [t.2, Ty₁.toTy_subst])

/-- `Ty₁.pair σ t` followed by the projection is `σ`. -/
theorem Ty₁.projection_pair {X Y : Ob} {a : Ty₁ Y} (σ : X ⟶ Y) (t : Tm₁ X (a.subst σ)) :
  Ty₁.pair σ t ≫ Ob.projection Y a.toTy = σ
  := Ob.pair_projection σ t.1 _

/-- The generic term reindexed along `Ty₁.pair σ t` is `t`. -/
theorem Ty₁.generic_pair {X Y : Ob} {a : Ty₁ Y} (σ : X ⟶ Y) (t : Tm₁ X (a.subst σ)) :
  HEq ((Tm₁.generic a).subst (Ty₁.pair σ t)) t
  := Tm₁.heq_of_eq (Ob.pair_generic σ t.1 _)

/-- The projection paired with the generic term is the identity. -/
theorem Ty₁.pair_eta {X : Ob} (a : Ty₁ X) :
  Ty₁.pair (Ob.projection X a.toTy) (Tm₁.generic a) = 𝟙 (Ob.extend X a.toTy)
  := Ob.pair_eta X a.toTy

end Ctx
