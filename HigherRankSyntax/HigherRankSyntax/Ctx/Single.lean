import HigherRankSyntax.Ctx.Extension

/-!
# One-entry types

The types of the HrS structure on `Ctx`: the classes of entries, an entry being
a telescope its slot binds together with the boundary it declares.  The terms of
such a type are the telescopes with a filling lying over the telescope the entry
presents.
-/

open CategoryTheory

namespace Ctx

/-- An entry over a context class. -/
structure Ob.Entry (X : Ob) : Type where
  /-- The entries the slot binds. -/
  arity : C.Arity
  /-- The declarations of the entries the slot binds. -/
  binding : dTel X.arity arity
  /-- The boundary the slot declares. -/
  declaration : Bd (X.arity ⋈ arity)
  /-- The one-entry telescope is well formed. -/
  wf : Ob.Tele.Wf X (dTel.cons binding declaration .nil)

/-- The one-entry telescope an entry presents. -/
def Ob.Entry.toTele {X : Ob} (e : Ob.Entry X) : Ob.Tele X :=
  ⟨C.single e.arity ⋈ 1, dTel.cons e.binding e.declaration .nil, e.wf⟩

/-- 7.4 on the entries over a context class. -/
def Ob.Entry.Rel {X : Ob} (e e' : Ob.Entry X) : Prop :=
  Ob.Tele.Rel e.toTele e'.toTele

def Ob.Entry.setoid (X : Ob) : Setoid (Ob.Entry X) where
  r := Ob.Entry.Rel
  iseqv := ⟨fun e => Ob.Tele.Rel.refl e.toTele, Ob.Tele.Rel.symm, Ob.Tele.Rel.trans⟩

/-- The classes of entries over a context class. -/
def Ty₁ (X : Ob) : Type := Quotient (Ob.Entry.setoid X)

/-- The telescope class an entry class presents. -/
def Ty₁.toTy {X : Ob} (a : Ty₁ X) : Ty.obj (Opposite.op X) :=
  Quotient.map Ob.Entry.toTele (fun _ _ h => h) a

theorem Ty₁.toTy_injective {X : Ob} : Function.Injective (Ty₁.toTy (X := X)) := by
  refine Quotient.ind₂ ?_
  intro e e' h
  exact Quotient.sound (Quotient.exact h : Ob.Tele.Rel e.toTele e'.toTele)

/-- The telescopes with a filling lying over the telescope an entry class
presents. -/
def Tm₁ (X : Ob) (a : Ty₁ X) : Type :=
  { t : Tm.obj (Opposite.op X) // Ob.Term.tele t = a.toTy }

/-- An entry reindexed along a filling. -/
def Ob.Entry.subst {X Y : Ob} (σ : Ob.Subst X Y) (e : Ob.Entry Y) : Ob.Entry X where
  arity := e.arity
  binding := dTel.actBase σ.1 e.binding
  declaration := Bd.act (Γ := 1) σ.1 e.arity e.declaration
  wf := Ob.Tele.Wf.subst σ e.toTele

theorem Ob.Entry.subst_congr {X Y : Ob} {σ σ' : Ob.Subst X Y} {e e' : Ob.Entry Y}
    (hσ : Ob.Subst.Rel X Y σ.1 σ'.1) (h : Ob.Entry.Rel e e') :
    Ob.Entry.Rel (Ob.Entry.subst σ e) (Ob.Entry.subst σ' e') := by
  exact Ob.Tele.Rel.subst hσ h

/-- A type reindexed along a substitution. -/
def Ty₁.subst {X Y : Ob} (a : Ty₁ Y) (σ : X ⟶ Y) : Ty₁ X :=
  Quotient.map₂ Ob.Entry.subst
    (fun _ _ hσ _ _ h => Ob.Entry.subst_congr hσ h) σ a

theorem Ty₁.toTy_subst {X Y : Ob} (a : Ty₁ Y) (σ : X ⟶ Y) :
    (a.subst σ).toTy = Ty.map σ.op a.toTy := by
  obtain ⟨σ⟩ := σ
  obtain ⟨e⟩ := a
  rfl

/-- A term reindexed along a substitution. -/
def Tm₁.subst {X Y : Ob} {a : Ty₁ Y} (t : Tm₁ Y a) (σ : X ⟶ Y) : Tm₁ X (a.subst σ) :=
  ⟨Tm.map σ.op t.1, by rw [Ob.Term.tele_map, t.2, Ty₁.toTy_subst]⟩

theorem Ty₁.subst_id {X : Ob} (a : Ty₁ X) : a.subst (𝟙 X) = a := by
  apply Ty₁.toTy_injective
  rw [Ty₁.toTy_subst, op_id]
  exact Functor.map_id_apply Ty (Opposite.op X) a.toTy

theorem Ty₁.subst_comp {X Y Z : Ob} (a : Ty₁ Y) (σ : X ⟶ Y) (θ : Z ⟶ X) :
    a.subst (θ ≫ σ) = (a.subst σ).subst θ := by
  apply Ty₁.toTy_injective
  rw [Ty₁.toTy_subst, Ty₁.toTy_subst, Ty₁.toTy_subst, op_comp]
  exact Functor.map_comp_apply Ty σ.op θ.op a.toTy

theorem Tm₁.subst_id {X : Ob} {a : Ty₁ X} (t : Tm₁ X a) : (t.subst (𝟙 X)).1 = t.1 :=
  (Functor.map_id_apply Tm (Opposite.op X) t.1 : Tm.map (𝟙 X).op t.1 = t.1)

theorem Tm₁.subst_comp {X Y Z : Ob} {a : Ty₁ Y} (t : Tm₁ Y a) (σ : X ⟶ Y) (θ : Z ⟶ X) :
    (t.subst (θ ≫ σ)).1 = ((t.subst σ).subst θ).1 :=
  (Functor.map_comp_apply Tm σ.op θ.op t.1 :
    Tm.map (θ ≫ σ).op t.1 = Tm.map θ.op (Tm.map σ.op t.1))

/-- Terms with the same underlying telescope with a filling are equal, across a
transport of their type. -/
theorem Tm₁.cast_eq {X : Ob} {a a' : Ty₁ X} (e : a = a') {t : Tm₁ X a} {t' : Tm₁ X a'}
    (h : t.1 = t'.1) : e ▸ t = t' := by
  subst e
  exact Subtype.ext h

theorem Tm₁.cast_val {X : Ob} {a a' : Ty₁ X} (e : a = a') (t : Tm₁ X a) :
    (e ▸ t : Tm₁ X a').1 = t.1 := by
  subst e
  rfl

/-- Terms with the same underlying telescope with a filling are heterogeneously
equal. -/
theorem Tm₁.heq_of_eq {X : Ob} {a a' : Ty₁ X} {t : Tm₁ X a} {t' : Tm₁ X a'}
    (h : t.1 = t'.1) : HEq t t' := by
  have e : a = a' := by
    apply Ty₁.toTy_injective
    rw [← t.2, ← t'.2, h]
  subst e
  exact _root_.heq_of_eq (Subtype.ext h)

/-- The expression a filling of the telescope an entry presents supplies. -/
def Ob.Fill.filler {X : Ob} {u : Ob.Entry X} (τ : Ob.Fill X u.toTele) :
    Expr (X.arity ⋈ u.arity) :=
  τ.1 (C.inl (C.singleSlot u.arity))

/-- The term given by a filling of the telescope an entry presents. -/
def Tm₁.ofFill {X : Ob} {e : Ob.Entry X} (τ : Ob.Fill X e.toTele) :
    Tm₁ X (Quotient.mk (Ob.Entry.setoid X) e) :=
  ⟨Quotient.mk (Ob.Term.setoid X) ⟨e.toTele, τ⟩, rfl⟩

theorem Tm₁.subst_ofFill {X Y : Ob} {u : Ob.Entry X} (τ : Ob.Fill X u.toTele)
    (σ : Ob.Subst Y X) :
    (Tm₁.ofFill τ).subst (Quotient.mk (Ob.Subst.setoid Y X) σ)
      = Tm₁.ofFill (e := Ob.Entry.subst σ u)
        ⟨_root_.Subst.applyEach σ.1 τ.1, Ob.Fill.Wf.subst σ ⟨u.toTele, τ⟩⟩ :=
  rfl

/-- The terms of the type an entry presents are its fillings. -/
def Tm₁.fillEquiv {X : Ob} (e : Ob.Entry X) :
    Tm₁ X (Quotient.mk (Ob.Entry.setoid X) e) ≃ Quotient (Ob.Fill.setoid e.toTele) :=
  (Equiv.subtypeQuotientEquivQuotientSubtype
      (fun s : Ob.Term X => Ob.Tele.Rel s.1 e.toTele)
      (s₂ := Ob.Term.fibreSetoid e.toTele)
      (fun t => Ob.Term.tele t = Quotient.mk (Ob.Tele.setoid X) e.toTele)
      (fun _ => ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩)
      (fun _ _ => Iff.rfl)).trans
    (Ob.Term.fibreEquiv e.toTele)

theorem Tm₁.fillEquiv_ofFill {X : Ob} {e : Ob.Entry X} (τ : Ob.Fill X e.toTele) :
    Tm₁.fillEquiv e (Tm₁.ofFill τ) = Quotient.mk (Ob.Fill.setoid e.toTele) τ :=
  rfl

/-- Induction on a term through the fillings of the telescope its entry
presents. -/
theorem Tm₁.ind {X : Ob} {e : Ob.Entry X}
    {motive : Tm₁ X (Quotient.mk (Ob.Entry.setoid X) e) → Prop}
    (ofFill : ∀ τ : Ob.Fill X e.toTele, motive (Tm₁.ofFill τ))
    (t : Tm₁ X (Quotient.mk (Ob.Entry.setoid X) e)) : motive t := by
  obtain ⟨u, hu⟩ := t
  refine Quotient.ind (motive := fun u =>
    ∀ hu : Ob.Term.tele u = Quotient.mk (Ob.Tele.setoid X) e.toTele,
      motive ⟨u, hu⟩) ?_ u hu
  intro s hs
  have hrel : Ob.Tele.Rel s.1 e.toTele := Quotient.exact hs
  have h : Tm₁.ofFill (Ob.Fill.ofRel hrel s.2)
      = ⟨Quotient.mk (Ob.Term.setoid X) s, hs⟩ :=
    Subtype.ext (Quotient.sound (Ob.Term.fibre_left ⟨s, hrel⟩))
  exact h ▸ ofFill (Ob.Fill.ofRel hrel s.2)

/-- 13.2: the generic term of a one-entry type. -/
def Tm₁.generic {X : Ob} (a : Ty₁ X) :
    Tm₁ (Ob.extend X a.toTy) (a.subst (Ob.projection X a.toTy)) :=
  ⟨Ob.generic X a.toTy, by rw [Ty₁.toTy_subst]; exact Ob.generic_tele X a.toTy⟩

theorem Ob.Entry.arity_cast {Z Z' : Ob} (h : Z = Z') (u : Ob.Entry Z) :
    (h ▸ u).arity = u.arity := by
  subst h
  rfl

theorem Ob.Entry.binding_cast {Z Z' : Ob} (h : Z = Z') (u : Ob.Entry Z) :
    HEq (h ▸ u).binding u.binding := by
  subst h
  rfl

theorem Ob.Entry.declaration_cast {Z Z' : Ob} (h : Z = Z') (u : Ob.Entry Z) :
    HEq (h ▸ u).declaration u.declaration := by
  subst h
  rfl

theorem Ty₁.mk_cast {Z Z' : Ob} (h : Z = Z') (u : Ob.Entry Z) :
    cast (congrArg Ty₁ h) (Quotient.mk (Ob.Entry.setoid Z) u)
      = Quotient.mk (Ob.Entry.setoid Z') (h ▸ u) := by
  subst h
  rfl

theorem Ty₁.heq_mk {X X' : Ob} (h : X = X') {γ : C.Arity}
    {Θ : dTel X.arity γ} {β : Bd (X.arity ⋈ γ)}
    {w : Ob.Tele.Wf X (dTel.cons Θ β .nil)}
    {Θ' : dTel X'.arity γ} {β' : Bd (X'.arity ⋈ γ)}
    {w' : Ob.Tele.Wf X' (dTel.cons Θ' β' .nil)}
    (hrel : ∀ e : X.arity = X'.arity,
      Ob.Tele.Eq X' (e ▸ dTel.cons Θ β .nil) (dTel.cons Θ' β' .nil)) :
    HEq (Quotient.mk (Ob.Entry.setoid X) ⟨γ, Θ, β, w⟩)
      (Quotient.mk (Ob.Entry.setoid X') ⟨γ, Θ', β', w'⟩) := by
  subst h
  exact heq_of_eq (Quotient.sound ⟨rfl, hrel rfl⟩)

theorem Ty₁.eq_of_heq_mk {X X' : Ob} (h : X = X') {γ γ' : C.Arity}
    {Θ : dTel X.arity γ} {β : Bd (X.arity ⋈ γ)}
    {w : Ob.Tele.Wf X (dTel.cons Θ β .nil)}
    {Θ' : dTel X'.arity γ'} {β' : Bd (X'.arity ⋈ γ')}
    {w' : Ob.Tele.Wf X' (dTel.cons Θ' β' .nil)}
    (hu : HEq (Quotient.mk (Ob.Entry.setoid X) ⟨γ, Θ, β, w⟩)
      (Quotient.mk (Ob.Entry.setoid X') ⟨γ', Θ', β', w'⟩)) :
    ∃ hγ : γ = γ', ∀ e : X.arity = X'.arity,
      Ob.Tele.Eq X' (e ▸ hγ ▸ dTel.cons Θ β .nil) (dTel.cons Θ' β' .nil) := by
  subst h
  obtain ⟨hs, hrel⟩ := Quotient.exact (eq_of_heq hu)
  have hs' : C.single γ = C.single γ' := hs
  obtain rfl := C.single_injective hs'
  exact ⟨rfl, fun _ => hrel⟩

theorem Ty₁.extend_heq {X X' : Ob} (h : X = X') {a : Ty₁ X} {a' : Ty₁ X'}
    (ha : HEq a a') : Ob.extend X a.toTy = Ob.extend X' a'.toTy := by
  subst h
  obtain rfl := eq_of_heq ha
  rfl

theorem Equiv.heq_congr {α α' β β' : Type} (hα : α = α') (hβ : β = β')
    {u : α ≃ β} {u' : α' ≃ β'}
    (h : ∀ (x : α) (x' : α'), HEq x x' → HEq (u x) (u' x')) : HEq u u' := by
  subst hα
  subst hβ
  exact heq_of_eq (Equiv.ext fun x => eq_of_heq (h x x HEq.rfl))

theorem Tm₁.eq_of_heq {X : Ob} {b b' : Ty₁ X} (hb : b = b') {t : Tm₁ X b}
    {t' : Tm₁ X b'} (h : HEq t t') : t.1 = t'.1 := by
  subst hb
  exact congrArg Subtype.val (_root_.eq_of_heq h)

theorem Tm₁.heq_of_heq_val {X X' : Ob} (hX : X = X') {b : Ty₁ X} {b' : Ty₁ X'}
    {t : Tm₁ X b} {t' : Tm₁ X' b'} (h : HEq t.1 t'.1) : HEq t t' := by
  subst hX
  exact Tm₁.heq_of_eq (_root_.eq_of_heq h)

theorem Tm₁.heq_val {Z Z' : Ob} (h : Z = Z') {c : Ty₁ Z} {c' : Ty₁ Z'}
    (hc : HEq c c') {x : Tm₁ Z c} {x' : Tm₁ Z' c'} (hx : HEq x x') :
    HEq x.1 x'.1 := by
  subst h
  obtain rfl := _root_.eq_of_heq hc
  obtain rfl := _root_.eq_of_heq hx
  rfl

theorem Tm₁.type_congr {Z Z' : Ob} (h : Z = Z') {c : Ty₁ Z} {c' : Ty₁ Z'}
    (hc : HEq c c') : Tm₁ Z c = Tm₁ Z' c' := by
  subst h
  obtain rfl := _root_.eq_of_heq hc
  rfl

/-- 10.4: a substitution extended past a type. -/
def Ty₁.lift {X Y : Ob} (a : Ty₁ X) (σ : Y ⟶ X) :
    Ob.extend Y (a.subst σ).toTy ⟶ Ob.extend X a.toTy :=
  (Ty₁.toTy_subst a σ).symm ▸ Ob.lift a.toTy σ

theorem Ty₁.lift_mk {Ξ Γ : Ctx} (e : Ob.Entry Γ.toOb)
    (σ : Ob.Subst Ξ.toOb Γ.toOb) :
    Ty₁.lift (Quotient.mk (Ob.Entry.setoid Γ.toOb) e)
        (Quotient.mk (Ob.Subst.setoid Ξ.toOb Γ.toOb) σ)
      = Ctx.lift σ e.toTele :=
  Ob.lift_mk σ e.toTele

theorem Ty₁.projection_lift {X Y : Ob} (a : Ty₁ X) (σ : Y ⟶ X) :
    a.lift σ ≫ Ob.projection X a.toTy
      = Ob.projection Y (a.subst σ).toTy ≫ σ := by
  obtain ⟨e⟩ := a
  obtain ⟨σ⟩ := σ
  exact Ob.pair_projection _ _ _

theorem Ty₁.generic_lift {X Y : Ob} (a : Ty₁ X) (σ : Y ⟶ X) :
    HEq ((Tm₁.generic a).subst (a.lift σ)) (Tm₁.generic (a.subst σ)) := by
  refine Tm₁.heq_of_eq ?_
  obtain ⟨e⟩ := a
  obtain ⟨σ⟩ := σ
  exact Ob.pair_generic _ _ _

/-- 13.2 on one-entry types: a substitution paired with a term over it. -/
def Ty₁.pair {X Y : Ob} {a : Ty₁ Y} (σ : X ⟶ Y) (t : Tm₁ X (a.subst σ)) :
    X ⟶ Ob.extend Y a.toTy :=
  Ob.pair σ t.1 (t.2.trans (Ty₁.toTy_subst a σ))

theorem Ty₁.projection_pair {X Y : Ob} {a : Ty₁ Y} (σ : X ⟶ Y)
    (t : Tm₁ X (a.subst σ)) :
    Ty₁.pair σ t ≫ Ob.projection Y a.toTy = σ :=
  Ob.pair_projection σ t.1 _

theorem Ty₁.generic_pair {X Y : Ob} {a : Ty₁ Y} (σ : X ⟶ Y)
    (t : Tm₁ X (a.subst σ)) :
    HEq ((Tm₁.generic a).subst (Ty₁.pair σ t)) t :=
  Tm₁.heq_of_eq (Ob.pair_generic σ t.1 _)

theorem Ty₁.pair_eta {X : Ob} (a : Ty₁ X) :
    Ty₁.pair (Ob.projection X a.toTy) (Tm₁.generic a) = 𝟙 (Ob.extend X a.toTy) :=
  Ob.pair_eta X a.toTy

end Ctx
