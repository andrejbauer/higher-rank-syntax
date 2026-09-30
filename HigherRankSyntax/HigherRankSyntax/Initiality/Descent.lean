import HigherRankSyntax.Initiality.Concatenation
import HigherRankSyntax.Ctx.Model

/-!
# The interpretation of context classes, types, terms and substitutions

The object of a context class is the end of the interpretation of its ambient at the
empty environment over the empty object, and its environment is the empty
environment extended by that interpretation. An entry over a context class is
interpreted, at the environment of the class, as a telescope and a boundary; the type
it presents is `Bind` of the telescope's chain at the boundary's type. A filling of the
one-entry telescope of an entry gives the term the interpreted entry is given by the
interpretation of the filler. A filling from `X` to `Y` gives, from the identity at the
environment of `X`, a section into the end of the chain of `Y` reindexed along the
substitution into the empty object; the substitution it presents is that section
followed by the lift of the substitution into the empty object through the chain.

Each of these respects the equalities the classes are taken modulo. The interpretation
of the ambient of an extension by an entry class is the interpretation of the ambient
of the base followed by the one-entry telescope of the interpreted entry.
-/

universe u

open CategoryTheory

namespace HrS

variable {M : Structure.{u}}

/-! ### Entries -/

namespace Environment

/-- The interpretation of an entry with binding telescope `binding` and declaration
`declaration`: an interpretation of the binding telescope, and an interpretation of the
declaration at the environment extended by the interpreted binding decoration. -/
def interpretEntry {Γ : M.Ob} {Δ γ : C.Arity} (E : Environment M Γ Δ) (binding : dTel Δ γ)
    (declaration : Bd (Δ ⋈ γ)) : Part (Σ T : Telescope M Γ γ, Boundary M T.chain.last) :=
  (E.interpretTelescope binding).bind fun T =>
    ((E.extend T.decoration).interpretBoundary declaration).map fun B => ⟨T, B⟩

/-- An entry is interpreted as a telescope and a boundary exactly when the telescope
interprets its binding telescope and the boundary interprets its declaration at the
environment extended by the telescope's decoration. -/
theorem mem_interpretEntry
    {Γ : M.Ob} {Δ γ : C.Arity} (E : Environment M Γ Δ) (binding : dTel Δ γ)
    (declaration : Bd (Δ ⋈ γ)) (p : Σ T : Telescope M Γ γ, Boundary M T.chain.last) :
  p ∈ E.interpretEntry binding declaration
    ↔ p.1 ∈ E.interpretTelescope binding
        ∧ p.2 ∈ (E.extend p.1.decoration).interpretBoundary declaration
  := by
  simp only [interpretEntry, Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨T, hT, B, hB, rfl⟩
    exact ⟨hT, hB⟩
  · rintro ⟨hT, hB⟩
    use p.1, hT, p.2, hB

/-- The environments for the arity with no slots are all equal. -/
instance {Γ : M.Ob} : Subsingleton (Environment M Γ 1) where
  allEq _ _ := by
    funext _ x
    apply (C.unit_is_empty x).elim

/-- A term that the entry `T`, `B` reindexed along the identity is given by the
interpretation of `f` at `E` extended by the reindexed binding decoration is
heterogeneously equal to a term that `T`, `B` is given by the interpretation of `f` at
`E` extended by the binding decoration. -/
theorem entryTerm_subst_identity
    {Γ : M.Ob} {Δ α : C.Arity} (E : Environment M Γ Δ) (T : Telescope M Γ α)
    (B : Boundary M T.chain.last) (f : Expr (Δ ⋈ α)) {t}
    (ht : t ∈ (T.chain.subst (M.identity Γ)).entryTerm (B.subst (T.chain.lift (M.identity Γ)))
      ((E.extend (T.decoration.subst (M.identity Γ))).interpret f)) :
  ∃ t' ∈ T.chain.entryTerm B ((E.extend T.decoration).interpret f), HEq t t'
  := by
  apply Chain.entryTerm_congr (Chain.subst_identity _) _ _ ht
  · apply HEq.trans _ (heq_of_eq (Boundary.subst_identity B))
    congr 1
    · rw [Chain.subst_identity]
    · apply Chain.lift_identity
  · congr 1
    · rw [Chain.subst_identity]
    · congr 1
      · apply Chain.subst_identity
      · apply Decoration.subst_identity

end Environment

open Environment

/-! ### Objects and environments -/

variable (M) in
/-- The interpretation of the ambient of a context class, at the empty environment over
the empty object. -/
def telescopeOf (X : Ctx.Ob) : Telescope M M.empty X.arity :=
  Quotient.hrecOn X (motive := fun X : Ctx.Ob => Telescope M M.empty X.arity)
    (fun Γ => ((Environment.empty M.empty).interpretTelescope Γ.ambient).get
      (Part.dom_iff_mem.mpr (Ambient.Wf.sound Γ.wf M.empty)))
    (by
      rintro ⟨_, Ξ, _⟩ ⟨_, Ξ', _⟩ ⟨rfl, hΞ⟩
      apply heq_of_eq
      symm
      apply Part.get_eq_of_mem
      apply Eq_t.sound hΞ _ (Typed.empty M.empty) _ (Part.get_mem _))

variable (M) in
/-- The object of a context class: the end of the interpretation of its ambient. -/
def onOb (X : Ctx.Ob) : M.Ob :=
  (telescopeOf M X).chain.last

variable (M) in
/-- The environment of a context class: the empty environment extended by the
interpretation of its ambient. -/
def envOf (X : Ctx.Ob) : Environment M (onOb M X) X.arity :=
  (Environment.empty M.empty).extend (telescopeOf M X).decoration

/-- The environment of the class of a context is typed by its ambient. -/
theorem envOf_typed (Γ : Ctx) :
  (envOf M (Quotient.mk _ Γ)).Typed Γ.ambient
  := by
  apply Typed.extend (Typed.empty M.empty)
  apply Part.get_mem

/-! ### Types -/

/-- An entry over a context class is interpreted at the environment of the class. -/
theorem interpretEntry_dom {X : Ctx.Ob} (e : Ctx.Ob.Entry X) :
  ((envOf M X).interpretEntry e.binding e.declaration).Dom
  := by
  induction X using Quotient.ind with
  | _ Γ =>
      obtain ⟨T, hT⟩ := Wf_t.sound e.wf _ (envOf_typed (M := M) Γ)
      obtain ⟨T₀, hT₀, B, hB, -⟩ := (mem_interpretTelescope_cons _ _ _ _ T).mp hT
      apply Part.dom_iff_mem.mpr
      use ⟨T₀, B⟩
      apply (mem_interpretEntry _ _ _ _).mpr ⟨hT₀, hB⟩

variable (M) in
/-- The interpretation of an entry over a context class at the environment of the
class. -/
def entryOf {X : Ctx.Ob} (e : Ctx.Ob.Entry X) :
    Σ T : Telescope M (onOb M X) e.arity, Boundary M T.chain.last :=
  ((envOf M X).interpretEntry e.binding e.declaration).get (interpretEntry_dom e)

/-- The interpreted entry interprets the entry's binding telescope and declaration. -/
theorem entryOf_mem {X : Ctx.Ob} (e : Ctx.Ob.Entry X) :
  (entryOf M e).1 ∈ (envOf M X).interpretTelescope e.binding
    ∧ (entryOf M e).2
        ∈ ((envOf M X).extend (entryOf M e).1.decoration).interpretBoundary e.declaration
  := (mem_interpretEntry _ _ _ _).mp (Part.get_mem _)

/-- The one-entry telescope of the interpreted entry interprets the one-entry telescope
of the entry. -/
theorem entryOf_telescope {X : Ctx.Ob} (e : Ctx.Ob.Entry X) :
  ⟨.cons ((entryOf M e).1.chain.Bind (entryOf M e).2.ty) .nil,
      .cons (entryOf M e).1.decoration (entryOf M e).2 _ rfl .nil⟩
    ∈ (envOf M X).interpretTelescope e.toTele.telescope
  := by
  apply (mem_interpretTelescope_cons _ _ _ _ _).mpr
  use (entryOf M e).1, (entryOf_mem e).1, (entryOf M e).2, (entryOf_mem e).2,
    (entryOf M e).1.chain.Bind (entryOf M e).2.ty, rfl, ⟨.nil, .nil⟩, Part.mem_some _
  rfl

/-- Entries of one arity whose one-entry telescopes are equal have the same
interpretation. -/
theorem entryOf_congr
    {X : Ctx.Ob} {γ : C.Arity} {binding binding' : dTel X.arity γ}
    {declaration declaration' : Bd (X.arity ⋈ γ)}
    {w : Ctx.Ob.Tele.Wf X (.cons binding declaration .nil)}
    {w' : Ctx.Ob.Tele.Wf X (.cons binding' declaration' .nil)}
    (h : Ctx.Ob.Tele.Eq X (.cons binding declaration .nil) (.cons binding' declaration' .nil)) :
  entryOf M ⟨γ, binding, declaration, w⟩ = entryOf M ⟨γ, binding', declaration', w'⟩
  := by
  induction X using Quotient.ind with
  | _ Γ =>
      obtain ⟨-, _, _, _, hcons, hbinding, hdeclaration, -⟩ := h
      injection hcons with _ _ _ hbinding' hdeclaration' _
      subst hbinding' hdeclaration'
      obtain ⟨hT, hB⟩ := entryOf_mem (M := M) ⟨γ, binding, declaration, w⟩
      symm
      apply Part.get_eq_of_mem
      apply (mem_interpretEntry _ _ _ _).mpr
      constructor
      · apply Eq_t.sound hbinding _ (envOf_typed Γ) _ hT
      · convert hB using 1
        symm
        apply Eq_bd.sound hdeclaration _ (Typed.extend (envOf_typed Γ) hT)

variable (M) in
/-- The type an entry class presents: `Bind` of the chain of the interpreted binding
telescope of an entry of the class at the type of its interpreted declaration. -/
def onTy {X : Ctx.Ob} (a : Ctx.Ty₁ X) : M.Ty (onOb M X) :=
  Quotient.lift (fun e => (entryOf M e).1.chain.Bind (entryOf M e).2.ty)
    (by
      rintro ⟨γ, binding, declaration, w⟩ ⟨γ', binding', declaration', w'⟩ ⟨harity, h⟩
      obtain rfl : γ = γ' := C.single_injective harity
      dsimp only
      rw [entryOf_congr h])
    a

/-! ### Terms -/

/-- The filler of a filling of the one-entry telescope of an entry gives the interpreted
entry a term. -/
theorem entryTerm_dom {X : Ctx.Ob} {e : Ctx.Ob.Entry X} (τ : Ctx.Ob.Fill X e.toTele) :
  ((entryOf M e).1.chain.entryTerm (entryOf M e).2
      (((envOf M X).extend (entryOf M e).1.decoration).interpret τ.filler)).Dom
  := by
  induction X using Quotient.ind with
  | _ Γ =>
      obtain ⟨s, hs⟩ := Wf_s.sound τ.2.2 _ (envOf_typed (M := M) Γ) _ (entryOf_telescope e)
      obtain ⟨t, ht, -⟩ := (mem_interpretFilling_cons _ _ _ _ _ _ _ _ _).mp hs
      obtain ⟨t', ht', -⟩ := entryTerm_subst_identity _ _ _ _ ht
      apply Part.dom_iff_mem.mpr ⟨t', ht'⟩

variable (M) in
/-- The term a filling of the one-entry telescope of an entry gives: the term the
interpreted entry is given by the interpretation of the filler, at the environment
extended by the interpreted binding decoration. -/
def termOf {X : Ctx.Ob} {e : Ctx.Ob.Entry X} (τ : Ctx.Ob.Fill X e.toTele) :
    M.Tm (onOb M X) ((entryOf M e).1.chain.Bind (entryOf M e).2.ty) :=
  ((entryOf M e).1.chain.entryTerm (entryOf M e).2
      (((envOf M X).extend (entryOf M e).1.decoration).interpret τ.filler)).get
    (entryTerm_dom τ)

/-- The term a filling gives is a term the interpreted entry is given by the
interpretation of the filler. -/
theorem termOf_mem {X : Ctx.Ob} {e : Ctx.Ob.Entry X} (τ : Ctx.Ob.Fill X e.toTele) :
  termOf M τ ∈ (entryOf M e).1.chain.entryTerm (entryOf M e).2
    (((envOf M X).extend (entryOf M e).1.decoration).interpret τ.filler)
  := Part.get_mem _

/-- Fillings of the one-entry telescopes of two entries that are related as terms (the
telescopes equal and the fillings agreeing) give heterogeneously equal terms. -/
theorem termOf_heq
    {X : Ctx.Ob} {e e' : Ctx.Ob.Entry X} (τ : Ctx.Ob.Fill X e.toTele)
    (τ' : Ctx.Ob.Fill X e'.toTele) (h : Ctx.Ob.Term.Rel ⟨e.toTele, τ⟩ ⟨e'.toTele, τ'⟩) :
  HEq (termOf M τ) (termOf M τ')
  := by
  induction X using Quotient.ind with
  | _ Γ =>
      obtain ⟨γ, binding, declaration, w⟩ := e
      obtain ⟨γ', binding', declaration', w'⟩ := e'
      obtain ⟨harity, htele, hfill⟩ := h
      obtain rfl : γ = γ' := C.single_injective harity
      obtain ⟨-, hτ, hττ'⟩ := hfill
      obtain ⟨s, hs⟩ := Wf_s.sound hτ _ (envOf_typed (M := M) Γ) _ (entryOf_telescope _)
      have hs' := Eq_s.sound hττ' _ (envOf_typed (M := M) Γ) _ (entryOf_telescope _) s hs
      obtain ⟨t₁, ht₁, hs₁⟩ := (mem_interpretFilling_cons _ _ _ _ _ _ _ _ _).mp hs
      obtain ⟨t₂, ht₂, hs₂⟩ := (mem_interpretFilling_cons _ _ _ _ _ _ _ _ _).mp hs'
      obtain rfl := (mem_interpretFilling_nil _ _ _ _).mp hs₁
      have hpair := (mem_interpretFilling_nil _ _ _ _).mp hs₂
      have ht : HEq t₁ t₂ := by
        apply HEq.trans (HEq.symm (eqRec_heq _ _))
        apply HEq.trans (HEq.symm (M.generic_pair (M.identity _) _))
        apply HEq.trans (congr_arg_heq (M.substTm (M.generic _)) hpair)
        apply HEq.trans (M.generic_pair _ _)
        apply eqRec_heq
      obtain ⟨t₁', ht₁', h₁⟩ := entryTerm_subst_identity _ _ _ _ ht₁
      obtain ⟨t₂', ht₂', h₂⟩ := entryTerm_subst_identity _ _ _ _ ht₂
      rw [Part.mem_unique (termOf_mem τ) ht₁']
      apply HEq.trans (HEq.symm h₁)
      apply HEq.trans ht
      apply HEq.trans h₂
      have hmem := termOf_mem (M := M) τ'
      generalize termOf M τ' = y at hmem ⊢
      revert y
      rw [← entryOf_congr (w := w) (w' := w') htele]
      intro y hmem
      apply heq_of_eq (Part.mem_unique ht₂' hmem)

variable (M) in
/-- The term a term class presents: the term a filling of the one-entry telescope of an
entry of its type gives. -/
def onTm {X : Ctx.Ob} {a : Ctx.Ty₁ X} (t : Ctx.Tm₁ X a) : M.Tm (onOb M X) (onTy M a) :=
  Quotient.hrecOn a (motive := fun a => Ctx.Tm₁ X a → M.Tm (onOb M X) (onTy M a))
    (fun e t => Quotient.lift (termOf M)
      (fun τ τ' h => eq_of_heq (termOf_heq τ τ' (Ctx.Ob.Term.fibre_comap τ τ' h)))
      (Ctx.Tm₁.fillEquiv e t))
    (by
      intro e e' h
      have ha : Quotient.mk (Ctx.Ob.Entry.setoid X) e = Quotient.mk _ e' := Quotient.sound h
      apply Function.hfunext (by rw [ha])
      intro t t' htt
      induction t using Ctx.Tm₁.ind with
      | ofFill τ =>
          induction t' using Ctx.Tm₁.ind with
          | ofFill τ' =>
              apply termOf_heq τ τ'
              apply Quotient.exact (s := Ctx.Ob.Term.setoid X)
              apply eq_of_heq (Ctx.Tm₁.heq_val rfl (heq_of_eq ha) htt))
    t

/-! ### Substitutions -/

/-- The interpretation of the ambient of `Δ`, reindexed along the substitution into the
empty object, interprets at the environment of `Γ` the ambient of `Δ` renamed into the
arity of `Γ`. -/
theorem telescopeOf_rename (Γ Δ : Ctx) :
  (telescopeOf M (Quotient.mk _ Δ)).subst (M.toEmpty (onOb M (Quotient.mk _ Γ)))
    ∈ (envOf M (Quotient.mk _ Γ)).interpretTelescope
        (dTel.rename (Renaming.fromUnit Γ.arity) Δ.ambient)
  := by
  rw [interpretTelescope_rename,
    Subsingleton.elim ((envOf M (Quotient.mk _ Γ)).rename _)
      ((Environment.empty M.empty).subst (M.toEmpty (onOb M (Quotient.mk _ Γ))))]
  apply interpretTelescope_subst _ _ _ _ (Part.get_mem _)

/-- A filling from `X` to `Y` is interpreted at the environment of `X`, from the
identity, along the decoration of the interpretation of the ambient of `Y` reindexed
along the substitution into the empty object. -/
theorem sectionOf_dom {X Y : Ctx.Ob} (σ : Ctx.Ob.Subst X Y) :
  ((envOf M X).interpretFilling σ.1
    ((telescopeOf M Y).decoration.subst (M.toEmpty (onOb M X))) (M.identity (onOb M X))).Dom
  := by
  induction X using Quotient.ind with
  | _ Γ =>
      induction Y using Quotient.ind with
      | _ Δ =>
          apply Part.dom_iff_mem.mpr
          apply Wf_s.sound σ.2 _ (envOf_typed Γ) _ (telescopeOf_rename Γ Δ)

variable (M) in
/-- The section a filling from `X` to `Y` gives: its interpretation at the environment of
`X`, from the identity, along the decoration of the interpretation of the ambient of `Y`
reindexed along the substitution into the empty object. -/
def sectionOf {X Y : Ctx.Ob} (σ : Ctx.Ob.Subst X Y) :
    M.Sub (onOb M X) ((telescopeOf M Y).chain.subst (M.toEmpty (onOb M X))).last :=
  ((envOf M X).interpretFilling σ.1
    ((telescopeOf M Y).decoration.subst (M.toEmpty (onOb M X))) (M.identity (onOb M X))).get
    (sectionOf_dom σ)

/-- Agreeing fillings from `X` to `Y` give the same section. -/
theorem sectionOf_congr {X Y : Ctx.Ob} {σ σ' : Ctx.Ob.Subst X Y}
    (h : Ctx.Ob.Subst.Rel X Y σ.1 σ'.1) :
  sectionOf M σ = sectionOf M σ'
  := by
  induction X using Quotient.ind with
  | _ Γ =>
      induction Y using Quotient.ind with
      | _ Δ =>
          obtain ⟨-, hσσ'⟩ := h
          symm
          apply Part.get_eq_of_mem
          apply Eq_s.sound hσσ' _ (envOf_typed Γ) _ (telescopeOf_rename Γ Δ) _ (Part.get_mem _)

variable (M) in
/-- The substitution a morphism of context classes presents: the section a filling
representing it gives, followed by the lift of the substitution into the empty object
through the chain of the interpretation of the ambient of the codomain. -/
def onSub {X Y : Ctx.Ob} (f : X ⟶ Y) : M.Sub (onOb M X) (onOb M Y) :=
  Quotient.lift (s := Ctx.Ob.Subst.setoid X Y)
    (fun σ => M.comp ((telescopeOf M Y).chain.lift (M.toEmpty (onOb M X))) (sectionOf M σ))
    (fun _ _ h => congrArg _ (sectionOf_congr h)) f

/-! ### Representatives -/

/-- The type the class of an entry presents is `Bind` of the chain of its interpreted
binding telescope at the type of its interpreted declaration. -/
theorem onTy_mk {X : Ctx.Ob} (e : Ctx.Ob.Entry X) :
  onTy M (Quotient.mk _ e) = (entryOf M e).1.chain.Bind (entryOf M e).2.ty
  := rfl

/-- The section a filling gives is its interpretation. -/
theorem sectionOf_mem {X Y : Ctx.Ob} (σ : Ctx.Ob.Subst X Y) :
  sectionOf M σ ∈ (envOf M X).interpretFilling σ.1
    ((telescopeOf M Y).decoration.subst (M.toEmpty (onOb M X))) (M.identity (onOb M X))
  := Part.get_mem _

/-- The substitution the class of a filling presents is the section the filling gives,
followed by the lift of the substitution into the empty object. -/
theorem onSub_mk {X Y : Ctx.Ob} (σ : Ctx.Ob.Subst X Y) :
  onSub M (Quotient.mk _ σ)
    = M.comp ((telescopeOf M Y).chain.lift (M.toEmpty (onOb M X))) (sectionOf M σ)
  := rfl

/-! ### Extension -/

/-- The interpretation of the ambient of the extension of the class of `Γ` by the class of
an entry is the interpretation of the ambient of `Γ` followed by the one-entry telescope
of the interpreted entry. -/
theorem telescopeOf_extend (Γ : Ctx) (e : Ctx.Ob.Entry (Quotient.mk _ Γ)) :
  telescopeOf M (Ctx.Ob.extend (Quotient.mk _ Γ) (Ctx.Ty₁.toTy (Quotient.mk _ e)))
    = (telescopeOf M (Quotient.mk _ Γ)).append ⟨.cons (onTy M (Quotient.mk _ e)) .nil,
        .cons (entryOf M e).1.decoration (entryOf M e).2 _ rfl .nil⟩
  := by
  apply Part.get_eq_of_mem
  apply interpretTelescope_concatenate _ _ _ _ _ (Part.get_mem _) (entryOf_telescope e)

/-- The object of the extension of a context class by a type class is the extension of
the object by the type. -/
theorem onOb_extend (X : Ctx.Ob) (a : Ctx.Ty₁ X) :
  onOb M (Ctx.Ob.extend X a.toTy) = M.extend (onOb M X) (onTy M a)
  := by
  induction X using Quotient.ind with
  | _ Γ =>
      induction a using Quotient.ind with
      | _ e =>
          apply Eq.trans (congrArg (fun T => T.chain.last) (telescopeOf_extend (M := M) Γ e))
          apply Chain.last_append

/-- The environment of the extension of the class of `Γ` by the class of an entry is the
environment of `Γ` extended by the one-entry decoration of the interpreted entry. -/
theorem envOf_extend (Γ : Ctx) (e : Ctx.Ob.Entry (Quotient.mk _ Γ)) :
  HEq (envOf M (Ctx.Ob.extend (Quotient.mk _ Γ) (Ctx.Ty₁.toTy (Quotient.mk _ e))))
    ((envOf M (Quotient.mk _ Γ)).extend
      (Decoration.cons (entryOf M e).1.decoration (entryOf M e).2 (onTy M (Quotient.mk _ e)) rfl
        .nil))
  := by
  apply HEq.trans (congr_arg_heq (fun T => (Environment.empty M.empty).extend T.decoration)
    (telescopeOf_extend Γ e))
  apply extend_append

/-! ### The environment of a substitution -/

/-- Restricted to its new slots, an environment extended by a decoration is the empty
environment extended by that decoration. -/
theorem Environment.rename_inr_extend
    {Γ : M.Ob} {Δ Ω : C.Arity} (E : Environment M Γ Δ) {c : Chain M Γ Ω}
    (d : Decoration M c) :
  (E.extend d).rename (Renaming.inr Δ Ω) = (Environment.empty Γ).extend d
  := by
  funext β z
  apply Eq.trans (extend_inr E d z)
  rw [← extend_inr (Environment.empty Γ) d z, C.unit_left]

/-- Reindexed along the section a filling from `X` to `Y` gives, the new slots of the
environment of `X` extended by the reindexed decoration of the ambient of `Y` hold the
environment of `Y` reindexed along the substitution the filling presents. -/
theorem envOf_substitution {X Y : Ctx.Ob} (σ : Ctx.Ob.Subst X Y) :
  (((envOf M X).extend ((telescopeOf M Y).decoration.subst (M.toEmpty (onOb M X)))).subst
      (sectionOf M σ)).rename (Renaming.inr X.arity Y.arity)
    = (envOf M Y).subst (onSub M (Quotient.mk _ σ))
  := by
  have h : ((envOf M X).extend ((telescopeOf M Y).decoration.subst (M.toEmpty (onOb M X)))).rename
        (Renaming.inr X.arity Y.arity)
      = (envOf M Y).subst ((telescopeOf M Y).chain.lift (M.toEmpty (onOb M X))) := by
    rw [rename_inr_extend, Subsingleton.elim (Environment.empty (onOb M X))
      ((Environment.empty M.empty).subst (M.toEmpty (onOb M X))), extend_subst]
    rfl
  rw [onSub_mk]
  erw [subst_comp, ← h]
  rfl

end HrS
