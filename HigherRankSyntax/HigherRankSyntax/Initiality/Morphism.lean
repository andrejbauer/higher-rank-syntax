import HigherRankSyntax.Initiality.Descent
import HigherRankSyntax.HrS.Morphism

/-!
# The morphism from the model on context classes

The maps `onOb`, `onSub`, `onTy`, `onTm` preserve the operations of `Ctx.model`, so
they form a morphism `initialMorphism M` from `Ctx.model` to `M`.

The substitution the class of a filling from `X` to `Y` presents is the interpretation
of the filling at the environment of `X`, along the decoration of the interpretation of
the ambient of `Y`, from the substitution into the empty object. Reindexed along it,
an interpretation at the environment of `Y` is an interpretation at the environment of
`X` of the syntax with the filling substituted.
-/

universe u

open CategoryTheory

namespace HrS

variable {M : Structure.{u}}

/-! ### Substitutions as interpretations of fillings -/

/-- The substitution the class of a filling from `X` to `Y` presents is the
interpretation of the filling at the environment of `X`, along the decoration of the
interpretation of the ambient of `Y`, from the substitution into the empty object. -/
theorem onSub_mem {X Y : Ctx.Ob} (σ : Ctx.Ob.Subst X Y) :
  onSub M (Quotient.mk _ σ)
    ∈ (envOf M X).interpretFilling σ.1 (telescopeOf M Y).decoration (M.toEmpty (onOb M X))
  := by
  rw [Environment.interpretFilling, ← M.comp_identity (M.toEmpty _),
    Environment.pairFillers_comp, onSub_mk]
  apply Part.mem_map
  apply sectionOf_mem

/-- An interpretation of a telescope at the environment of `Y`, reindexed along the
substitution a filling `σ` from `X` to `Y` presents, is an interpretation at the
environment of `X` of the telescope with `σ` substituted in its base. -/
theorem interpretTelescope_actBase
    {X Y : Ctx.Ob} (σ : Ctx.Ob.Subst X Y) {Ω : C.Arity} {Θ : dTel Y.arity Ω}
    {T : Telescope M (onOb M Y) Ω} (hT : T ∈ (envOf M Y).interpretTelescope Θ) :
  T.subst (onSub M (Quotient.mk _ σ)) ∈ (envOf M X).interpretTelescope (dTel.actBase σ.1 Θ)
  := by
  rw [← dTel.instantiate_weaken]
  apply Environment.interpretTelescope_fill
    (Environment.Filling.ofSection _ _ _ _ (sectionOf_mem σ))
  rw [Environment.interpretTelescope_rename, envOf_substitution]
  apply Environment.interpretTelescope_subst _ _ _ _ hT

/-- An interpretation of a boundary at the environment of `Y` extended by a decoration
`D`, reindexed along the lift through the chain of `D` of the substitution a filling `σ`
from `X` to `Y` presents, is an interpretation of the boundary acted on by `σ` at the
environment of `X` extended by `D` reindexed along that substitution. -/
theorem interpretBoundary_act
    {X Y : Ctx.Ob} (σ : Ctx.Ob.Subst X Y) {Φ : C.Arity} {c : Chain M (onOb M Y) Φ}
    {D : Decoration M c} {β : Bd (Y.arity ⋈ Φ)} {B : Boundary M c.last}
    (hB : B ∈ ((envOf M Y).extend D).interpretBoundary β) :
  B.subst (c.lift (onSub M (Quotient.mk _ σ)))
    ∈ ((envOf M X).extend (D.subst (onSub M (Quotient.mk _ σ)))).interpretBoundary
        (Bd.act (Γ := 1) σ.1 Φ β)
  := by
  have h := Environment.interpretBoundary_subst _ (c.lift (onSub M (Quotient.mk _ σ))) _ _ hB
  rw [← Environment.extend_subst, ← envOf_substitution, Environment.extend_rename,
    ← Environment.interpretBoundary_rename] at h
  have h' := Environment.interpretBoundary_fill
    ((Environment.Filling.ofSection _ _ _ _ (sectionOf_mem σ)).extend
      (D.subst (onSub M (Quotient.mk _ σ)))) _ _ h
  rw [Bd.apply, Bd.act_lift_depth] at h'
  erw [Bd.act_copair_prefix, Bd.act_weaken] at h'
  apply h'

/-- An interpretation of an expression at the environment of `Y` extended by a decoration
`D`, reindexed along the lift through the chain of `D` of the substitution a filling `σ`
from `X` to `Y` presents, is an interpretation of the expression acted on by `σ` at the
environment of `X` extended by `D` reindexed along that substitution. -/
theorem interpret_act
    {X Y : Ctx.Ob} (σ : Ctx.Ob.Subst X Y) {Φ : C.Arity} {c : Chain M (onOb M Y) Φ}
    {D : Decoration M c} {g : Expr (Y.arity ⋈ Φ)} (v : Filler M c.last)
    (hv : v ∈ ((envOf M Y).extend D).interpret g) :
  v.subst (c.lift (onSub M (Quotient.mk _ σ)))
    ∈ ((envOf M X).extend (D.subst (onSub M (Quotient.mk _ σ)))).interpret
        (Subst.act (Γ := 1) σ.1 Φ g)
  := by
  have h := Environment.interpret_subst _ (c.lift (onSub M (Quotient.mk _ σ))) _ _ hv
  rw [← Environment.extend_subst, ← envOf_substitution, Environment.extend_rename,
    ← Environment.interpret_rename] at h
  have h' := Environment.interpret_fill Y.arity
    ((Environment.Filling.ofSection _ _ _ _ (sectionOf_mem σ)).extend
      (D.subst (onSub M (Quotient.mk _ σ)))) _ _ h
  rw [Subst.apply, Subst.act_lift_depth] at h'
  erw [act_copair_prefix, Subst.act_weaken] at h'
  apply h'

/-- An interpretation of a filling `τ` along `d` from `g` at the environment of `Y`,
reindexed along the substitution a filling `σ` from `X` to `Y` presents, is an
interpretation at the environment of `X` of `τ` with `σ` substituted in every filler, from
`g` reindexed along that substitution. -/
theorem interpretFilling_applyEach
    {X Y : Ctx.Ob} (σ : Ctx.Ob.Subst X Y) {Λ : C.Arity} {τ : Subst Λ Y.arity} {Z : M.Ob}
    {c : Chain M Z Λ} {d : Decoration M c} {g : M.Sub (onOb M Y) Z}
    {s : M.Sub (onOb M Y) c.last} (hs : s ∈ (envOf M Y).interpretFilling τ d g) :
  M.comp s (onSub M (Quotient.mk _ σ))
    ∈ (envOf M X).interpretFilling (Subst.applyEach σ.1 τ) d
        (M.comp g (onSub M (Quotient.mk _ σ)))
  := by
  have h := Environment.interpretFilling_subst _ (onSub M (Quotient.mk _ σ)) _ _ _ _ hs
  rw [← envOf_substitution, ← Environment.interpretFilling_rename] at h
  convert Environment.interpretFilling_fill
    (Environment.Filling.ofSection _ _ _ _ (sectionOf_mem σ)) _ _ _ _ h using 2
  funext Ω i
  symm
  apply Eq.trans (act_copair_prefix σ.1 Ω _)
  apply Subst.act_weaken

/-- A pairing of `fillers` along `d.append d'` from `g` is heterogeneously equal to a
pairing along `d'` of the fillers of the slots of `d'`, from a pairing along `d` from `g`
of the fillers of the slots of `d`. -/
theorem Environment.pairFillers_append
    {Γ : M.Ob} {Δ : C.Arity} (E : Environment M Γ Δ) :
    ∀ {Y : M.Ob} {Φ Λ : C.Arity} {c : Chain M Y Φ} {d : Decoration M c}
      {c' : Chain M c.last Λ} {d' : Decoration M c'} {g : M.Sub Γ Y}
      {fillers : ∀ ⦃Ω : C.Arity⦄, (Φ ⋈ Λ) ∋ Ω → ∀ {Z : M.Ob}, Environment M Z (Δ ⋈ Ω) →
        Part (Filler M Z)}
      {p : M.Sub Γ (c.append c').last}, p ∈ E.pairFillers (d.append d') g fillers →
      ∃ s ∈ E.pairFillers d g (fun _ i _ E' => fillers (C.inl i) E'),
        ∃ p' ∈ E.pairFillers d' s (fun _ j _ E' => fillers (C.inr j) E'), HEq p p'
  | _, _, _, _, .nil, _, _, g, _, p, hp => by
      simp only [C.unit_left]
      use g, Part.mem_some g, p, hp
      apply HEq.rfl
  | _, _, _, _, .cons _ _ _ _ _, _, _, _, _, _, hp => by
      obtain ⟨t, ht, hp'⟩ := Part.mem_bind_iff.mp hp
      obtain ⟨s, hs, p', hp'', hpp'⟩ := pairFillers_append E hp'
      simp only [C.inl_inl, C.inr_inl, C.inr_inr] at ht hs hp''
      use s, Part.mem_bind_iff.mpr ⟨t, ht, hs⟩, p', hp'', hpp'

/-! ### Reindexing -/

/-- An entry reindexed along a filling `σ` is interpreted as the interpreted entry
reindexed along the substitution `σ` presents: its telescope along that substitution, its
boundary along the lift of that substitution through the chain of the telescope. -/
theorem entryOf_subst {X Y : Ctx.Ob} (e : Ctx.Ob.Entry Y) (σ : Ctx.Ob.Subst X Y) :
  entryOf M (e.subst σ)
    = ⟨(entryOf M e).1.subst (onSub M (Quotient.mk _ σ)),
        (entryOf M e).2.subst ((entryOf M e).1.chain.lift (onSub M (Quotient.mk _ σ)))⟩
  := by
  apply Part.get_eq_of_mem
  apply (Environment.mem_interpretEntry _ _ _ _).mpr
  obtain ⟨hT, hB⟩ := entryOf_mem e
  constructor
  · apply interpretTelescope_actBase σ hT
  · apply interpretBoundary_act σ hB

/-- Reindexing a type class along a morphism of context classes is reindexing the type it
presents along the substitution the morphism presents. -/
theorem onTy_substTy {X Y : Ctx.Ob} (a : Ctx.Ty₁ Y) (f : X ⟶ Y) :
  onTy M (a.subst f) = M.substTy (onTy M a) (onSub M f)
  := by
  induction a, f using Quotient.ind₂ with
  | _ e σ =>
      apply Eq.trans (onTy_mk _)
      rw [entryOf_subst, onTy_mk]
      symm
      apply Chain.Bind_subst_entry rfl

/-- Reindexing a term class along a morphism of context classes is reindexing the term it
presents along the substitution the morphism presents. -/
theorem onTm_substTm {X Y : Ctx.Ob} {a : Ctx.Ty₁ Y} (t : Ctx.Tm₁ Y a) (f : X ⟶ Y) :
  HEq (onTm M (t.subst f)) (M.substTm (onTm M t) (onSub M f))
  := by
  induction a, f using Quotient.ind₂ with
  | _ e σ =>
      induction t using Ctx.Tm₁.ind with
      | ofFill τ =>
          have ht := Chain.entryTerm_subst _ (onSub M (Quotient.mk _ σ)) _ _ _
            (interpret_act σ) (termOf_mem τ)
          have hentry := entryOf_subst (M := M) e σ
          obtain ⟨z, hz, hyz⟩ := Chain.entryTerm_congr (congrArg (fun q => q.1.chain) hentry)
            (congr_arg_heq Sigma.snd hentry)
            (congr_arg_heq (fun q => ((envOf M X).extend q.1.decoration).interpret _) hentry)
            (termOf_mem (e := e.subst σ)
              ⟨Subst.applyEach σ.1 τ.1, Ctx.Ob.Fill.Wf.subst σ ⟨e.toTele, τ⟩⟩)
          rw [Part.mem_unique hz ht] at hyz
          apply HEq.trans hyz
          apply eqRec_heq

/-! ### Identities and composites -/

/-- The identity of a context class presents the identity. -/
theorem onSub_identity (X : Ctx.Ob) :
  onSub M (𝟙 X) = M.identity (onOb M X)
  := by
  induction X using Quotient.ind with
  | _ Γ =>
      apply Part.mem_unique (onSub_mem _)
      rw [← M.toEmpty_unique (M.comp (telescopeOf M _).chain.projection (M.identity (onOb M _)))]
      apply Environment.interpretFilling_ofRenaming _ _ _ (𝟙ʳ Γ.arity)
      · intro _ i
        erw [Value.subst_identity]
        rw [← Environment.extend_inr (Environment.empty M.empty), C.unit_left]
        rfl
      · intro _ _
        apply Environment.interpret_eta

/-- A composite of morphisms of context classes presents the composite of the
substitutions they present. -/
theorem onSub_comp {X Y Z : Ctx.Ob} (g : Y ⟶ Z) (f : X ⟶ Y) :
  onSub M (f ≫ g) = M.comp (onSub M g) (onSub M f)
  := by
  induction g, f using Quotient.ind₂ with
  | _ σ θ =>
      apply Part.mem_unique (onSub_mem (Ctx.Ob.Subst.comp θ σ))
      rw [← M.toEmpty_unique (M.comp (M.toEmpty _) (onSub M (Quotient.mk _ θ)))]
      apply interpretFilling_applyEach θ (onSub_mem σ)

/-! ### Sorts, elements and their equality types -/

/-- The type of sorts over a context class presents the type of sorts. -/
theorem onTy_U (X : Ctx.Ob) :
  onTy M (Ctx.U X) = M.U (onOb M X)
  := rfl

/-- The type of elements of a sort class presents the type of elements of the sort it
presents. -/
theorem onTy_El {X : Ctx.Ob} (S : Ctx.Tm₁ X (Ctx.U X)) :
  onTy M (Ctx.El S) = M.El (onTy_U X ▸ onTm M S)
  := by
  induction S using Ctx.Tm₁.ind with
  | ofFill τ => rfl

/-- The filler of a filling of the one-entry telescope declaring a sort is interpreted as
the sort the filling gives. -/
theorem termOf_sort {X : Ctx.Ob} (τ : Ctx.Ob.Fill X (Ctx.Ob.Entry.sort X).toTele) :
  Filler.mk .sort (termOf M τ) ∈ ((envOf M X).extend .nil).interpret τ.filler
  := by
  obtain ⟨s, hs, hτ⟩ := (Chain.mem_entryTerm_sort _ _).mp (termOf_mem τ)
  rw [hτ]
  apply hs

/-- The filler of a filling `ρ` of the one-entry telescope declaring an element of the sort
a filling `τ` gives is interpreted as the element of that sort `ρ` gives. -/
theorem termOf_of
    {X : Ctx.Ob} {τ : Ctx.Ob.Fill X (Ctx.Ob.Entry.sort X).toTele}
    (ρ : Ctx.Ob.Fill X (Ctx.Ob.Entry.of τ).toTele) :
  Filler.mk (.of (termOf M τ)) (termOf M ρ) ∈ ((envOf M X).extend .nil).interpret ρ.filler
  := by
  obtain ⟨u, hu, hρ⟩ := (Chain.mem_entryTerm_of _ _ _).mp (termOf_mem ρ)
  rw [hρ]
  apply hu

/-- The type asserting that two sort classes are equal presents the type asserting that the
sorts they present are equal. -/
theorem onTy_IdSort {X : Ctx.Ob} (S S' : Ctx.Tm₁ X (Ctx.U X)) :
  onTy M (Ctx.IdSort S S') = M.IdSort (onTy_U X ▸ onTm M S) (onTy_U X ▸ onTm M S')
  := by
  induction S using Ctx.Tm₁.ind with
  | ofFill τ =>
      induction S' using Ctx.Tm₁.ind with
      | ofFill τ' =>
          apply Eq.trans (onTy_mk (Ctx.Ob.Entry.id (β := Bd.sort) not_false τ τ'))
          obtain ⟨-, hB⟩ := entryOf_mem (M := M) (Ctx.Ob.Entry.id (β := Bd.sort) not_false τ τ')
          rcases (Environment.mem_interpretBoundary_eq _ _ _ _).mp hB with
            ⟨_, _, hl, hr, hBe⟩ | ⟨_, _, _, hl, -, -⟩
          · cases Part.mem_unique hl (termOf_sort τ)
            cases Part.mem_unique hr (termOf_sort τ')
            rw [hBe]
            rfl
          · cases Part.mem_unique hl (termOf_sort τ)

/-- Reflexivity of a sort class presents reflexivity of the sort it presents. -/
theorem onTm_IdSort_refl {X : Ctx.Ob} (S : Ctx.Tm₁ X (Ctx.U X)) :
  HEq (onTm M (Ctx.IdSort_refl S)) (M.IdSort_refl (onTy_U X ▸ onTm M S))
  := by
  apply heq_of_cast_eq (congrArg _ (onTy_IdSort S S))
  apply M.IdSort_irrelevant

/-- The type asserting that two element classes of a sort class are equal presents the type
asserting that the elements they present are equal. -/
theorem onTy_IdElement {X : Ctx.Ob} {S : Ctx.Tm₁ X (Ctx.U X)} (l r : Ctx.Tm₁ X (Ctx.El S)) :
  HEq (onTy M (Ctx.IdElement l r))
    (M.IdElement (onTy_El S ▸ onTm M l) (onTy_El S ▸ onTm M r))
  := by
  induction S using Ctx.Tm₁.ind with
  | ofFill τ =>
      induction l using Ctx.Tm₁.ind with
      | ofFill ρ =>
          induction r using Ctx.Tm₁.ind with
          | ofFill ν =>
              apply heq_of_eq
              apply Eq.trans (onTy_mk (Ctx.Ob.Entry.id (β := Bd.of τ.filler) not_false ρ ν))
              obtain ⟨-, hB⟩ :=
                entryOf_mem (M := M) (Ctx.Ob.Entry.id (β := Bd.of τ.filler) not_false ρ ν)
              rcases (Environment.mem_interpretBoundary_eq _ _ _ _).mp hB with
                ⟨_, _, hl, -, -⟩ | ⟨_, _, _, hl, hr, hBe⟩
              · cases Part.mem_unique hl (termOf_of ρ)
              · cases Part.mem_unique hl (termOf_of ρ)
                cases Part.mem_unique hr (termOf_of ν)
                rw [hBe]
                rfl

/-- Reflexivity of an element class presents reflexivity of the element it presents. -/
theorem onTm_IdElement_refl {X : Ctx.Ob} {S : Ctx.Tm₁ X (Ctx.U X)} (t : Ctx.Tm₁ X (Ctx.El S)) :
  HEq (onTm M (Ctx.IdElement_refl t)) (M.IdElement_refl (onTy_El S ▸ onTm M t))
  := by
  apply heq_of_cast_eq (congrArg _ (eq_of_heq (onTy_IdElement t t)))
  apply M.IdElement_irrelevant

/-! ### Extension -/

/-- Pairing a morphism of context classes with a term class presents pairing the
substitution the morphism presents with the term the term class presents. -/
theorem onSub_pair {X Y : Ctx.Ob} {a : Ctx.Ty₁ Y} (f : X ⟶ Y) (t : Ctx.Tm₁ X (a.subst f)) :
  HEq (onSub M (Ctx.Ty₁.pair f t)) (M.pair (onSub M f) (onTy_substTy a f ▸ onTm M t))
  := by
  induction Y using Quotient.ind with
  | _ Γ =>
      induction a, f using Quotient.ind₂ with
      | _ e σ =>
          induction t using Ctx.Tm₁.ind with
          | ofFill τ =>
              obtain ⟨κ, hκ, hκσ⟩ : ∃ κ, Ctx.Ty₁.pair (a := Quotient.mk _ e) (Quotient.mk _ σ)
                  (Ctx.Tm₁.ofFill τ) = Quotient.mk _ κ ∧ κ.1 = Subst.copair σ.1 τ.1 :=
                ⟨_, rfl, rfl⟩
              have hmem := onSub_mem (M := M) κ
              rw [hκσ] at hmem
              rw [hκ]
              generalize onSub M (Quotient.mk _ κ) = p at hmem ⊢
              revert p
              dsimp only [onOb]
              rw [telescopeOf_extend]
              intro p hp
              obtain ⟨s, hs, p', hp', hpp'⟩ := Environment.pairFillers_append _ hp
              simp only [Ctx.Ob.Tele.arity, Ctx.Ob.Entry.toTele, Ctx.Ob.Entry.subst,
                Subst.copair_inl, Subst.copair_inr] at hs hp'
              obtain rfl := Part.mem_unique hs (onSub_mem σ)
              apply HEq.trans hpp'
              obtain ⟨t', ht', hp''⟩ :=
                (Environment.mem_interpretFilling_cons _ _ _ _ _ _ _ _ _).mp hp'
              obtain rfl := (Environment.mem_interpretFilling_nil _ _ _ _).mp hp''
              congr 1
              apply eq_of_heq
              apply HEq.trans (eqRec_heq _ _)
              symm
              apply HEq.trans (eqRec_heq _ _)
              have hentry := entryOf_subst (M := M) e σ
              obtain ⟨z, hz, hyz⟩ := Chain.entryTerm_congr (congrArg (fun q => q.1.chain) hentry)
                (congr_arg_heq Sigma.snd hentry)
                (congr_arg_heq (fun q => ((envOf M X).extend q.1.decoration).interpret _) hentry)
                (termOf_mem τ)
              rw [Part.mem_unique hz ht'] at hyz
              apply hyz

/-- The projection off the extension of a context class by a type class presents the
projection off the extension by the type it presents. -/
theorem onSub_projection {X : Ctx.Ob} (a : Ctx.Ty₁ X) :
  HEq (onSub M (Ctx.Ob.projection X a.toTy)) (M.projection (onTy M a))
  := by
  have hpair := onSub_pair (M := M) (Ctx.Ob.projection X a.toTy) (Ctx.Tm₁.generic a)
  rw [Ctx.Ty₁.pair_eta, onSub_identity] at hpair
  rw [← M.projection_pair (onSub M (Ctx.Ob.projection X a.toTy))
    (onTy_substTy a _ ▸ onTm M (Ctx.Tm₁.generic a))]
  apply HEq.trans (b := M.comp (M.projection (onTy M a)) (M.identity _))
  · congr 1
    · apply onOb_extend
    · apply HEq.trans (HEq.symm hpair)
      rw [onOb_extend]
  · rw [M.comp_identity]

/-- The generic term of a type class presents the generic term of the type it
presents. -/
theorem onTm_generic {X : Ctx.Ob} (a : Ctx.Ty₁ X) :
  HEq (onTm M (Ctx.Tm₁.generic a)) (M.generic (onTy M a))
  := by
  have hpair := onSub_pair (M := M) (Ctx.Ob.projection X a.toTy) (Ctx.Tm₁.generic a)
  rw [Ctx.Ty₁.pair_eta, onSub_identity] at hpair
  apply HEq.trans (HEq.symm (eqRec_heq (onTy_substTy a _) _))
  apply HEq.trans (HEq.symm (M.generic_pair _ _))
  apply HEq.trans (b := M.substTm (M.generic (onTy M a)) (M.identity _))
  · congr 1
    · apply onOb_extend
    · apply HEq.trans (HEq.symm hpair)
      rw [onOb_extend]
  · apply M.substTm_identity_heq _ rfl

/-! ### Binding -/

/-- The terms the entry with binding chain `cons A c` and boundary `B` is given by `w` are
`lam` of the terms the entry with binding chain `c` and boundary `B` is given by `w`. -/
theorem Chain.entryTerm_cons
    {Γ : M.Ob} {α Ω : C.Arity} (A : M.Ty Γ) (c : Chain M (M.extend Γ A) Ω)
    (B : Boundary M c.last) (w : Part (Filler M c.last)) :
  (cons (α := α) A c).entryTerm B w = (c.entryTerm B w).map M.lam
  := by
  cases B <;> rfl

/-- An entry `f` over the extension of the class of `Γ` by the class of an entry `e` has an
interpretation `p` at the environment of `Γ` extended by the one-entry decoration of the
interpreted `e` such that the type the class of `f` presents is heterogeneously equal to
`Bind` of the chain of `p` at the type of the boundary of `p`. -/
theorem entryOf_extend
    {Γ : Ctx} {e : Ctx.Ob.Entry (Quotient.mk _ Γ)}
    (f : Ctx.Ob.Entry (Ctx.Ob.extend (Quotient.mk _ Γ) (Ctx.Ty₁.toTy (Quotient.mk _ e)))) :
  ∃ p ∈ ((envOf M (Quotient.mk _ Γ)).extend
      (Decoration.cons (entryOf M e).1.decoration (entryOf M e).2 (onTy M (Quotient.mk _ e)) rfl
        .nil)).interpretEntry f.binding f.declaration,
    HEq (onTy M (Quotient.mk _ f)) (p.1.chain.Bind p.2.ty)
  := by
  have hq : entryOf M f ∈ (envOf M _).interpretEntry f.binding f.declaration := Part.get_mem _
  have hE := envOf_extend (M := M) Γ e
  rw [onTy_mk f]
  generalize entryOf M f = q at hq ⊢
  generalize envOf M (Ctx.Ob.extend (Quotient.mk _ Γ) (Ctx.Ty₁.toTy (Quotient.mk _ e))) = E
    at hE hq
  revert q E
  rw [onOb_extend]
  intro q E hE hq
  obtain rfl := eq_of_heq hE
  use q, hq
  apply HEq.rfl

/-- For an interpretation `p` of an entry `f` over the extension of the class of `Γ` by the
class of an entry `e`, at the environment of `Γ` extended by the one-entry decoration of the
interpreted `e`, the term a filling `τ` of the one-entry telescope of `f` gives is
heterogeneously equal to a term `p` is given by the interpretation of the filler of `τ` at
that environment extended by the decoration of `p`. -/
theorem termOf_extend
    {Γ : Ctx} {e : Ctx.Ob.Entry (Quotient.mk _ Γ)}
    {f : Ctx.Ob.Entry (Ctx.Ob.extend (Quotient.mk _ Γ) (Ctx.Ty₁.toTy (Quotient.mk _ e)))}
    (τ : Ctx.Ob.Fill (Ctx.Ob.extend (Quotient.mk _ Γ) (Ctx.Ty₁.toTy (Quotient.mk _ e)))
      f.toTele)
    {p} (hp : p ∈ ((envOf M (Quotient.mk _ Γ)).extend
      (Decoration.cons (entryOf M e).1.decoration (entryOf M e).2 (onTy M (Quotient.mk _ e)) rfl
        .nil)).interpretEntry f.binding f.declaration) :
  ∃ u ∈ p.1.chain.entryTerm p.2
      ((((envOf M (Quotient.mk _ Γ)).extend
        (Decoration.cons (entryOf M e).1.decoration (entryOf M e).2 (onTy M (Quotient.mk _ e))
          rfl .nil)).extend p.1.decoration).interpret τ.filler),
    HEq (termOf M τ) u
  := by
  have hq : entryOf M f ∈ (envOf M _).interpretEntry f.binding f.declaration := Part.get_mem _
  have hy := termOf_mem (M := M) τ
  have hE := envOf_extend (M := M) Γ e
  generalize termOf M τ = y at hy ⊢
  generalize entryOf M f = q at y hy hq ⊢
  generalize envOf M (Ctx.Ob.extend (Quotient.mk _ Γ) (Ctx.Ty₁.toTy (Quotient.mk _ e))) = E
    at hE hq hy
  revert q y E
  rw [onOb_extend]
  intro q y E hE hq hy
  obtain rfl := eq_of_heq hE
  obtain rfl := Part.mem_unique hq hp
  use y, hy
  apply HEq.rfl

/-- For an interpretation `p` of an entry `f` at the environment of `Γ` extended by the
one-entry decoration of the interpreted `e`, the entry `Ctx.bind Γ e f` is interpreted as
the one-entry telescope of the interpreted `e` followed by the telescope of `p`, with the
boundary of `p`. -/
theorem entryOf_bind
    {Γ : Ctx} {e : Ctx.Ob.Entry (Quotient.mk _ Γ)}
    {f : Ctx.Ob.Entry (Ctx.Ob.extend (Quotient.mk _ Γ) (Ctx.Ty₁.toTy (Quotient.mk _ e)))}
    {p} (hp : p ∈ ((envOf M (Quotient.mk _ Γ)).extend
      (Decoration.cons (entryOf M e).1.decoration (entryOf M e).2 (onTy M (Quotient.mk _ e)) rfl
        .nil)).interpretEntry f.binding f.declaration) :
  entryOf M (Ctx.bind Γ e f)
    = ⟨⟨.cons (onTy M (Quotient.mk _ e)) p.1.chain,
        .cons (entryOf M e).1.decoration (entryOf M e).2 _ rfl p.1.decoration⟩, p.2⟩
  := by
  obtain ⟨hT, hB⟩ := (Environment.mem_interpretEntry _ _ _ _).mp hp
  apply Part.get_eq_of_mem
  apply (Environment.mem_interpretEntry _ _ _ _).mpr
  constructor
  · apply (Environment.mem_interpretTelescope_cons _ _ _ _ _).mpr
    use (entryOf M e).1, (entryOf_mem e).1, (entryOf M e).2, (entryOf_mem e).2,
      onTy M (Quotient.mk _ e), rfl, p.1, hT
    rfl
  · erw [Environment.extend_cons]
    apply hB

/-- `Bind` of a type class `a` and a type class `c` over the extension by `a` presents `Bind`
of the type `a` presents and any type `c'` heterogeneously equal to the type `c` presents. -/
theorem onTy_Bind
    {X : Ctx.Ob} (a : Ctx.Ty₁ X) (c : Ctx.Ty₁ (Ctx.Ob.extend X a.toTy))
    (c' : M.Ty (M.extend (onOb M X) (onTy M a))) (hc : HEq (onTy M c) c') :
  onTy M (Ctx.Bind a c) = M.Bind (onTy M a) c'
  := by
  induction X using Quotient.ind with
  | _ Γ =>
      induction a using Quotient.ind with
      | _ e =>
          induction c using Quotient.ind with
          | _ f =>
              obtain ⟨p, hp, hfp⟩ := entryOf_extend f
              apply Eq.trans (onTy_mk (Ctx.bind Γ e f))
              rw [entryOf_bind hp]
              obtain rfl := eq_of_heq (HEq.trans (HEq.symm hfp) hc)
              rfl

/-- `lam` of a term class `t` over the extension by a type class presents `lam` of any term
`t'` heterogeneously equal to the term `t` presents. -/
theorem onTm_lam
    {X : Ctx.Ob} {a : Ctx.Ty₁ X} {c : Ctx.Ty₁ (Ctx.Ob.extend X a.toTy)}
    (t : Ctx.Tm₁ (Ctx.Ob.extend X a.toTy) c) (c' : M.Ty (M.extend (onOb M X) (onTy M a)))
    (t' : M.Tm (M.extend (onOb M X) (onTy M a)) c') (hc : HEq (onTy M c) c')
    (ht : HEq (onTm M t) t') :
  HEq (onTm M (Ctx.lam t)) (M.lam t')
  := by
  induction X using Quotient.ind with
  | _ Γ =>
      induction a using Quotient.ind with
      | _ e =>
          induction c using Quotient.ind with
          | _ f =>
              induction t using Ctx.Tm₁.ind with
              | ofFill τ =>
                  obtain ⟨p, hp, hfp⟩ := entryOf_extend f
                  obtain ⟨u, hu, hτu⟩ := termOf_extend τ hp
                  obtain rfl := eq_of_heq (HEq.trans (HEq.symm hfp) hc)
                  obtain rfl := eq_of_heq (HEq.trans (HEq.symm hτu) ht)
                  have hbind := entryOf_bind hp
                  obtain ⟨z, hz, hyz⟩ := Chain.entryTerm_congr
                    (congrArg (fun q => q.1.chain) hbind) (congr_arg_heq Sigma.snd hbind)
                    (congr_arg_heq (fun q => ((envOf M (Quotient.mk _ Γ)).extend
                      q.1.decoration).interpret _) hbind)
                    (termOf_mem (Ctx.lamFill Γ e f τ))
                  erw [Chain.entryTerm_cons] at hz
                  obtain ⟨u', hu', rfl⟩ := (Part.mem_map_iff _).mp hz
                  erw [Environment.extend_cons] at hu'
                  obtain rfl := Part.mem_unique hu' hu
                  apply hyz

/-! ### The morphism -/

variable (M) in
/-- The morphism from the model on context classes to `M`, sending each context class,
substitution class, type class and term class to what it presents. -/
def initialMorphism : Morphism Ctx.model M where
  onOb := onOb M
  onSub := onSub M
  onTy := onTy M
  onTm := onTm M
  onSub_identity := onSub_identity
  onSub_comp := onSub_comp
  onOb_empty := rfl
  onTy_substTy := onTy_substTy
  onTm_substTm := onTm_substTm
  onOb_extend := onOb_extend
  onSub_projection := onSub_projection
  onTm_generic := onTm_generic
  onSub_pair := onSub_pair
  onTy_U := onTy_U
  onTy_El := onTy_El
  onTy_Bind := onTy_Bind
  onTm_lam := onTm_lam
  onTy_IdSort := onTy_IdSort
  onTm_IdSort_refl := onTm_IdSort_refl
  onTy_IdElement := onTy_IdElement
  onTm_IdElement_refl := onTm_IdElement_refl

end HrS
