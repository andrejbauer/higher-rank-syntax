import HigherRankSyntax.Initiality.Descent
import HigherRankSyntax.HrS.Morphism

/-!
# The morphism from the model on context classes

The maps `onOb`, `onSub`, `onTy`, `onTm` commute with the operations of the models,
so they form a morphism from `Ctx.model` to `M`.

The substitution the class of a filling from `X` to `Y` presents is the interpretation
of the filling at the environment of `X`, along the decoration of the interpretation of
the ambient of `Y`, from the substitution into the empty object. Along it, the
interpretations over `Y` become the interpretations over `X` of the syntax with the
filling substituted.
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
  have h := Environment.pairFillers_comp (envOf M X) (telescopeOf M Y).decoration
    (M.toEmpty (onOb M X)) (M.identity (onOb M X)) (fun _ i _ E' => E'.interpret (σ.1 i))
  rw [M.comp_identity] at h
  rw [Environment.interpretFilling, h, onSub_mk]
  apply Part.mem_map
  apply sectionOf_mem

/-- Along the substitution a filling `σ` from `X` to `Y` presents, an interpretation of a
telescope over `Y` becomes an interpretation of the telescope with `σ` substituted in its
base. -/
theorem interpretTelescope_actBase
    {X Y : Ctx.Ob} (σ : Ctx.Ob.Subst X Y) {Ω : C.Arity} (Θ : dTel Y.arity Ω)
    (T : Telescope M (onOb M Y) Ω) (hT : T ∈ (envOf M Y).interpretTelescope Θ) :
  T.subst (onSub M (Quotient.mk _ σ)) ∈ (envOf M X).interpretTelescope (dTel.actBase σ.1 Θ)
  := by
  have h := Environment.interpretTelescope_subst _ (onSub M (Quotient.mk _ σ)) Θ T hT
  rw [← envOf_substitution, ← Environment.interpretTelescope_rename] at h
  have h' := Environment.interpretTelescope_fill
    (Environment.Filling.ofSection _ _ _ _ (sectionOf_mem σ)) _ _ h
  rw [← dTel.instantiate_weaken]
  apply h'

/-- Along the substitution a filling `σ` from `X` to `Y` presents, lifted through a chain,
an interpretation of a boundary over `Y` extended by the chain becomes an interpretation
of the boundary acted on by `σ`, over `X` extended by the reindexed chain. -/
theorem interpretBoundary_act
    {X Y : Ctx.Ob} (σ : Ctx.Ob.Subst X Y) {Φ : C.Arity} {c : Chain M (onOb M Y) Φ}
    (D : Decoration M c) (β : Bd (Y.arity ⋈ Φ)) (B : Boundary M c.last)
    (hB : B ∈ ((envOf M Y).extend D).interpretBoundary β) :
  B.subst (c.lift (onSub M (Quotient.mk _ σ)))
    ∈ ((envOf M X).extend (D.subst (onSub M (Quotient.mk _ σ)))).interpretBoundary
        (Bd.act (Γ := 1) σ.1 Φ β)
  := by
  have h := Environment.interpretBoundary_subst _ (c.lift (onSub M (Quotient.mk _ σ))) β B hB
  rw [← Environment.extend_subst, ← envOf_substitution, Environment.extend_rename,
    ← Environment.interpretBoundary_rename] at h
  have h' := Environment.interpretBoundary_fill
    ((Environment.Filling.ofSection _ _ _ _ (sectionOf_mem σ)).extend
      (D.subst (onSub M (Quotient.mk _ σ)))) _ _ h
  rw [Bd.apply, Bd.act_lift_depth] at h'
  erw [Bd.act_copair_prefix] at h'
  rw [Bd.act_weaken] at h'
  apply h'

/-- Along the substitution a filling `σ` from `X` to `Y` presents, lifted through a chain,
an interpretation of an expression over `Y` extended by the chain becomes an
interpretation of the expression acted on by `σ`, over `X` extended by the reindexed
chain. -/
theorem interpret_act
    {X Y : Ctx.Ob} (σ : Ctx.Ob.Subst X Y) {Φ : C.Arity} {c : Chain M (onOb M Y) Φ}
    (D : Decoration M c) (g : Expr (Y.arity ⋈ Φ)) (v : Filler M c.last)
    (hv : v ∈ ((envOf M Y).extend D).interpret g) :
  v.subst (c.lift (onSub M (Quotient.mk _ σ)))
    ∈ ((envOf M X).extend (D.subst (onSub M (Quotient.mk _ σ)))).interpret
        (Subst.act (Γ := 1) σ.1 Φ g)
  := by
  have h := Environment.interpret_subst _ (c.lift (onSub M (Quotient.mk _ σ))) g v hv
  rw [← Environment.extend_subst, ← envOf_substitution, Environment.extend_rename,
    ← Environment.interpret_rename] at h
  have h' := Environment.interpret_fill Y.arity
    ((Environment.Filling.ofSection _ _ _ _ (sectionOf_mem σ)).extend
      (D.subst (onSub M (Quotient.mk _ σ)))) _ _ h
  rw [Subst.apply, Subst.act_lift_depth] at h'
  erw [act_copair_prefix] at h'
  rw [Subst.act_weaken] at h'
  apply h'

/-- Along the substitution a filling `σ` from `X` to `Y` presents, an interpretation of a
filling at the environment of `Y` becomes, followed by that substitution, an
interpretation at the environment of `X` of the filling with `σ` substituted in every
filler. -/
theorem interpretFilling_applyEach
    {X Y : Ctx.Ob} (σ : Ctx.Ob.Subst X Y) {Λ : C.Arity} (τ : Subst Λ Y.arity) {Y' : M.Ob}
    {c : Chain M Y' Λ} (d : Decoration M c) (g : M.Sub (onOb M Y) Y')
    (s : M.Sub (onOb M Y) c.last) (hs : s ∈ (envOf M Y).interpretFilling τ d g) :
  M.comp s (onSub M (Quotient.mk _ σ))
    ∈ (envOf M X).interpretFilling (Subst.applyEach σ.1 τ) d
        (M.comp g (onSub M (Quotient.mk _ σ)))
  := by
  have h := Environment.interpretFilling_subst _ (onSub M (Quotient.mk _ σ)) τ d g s hs
  rw [← envOf_substitution, ← Environment.interpretFilling_rename] at h
  have h' := Environment.interpretFilling_fill
    (Environment.Filling.ofSection _ _ _ _ (sectionOf_mem σ)) _ d _ _ h
  have hfill : Subst.applyEach (Subst.copair (Subst.id X.arity) σ.1)
      (fun ⦃Λ'⦄ i => ⟦Renaming.inr X.arity Y.arity ⇑ʳ Λ'⟧ʳ (τ i)) = Subst.applyEach σ.1 τ := by
    funext Λ' i
    apply Eq.trans (act_copair_prefix σ.1 Λ' _)
    apply Subst.act_weaken
  rw [hfill] at h'
  apply h'

/-- Pairing fillers along an appended decoration pairs them along the first decoration,
and then along the second from the substitution so obtained. The two results lie over
the end of the appended chain and over the end of the second chain. -/
theorem Environment.pairFillers_append
    {Γ : M.Ob} {Δ : C.Arity} (E : Environment M Γ Δ) :
    ∀ {Y : M.Ob} {Φ Λ : C.Arity} {c : Chain M Y Φ} (d : Decoration M c)
      {c' : Chain M c.last Λ} (d' : Decoration M c') (g : M.Sub Γ Y)
      (fillers : ∀ ⦃Ω : C.Arity⦄, (Φ ⋈ Λ) ∋ Ω → ∀ {Z : M.Ob}, Environment M Z (Δ ⋈ Ω) →
        Part (Filler M Z))
      (p : M.Sub Γ (c.append c').last), p ∈ E.pairFillers (d.append d') g fillers →
      ∃ s ∈ E.pairFillers d g (fun _ i _ E' => fillers (C.inl i) E'),
        ∃ p' ∈ E.pairFillers d' s (fun _ j _ E' => fillers (C.inr j) E'), HEq p p'
  | _, _, Λ, _, .nil, _, d', g, fillers, p, hp => by
      use g, Part.mem_some g, p
      constructor
      · convert hp using 2
        funext Ω j Z E'
        rw [C.unit_left]
      · rfl
  | _, _, _, _, @Decoration.cons _ _ α Φ₀ b db B A hA c d, _, d', g, fillers, p, hp => by
      obtain ⟨t, ht, hp'⟩ := Part.mem_bind_iff.mp hp
      obtain ⟨s, hs, p', hp'', hpp'⟩ := pairFillers_append E d d' _ _ _ hp'
      use s
      constructor
      · apply Part.mem_bind_iff.mpr
        use t
        constructor
        · rw [C.inl_inl] at ht
          apply ht
        · simp only [C.inr_inl] at hs
          apply hs
      · use p'
        constructor
        · simp only [C.inr_inr] at hp''
          apply hp''
        · apply hpp'

/-! ### Reindexing -/

/-- A reindexed entry is interpreted as the interpreted entry reindexed along the
substitution the filling presents. -/
theorem entryOf_subst {X Y : Ctx.Ob} (e : Ctx.Ob.Entry Y) (σ : Ctx.Ob.Subst X Y) :
  entryOf M (e.subst σ) = ⟨(entryOf M e).1.subst (onSub M (Quotient.mk _ σ)),
    (entryOf M e).2.subst ((entryOf M e).1.chain.lift (onSub M (Quotient.mk _ σ)))⟩
  := by
  apply Part.get_eq_of_mem
  apply (Environment.mem_interpretEntry _ _ _ _).mpr
  obtain ⟨hT, hB⟩ := entryOf_mem (M := M) e
  constructor
  · apply interpretTelescope_actBase σ _ _ hT
  · apply interpretBoundary_act σ _ _ _ hB

/-- Reindexing a type class along a morphism of context classes is reindexing the type it
presents along the substitution the morphism presents. -/
theorem onTy_substTy {X Y : Ctx.Ob} (a : Ctx.Ty₁ Y) (f : X ⟶ Y) :
  onTy M (a.subst f) = M.substTy (onTy M a) (onSub M f)
  := by
  induction a using Quotient.ind with
  | _ e =>
      induction f using Quotient.ind with
      | _ σ =>
          apply Eq.trans (onTy_mk (M := M) (e.subst σ))
          rw [entryOf_subst, onTy_mk]
          symm
          apply Chain.Bind_subst_entry rfl

/-- Reindexing a term class along a morphism of context classes is reindexing the term it
presents along the substitution the morphism presents. -/
theorem onTm_substTm {X Y : Ctx.Ob} {a : Ctx.Ty₁ Y} (t : Ctx.Tm₁ Y a) (f : X ⟶ Y) :
  HEq (onTm M (t.subst f)) (M.substTm (onTm M t) (onSub M f))
  := by
  induction a using Quotient.ind with
  | _ e =>
      induction t using Ctx.Tm₁.ind with
      | ofFill τ =>
          induction f using Quotient.ind with
          | _ σ =>
              have ht := Chain.entryTerm_subst _ (onSub M (Quotient.mk _ σ)) _ _
                (((envOf M X).extend
                    ((entryOf M e).1.decoration.subst (onSub M (Quotient.mk _ σ)))).interpret
                  (Subst.act (Γ := 1) σ.1 e.arity τ.filler))
                (fun v hv => interpret_act σ _ _ v hv) (termOf_mem τ)
              let τ' : Ctx.Ob.Fill X (e.subst σ).toTele :=
                ⟨Subst.applyEach σ.1 τ.1, Ctx.Ob.Fill.Wf.subst σ ⟨e.toTele, τ⟩⟩
              have key : ∀ (p q : Σ T : Telescope M (onOb M X) e.arity, Boundary M T.chain.last),
                  p = q → ∀ (y : M.Tm (onOb M X) (p.1.chain.Bind p.2.ty))
                    (z : M.Tm (onOb M X) (q.1.chain.Bind q.2.ty)),
                  y ∈ p.1.chain.entryTerm p.2 (((envOf M X).extend p.1.decoration).interpret τ'.filler) →
                  z ∈ q.1.chain.entryTerm q.2 (((envOf M X).extend q.1.decoration).interpret τ'.filler) →
                  HEq y z := by
                rintro p _ rfl y z hy hz
                apply heq_of_eq (Part.mem_unique hy hz)
              apply HEq.trans (key _ _ (entryOf_subst e σ) _ _ (termOf_mem τ') ht)
              apply eqRec_heq

/-! ### The category and its terminal object -/

/-- The identity of a context class presents the identity. -/
theorem onSub_identity (X : Ctx.Ob) :
  onSub M (𝟙 X) = M.identity (onOb M X)
  := by
  induction X using Quotient.ind with
  | _ Γ =>
      have h := Environment.interpretFilling_ofRenaming (envOf M (Quotient.mk _ Γ))
        (telescopeOf M (Quotient.mk _ Γ)).decoration (M.identity _) (𝟙ʳ Γ.arity)
        (fun _ i => by
          have hi := Environment.extend_inr (Environment.empty M.empty)
            (telescopeOf M (Quotient.mk _ Γ)).decoration i
          rw [C.unit_left] at hi
          apply Eq.trans hi
          symm
          apply Value.subst_identity)
        (fun _ i => Environment.interpret_eta _ _)
      rw [M.toEmpty_unique (M.comp _ _)] at h
      apply Part.mem_unique (onSub_mem (Ctx.Ob.Subst.id _)) h

/-- A composite of morphisms of context classes presents the composite of the
substitutions they present. -/
theorem onSub_comp {X Y Z : Ctx.Ob} (g : Y ⟶ Z) (f : X ⟶ Y) :
  onSub M (f ≫ g) = M.comp (onSub M g) (onSub M f)
  := by
  induction g using Quotient.ind with
  | _ σ =>
      induction f using Quotient.ind with
      | _ θ =>
          have h := interpretFilling_applyEach θ σ.1 (telescopeOf M Z).decoration
            (M.toEmpty (onOb M Y)) _ (onSub_mem σ)
          rw [M.toEmpty_unique (M.comp _ _)] at h
          symm
          apply Part.mem_unique h (onSub_mem (Ctx.Ob.Subst.comp θ σ))

/-- The empty context class presents the empty object. -/
theorem onOb_empty :
  onOb M Ctx.empty.toOb = M.empty
  := rfl

/-! ### Sorts, elements and their equations -/

/-- The type of sorts over a context class presents the type of sorts. -/
theorem onTy_U (X : Ctx.Ob) :
  onTy M (Ctx.U X) = M.U (onOb M X)
  := rfl

/-- The type of elements of a sort presents the type of elements of the sort the sort
presents. -/
theorem onTy_El {X : Ctx.Ob} (S : Ctx.Tm₁ X (Ctx.U X)) :
  onTy M (Ctx.El S) = M.El (onTy_U X ▸ onTm M S)
  := by
  induction S using Ctx.Tm₁.ind with
  | ofFill τ => rfl

/-- The filler of a filling of the one-entry telescope declaring a sort is interpreted as
the sort the filling gives. -/
theorem termOf_sort {X : Ctx.Ob} (τ : Ctx.Ob.Fill X (Ctx.Ob.Entry.sort X).toTele) :
  (⟨.sort, termOf M τ⟩ : Filler M (onOb M X))
    ∈ ((envOf M X).extend .nil).interpret τ.filler
  := by
  obtain ⟨s, hs, hτ⟩ := (Chain.mem_entryTerm_sort _ _).mp (termOf_mem (M := M) τ)
  rw [hτ]
  apply hs

/-- The filler of a filling of the one-entry telescope declaring an element of the sort a
filling `τ` gives is interpreted as an element of that sort. -/
theorem termOf_of {X : Ctx.Ob} {τ : Ctx.Ob.Fill X (Ctx.Ob.Entry.sort X).toTele}
    (ρ : Ctx.Ob.Fill X (Ctx.Ob.Entry.of τ).toTele) :
  (⟨.of (termOf M τ), termOf M ρ⟩ : Filler M (onOb M X))
    ∈ ((envOf M X).extend .nil).interpret ρ.filler
  := by
  obtain ⟨u, hu, hρ⟩ := (Chain.mem_entryTerm_of _ _ _).mp (termOf_mem (M := M) ρ)
  rw [hρ]
  apply hu

/-- The equation of two sorts presents the equation of the sorts they present. -/
theorem onTy_IdSort {X : Ctx.Ob} (S S' : Ctx.Tm₁ X (Ctx.U X)) :
  onTy M (Ctx.IdSort S S') = M.IdSort (onTy_U X ▸ onTm M S) (onTy_U X ▸ onTm M S')
  := by
  induction S using Ctx.Tm₁.ind with
  | ofFill τ =>
      induction S' using Ctx.Tm₁.ind with
      | ofFill τ' =>
          apply Eq.trans (onTy_mk (M := M) (Ctx.Ob.Entry.id (β := Bd.sort) not_false τ τ'))
          obtain ⟨-, hB⟩ := entryOf_mem (M := M) (Ctx.Ob.Entry.id (β := Bd.sort) not_false τ τ')
          rcases (Environment.mem_interpretBoundary_eq _ _ _ _).mp hB with
            ⟨tl, tr, hl, hr, hBe⟩ | ⟨S₀, tl, tr, hl, hr, hBe⟩
          · obtain ⟨-, htl⟩ := Filler.mk.inj (Part.mem_unique hl (termOf_sort τ))
            obtain ⟨-, htr⟩ := Filler.mk.inj (Part.mem_unique hr (termOf_sort τ'))
            rw [hBe, eq_of_heq htl, eq_of_heq htr]
            rfl
          · cases (Filler.mk.inj (Part.mem_unique hl (termOf_sort τ))).1

/-- Reflexivity of a sort presents reflexivity of the sort it presents. -/
theorem onTm_IdSort_refl {X : Ctx.Ob} (S : Ctx.Tm₁ X (Ctx.U X)) :
  HEq (onTm M (Ctx.IdSort_refl S)) (M.IdSort_refl (onTy_U X ▸ onTm M S))
  := by
  apply heq_of_cast_eq (congrArg (M.Tm (onOb M X)) (onTy_IdSort S S))
  apply M.IdSort_irrelevant

/-- The equation of two elements of a sort presents the equation of the elements they
present. -/
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
              apply Eq.trans
                (onTy_mk (M := M) (Ctx.Ob.Entry.id (β := Bd.of τ.filler) not_false ρ ν))
              obtain ⟨-, hB⟩ :=
                entryOf_mem (M := M) (Ctx.Ob.Entry.id (β := Bd.of τ.filler) not_false ρ ν)
              rcases (Environment.mem_interpretBoundary_eq _ _ _ _).mp hB with
                ⟨tl, tr, hl, hr, hBe⟩ | ⟨S₀, tl, tr, hl, hr, hBe⟩
              · cases (Filler.mk.inj (Part.mem_unique hl (termOf_of ρ))).1
              · obtain ⟨hS, htl⟩ := Filler.mk.inj (Part.mem_unique hl (termOf_of ρ))
                obtain rfl := Boundary.of.inj hS
                obtain ⟨-, htr⟩ := Filler.mk.inj (Part.mem_unique hr (termOf_of ν))
                rw [hBe, eq_of_heq htl, eq_of_heq htr]
                rfl

/-- Reflexivity of an element of a sort presents reflexivity of the element it
presents. -/
theorem onTm_IdElement_refl {X : Ctx.Ob} {S : Ctx.Tm₁ X (Ctx.U X)} (t : Ctx.Tm₁ X (Ctx.El S)) :
  HEq (onTm M (Ctx.IdElement_refl t)) (M.IdElement_refl (onTy_El S ▸ onTm M t))
  := by
  apply heq_of_cast_eq (congrArg (M.Tm (onOb M X)) (eq_of_heq (onTy_IdElement t t)))
  apply M.IdElement_irrelevant

/-! ### Extension -/

/-- Pairing a morphism of context classes with a term class presents pairing the
substitution the morphism presents with the term the term class presents. -/
theorem onSub_pair {X Y : Ctx.Ob} {a : Ctx.Ty₁ Y} (f : X ⟶ Y) (t : Ctx.Tm₁ X (a.subst f)) :
  HEq (onSub M (Ctx.Ty₁.pair f t)) (M.pair (onSub M f) (onTy_substTy a f ▸ onTm M t))
  := by
  induction Y using Quotient.ind with
  | _ Γ =>
      induction a using Quotient.ind with
      | _ e =>
          induction f using Quotient.ind with
          | _ σ =>
              induction t using Ctx.Tm₁.ind with
              | ofFill τ =>
                  obtain ⟨κ, hκ, hκσ⟩ : ∃ κ : Ctx.Ob.Subst X
                        (Ctx.Ob.extend (Quotient.mk _ Γ) (Ctx.Ty₁.toTy (Quotient.mk _ e))),
                      Ctx.Ty₁.pair (a := Quotient.mk _ e) (Quotient.mk _ σ) (Ctx.Tm₁.ofFill τ)
                        = Quotient.mk _ κ ∧ κ.1 = Subst.copair σ.1 τ.1 :=
                    ⟨_, rfl, rfl⟩
                  rw [hκ]
                  have hmem := onSub_mem (M := M) κ
                  rw [hκσ] at hmem
                  generalize onSub M (Quotient.mk _ κ) = p at hmem ⊢
                  revert p
                  dsimp only [onOb]
                  rw [telescopeOf_extend]
                  intro p hp
                  obtain ⟨s, hs, p', hp', hpp'⟩ := Environment.pairFillers_append _ _ _ _ _ p hp
                  simp only [Ctx.Ob.Tele.arity, Ctx.Ob.Entry.toTele, Ctx.Ob.Entry.subst,
                    Subst.copair_inl] at hs
                  simp only [Ctx.Ob.Tele.arity, Ctx.Ob.Entry.toTele, Ctx.Ob.Entry.subst,
                    Subst.copair_inr] at hp'
                  obtain rfl := Part.mem_unique hs (onSub_mem (M := M) σ)
                  apply HEq.trans hpp'
                  obtain ⟨t', ht', hp''⟩ := Part.mem_bind_iff.mp hp'
                  obtain rfl := Part.mem_some_iff.mp hp''
                  apply heq_of_eq
                  congr 1
                  apply eq_of_heq
                  apply HEq.trans (eqRec_heq _ _)
                  symm
                  apply HEq.trans (eqRec_heq _ _)
                  have hentry := entryOf_subst (M := M) e σ
                  obtain ⟨z, hz, hyz⟩ := Chain.entryTerm_congr (congrArg (fun q => q.1.chain) hentry)
                    (congr_arg_heq Sigma.snd hentry)
                    (congr_arg_heq (fun q => ((envOf M X).extend q.1.decoration).interpret τ.filler)
                      hentry)
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
  revert hpair
  generalize onTm M (Ctx.Tm₁.generic a) = v
  generalize onTy_substTy a (Ctx.Ob.projection X a.toTy) = h
  revert v h
  generalize onTy M (a.subst (Ctx.Ob.projection X a.toTy)) = T
  generalize onSub M (Ctx.Ob.projection X a.toTy) = p
  revert p T
  rw [onOb_extend]
  intro T p v h hpair
  apply heq_of_eq
  rw [← M.projection_pair p (h ▸ v), ← eq_of_heq hpair, M.comp_identity]

/-- The generic term of a type class presents the generic term of the type it
presents. -/
theorem onTm_generic {X : Ctx.Ob} (a : Ctx.Ty₁ X) :
  HEq (onTm M (Ctx.Tm₁.generic a)) (M.generic (onTy M a))
  := by
  have hpair := onSub_pair (M := M) (Ctx.Ob.projection X a.toTy) (Ctx.Tm₁.generic a)
  rw [Ctx.Ty₁.pair_eta, onSub_identity] at hpair
  revert hpair
  generalize onTm M (Ctx.Tm₁.generic a) = v
  generalize onTy_substTy a (Ctx.Ob.projection X a.toTy) = h
  revert v h
  generalize onTy M (a.subst (Ctx.Ob.projection X a.toTy)) = T
  generalize onSub M (Ctx.Ob.projection X a.toTy) = p
  revert p T
  rw [onOb_extend]
  intro T p v h hpair
  have hgeneric := M.generic_pair p (h ▸ v)
  rw [← eq_of_heq hpair] at hgeneric
  symm
  apply HEq.trans (HEq.symm (M.substTm_identity_heq (M.generic (onTy M a)) rfl))
  apply HEq.trans hgeneric
  apply eqRec_heq

/-! ### Binding -/

/-- An entry whose binding chain begins with the type `A` is given `lam` of the terms the
entry with the rest of the chain is given. -/
theorem Chain.mem_entryTerm_cons
    {Γ : M.Ob} {α Ω : C.Arity} (A : M.Ty Γ) (c : Chain M (M.extend Γ A) Ω)
    (B : Boundary M c.last) (w : Part (Filler M c.last)) {t} :
  t ∈ (Chain.cons (α := α) A c).entryTerm B w ↔ ∃ u ∈ c.entryTerm B w, t = M.lam u
  := by
  cases B with
  | sort =>
      constructor
      · intro ht
        obtain ⟨s, hs, rfl⟩ := (Chain.mem_entryTerm_sort _ _).mp ht
        use c.lam s, (Chain.mem_entryTerm_sort c w).mpr ⟨s, hs, rfl⟩
        rfl
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨s, hs, rfl⟩ := (Chain.mem_entryTerm_sort c w).mp hu
        apply (Chain.mem_entryTerm_sort (Chain.cons (α := α) A c) w).mpr
        use s, hs
        rfl
  | of S =>
      constructor
      · intro ht
        obtain ⟨s, hs, rfl⟩ := (Chain.mem_entryTerm_of _ _ _).mp ht
        use c.lam s, (Chain.mem_entryTerm_of c S w).mpr ⟨s, hs, rfl⟩
        rfl
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨s, hs, rfl⟩ := (Chain.mem_entryTerm_of c S w).mp hu
        apply (Chain.mem_entryTerm_of (Chain.cons (α := α) A c) S w).mpr
        use s, hs
        rfl
  | eqSort S S' =>
      constructor
      · intro ht
        obtain ⟨h, rfl⟩ := (Chain.mem_entryTerm_eqSort _ _ _ _).mp ht
        use c.lam (h ▸ M.IdSort_refl S), (Chain.mem_entryTerm_eqSort c S S' w).mpr ⟨h, rfl⟩
        rfl
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨h, rfl⟩ := (Chain.mem_entryTerm_eqSort c S S' w).mp hu
        apply (Chain.mem_entryTerm_eqSort (Chain.cons (α := α) A c) S S' w).mpr
        use h
        rfl
  | eqElement S l r =>
      constructor
      · intro ht
        obtain ⟨h, rfl⟩ := (Chain.mem_entryTerm_eqElement _ _ _ _ _).mp ht
        use c.lam (h ▸ M.IdElement_refl l), (Chain.mem_entryTerm_eqElement c S l r w).mpr ⟨h, rfl⟩
        rfl
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨h, rfl⟩ := (Chain.mem_entryTerm_eqElement c S l r w).mp hu
        apply (Chain.mem_entryTerm_eqElement (Chain.cons (α := α) A c) S l r w).mpr
        use h
        rfl

/-- The type an entry over the extension of the class of `Γ` by the class of an entry `e`
presents is `Bind` of an interpretation of the entry at the environment of `Γ` extended by
the one-entry decoration of the interpreted `e`. -/
theorem entryOf_extend (Γ : Ctx) (e : Ctx.Ob.Entry (Quotient.mk _ Γ))
    (f : Ctx.Ob.Entry (Ctx.Ob.extend (Quotient.mk _ Γ) (Ctx.Ty₁.toTy (Quotient.mk _ e)))) :
  ∃ p ∈ ((envOf M (Quotient.mk _ Γ)).extend
      (Decoration.cons (entryOf M e).1.decoration (entryOf M e).2 (onTy M (Quotient.mk _ e)) rfl
        .nil)).interpretEntry f.binding f.declaration,
    HEq (onTy M (Quotient.mk _ f)) (p.1.chain.Bind p.2.ty)
  := by
  have hq : entryOf M f ∈ (envOf M _).interpretEntry f.binding f.declaration := Part.get_mem _
  have hE := envOf_extend (M := M) Γ e
  rw [onTy_mk f]
  revert hq
  generalize entryOf M f = q
  revert q
  generalize envOf M (Ctx.Ob.extend (Quotient.mk _ Γ) (Ctx.Ty₁.toTy (Quotient.mk _ e))) = E
    at hE ⊢
  revert E
  rw [onOb_extend]
  intro E hE q hq
  obtain rfl := eq_of_heq hE
  use q, hq
  apply HEq.rfl

/-- The term a filling of the one-entry telescope of an entry over the extension of the
class of `Γ` by the class of an entry `e` gives is a term an interpretation of the entry at
the environment of `Γ` extended by the one-entry decoration of the interpreted `e` is
given by the interpretation of the filler. -/
theorem termOf_extend (Γ : Ctx) (e : Ctx.Ob.Entry (Quotient.mk _ Γ))
    {f : Ctx.Ob.Entry (Ctx.Ob.extend (Quotient.mk _ Γ) (Ctx.Ty₁.toTy (Quotient.mk _ e)))}
    (τ : Ctx.Ob.Fill (Ctx.Ob.extend (Quotient.mk _ Γ) (Ctx.Ty₁.toTy (Quotient.mk _ e)))
      f.toTele) :
  ∃ p ∈ ((envOf M (Quotient.mk _ Γ)).extend
      (Decoration.cons (entryOf M e).1.decoration (entryOf M e).2 (onTy M (Quotient.mk _ e)) rfl
        .nil)).interpretEntry f.binding f.declaration,
    ∃ u ∈ p.1.chain.entryTerm p.2
        ((((envOf M (Quotient.mk _ Γ)).extend
          (Decoration.cons (entryOf M e).1.decoration (entryOf M e).2 (onTy M (Quotient.mk _ e))
            rfl .nil)).extend p.1.decoration).interpret τ.filler),
      HEq (onTy M (Quotient.mk _ f)) (p.1.chain.Bind p.2.ty) ∧ HEq (termOf M τ) u
  := by
  have hq : entryOf M f ∈ (envOf M _).interpretEntry f.binding f.declaration := Part.get_mem _
  have hy := termOf_mem (M := M) τ
  have hE := envOf_extend (M := M) Γ e
  rw [onTy_mk f]
  revert hy
  generalize termOf M τ = y
  revert y hq
  generalize entryOf M f = q
  revert q
  generalize envOf M (Ctx.Ob.extend (Quotient.mk _ Γ) (Ctx.Ty₁.toTy (Quotient.mk _ e))) = E
    at hE ⊢
  revert E
  rw [onOb_extend]
  intro E hE q hq y hy
  obtain rfl := eq_of_heq hE
  use q, hq, y, hy
  exact ⟨HEq.rfl, HEq.rfl⟩

/-- The entry binding an entry `e` followed by the entries an entry `f` over the extension
by `e` binds is interpreted as the one-entry telescope of the interpreted `e` followed by
an interpretation of the binding telescope of `f`, with an interpretation of the
declaration of `f`. -/
theorem entryOf_bind (Γ : Ctx) (e : Ctx.Ob.Entry (Quotient.mk _ Γ))
    (f : Ctx.Ob.Entry (Ctx.Ob.extend (Quotient.mk _ Γ) (Ctx.Ty₁.toTy (Quotient.mk _ e))))
    (p : Σ T : Telescope M (M.extend (onOb M (Quotient.mk _ Γ)) (onTy M (Quotient.mk _ e)))
      f.arity, Boundary M T.chain.last)
    (hp : p ∈ ((envOf M (Quotient.mk _ Γ)).extend
      (Decoration.cons (entryOf M e).1.decoration (entryOf M e).2 (onTy M (Quotient.mk _ e)) rfl
        .nil)).interpretEntry f.binding f.declaration) :
  entryOf M (Ctx.bind Γ e f) = ⟨⟨.cons (onTy M (Quotient.mk _ e)) p.1.chain,
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

/-- `Bind` of a type class and a type class over the extension by it presents `Bind` of
the types they present. -/
theorem onTy_Bind {X : Ctx.Ob} (a : Ctx.Ty₁ X) (c : Ctx.Ty₁ (Ctx.Ob.extend X a.toTy))
    (c' : M.Ty (M.extend (onOb M X) (onTy M a))) (hc : HEq (onTy M c) c') :
  onTy M (Ctx.Bind a c) = M.Bind (onTy M a) c'
  := by
  induction X using Quotient.ind with
  | _ Γ =>
      induction a using Quotient.ind with
      | _ e =>
          induction c using Quotient.ind with
          | _ f =>
              obtain ⟨p, hp, hfp⟩ := entryOf_extend (M := M) Γ e f
              apply Eq.trans (onTy_mk (M := M) (Ctx.bind Γ e f))
              rw [entryOf_bind Γ e f p hp]
              obtain rfl := eq_of_heq (HEq.trans (HEq.symm hfp) hc)
              rfl

/-- `lam` of a term class over the extension by a type class presents `lam` of the term it
presents. -/
theorem onTm_lam {X : Ctx.Ob} {a : Ctx.Ty₁ X} {c : Ctx.Ty₁ (Ctx.Ob.extend X a.toTy)}
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
                  obtain ⟨p, hp, u, hu, hfp, hτu⟩ := termOf_extend (M := M) Γ e τ
                  obtain rfl := eq_of_heq (HEq.trans (HEq.symm hfp) hc)
                  obtain rfl := eq_of_heq (HEq.trans (HEq.symm hτu) ht)
                  have hbind := entryOf_bind Γ e f p hp
                  obtain ⟨z, hz, hyz⟩ := Chain.entryTerm_congr
                    (congrArg (fun q => q.1.chain) hbind) (congr_arg_heq Sigma.snd hbind)
                    (congr_arg_heq (fun q => ((envOf M (Quotient.mk _ Γ)).extend
                      q.1.decoration).interpret (Ctx.lamFill Γ e f τ).filler) hbind)
                    (termOf_mem (Ctx.lamFill Γ e f τ))
                  obtain ⟨u', hu', rfl⟩ := (Chain.mem_entryTerm_cons _ _ _ _).mp hz
                  simp only [Ctx.Ob.Fill.filler, Ctx.lamFill, Subst.single_head] at hu'
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
  onOb_empty := onOb_empty
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
