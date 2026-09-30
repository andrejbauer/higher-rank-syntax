import HigherRankSyntax.Initiality.Substitution

/-!
# Totality and soundness of the interpretation

At every environment typed by the ambient of a judgement:

* a well-formed expression is interpreted, with a boundary interpreted from its
  computed boundary;
* equal expressions are interpreted as one filler;
* equal boundaries have the same interpretation;
* a filling of a telescope is interpreted, from the identity, along every
  interpretation of the telescope, and such an interpretation of a filling is also
  one of every filling agreeing with it;
* a well-formed declaration is interpreted at the environment extended by the
  decoration of every interpretation of its bound entries;
* a well-formed telescope is interpreted, and an interpretation of a telescope is also
  one of every telescope equal to it.

All but the statement on equal telescopes are proved by one mutual induction. In
particular every well-formed ambient is interpreted at the empty environment over every
object.
-/

universe u

namespace HrS

variable {M : Structure.{u}}

namespace Environment

/-- A boundary interpreted from a syntactic boundary is an equation exactly when the
syntactic boundary is. -/
theorem isEq_of_mem_interpretBoundary
    {Γ : M.Ob} {Δ : C.Arity} (E : Environment M Γ Δ) (β : Bd Δ) (B : Boundary M Γ)
    (hB : B ∈ E.interpretBoundary β) :
  B.IsEq ↔ β.isEq
  := by
  cases β with
  | sort =>
      obtain rfl := (mem_interpretBoundary_sort E B).mp hB
      apply Iff.rfl
  | of S =>
      obtain ⟨t, _, rfl⟩ := (mem_interpretBoundary_of E S B).mp hB
      apply Iff.rfl
  | eq l r =>
      rcases (mem_interpretBoundary_eq E l r B).mp hB with
        ⟨tl, tr, _, _, rfl⟩ | ⟨S, tl, tr, _, _, rfl⟩ <;> apply Iff.rfl

/-- Whatever an expression is interpreted as has a boundary that is not an
equation. -/
theorem not_isEq_of_mem_interpret
    {Γ : M.Ob} {Δ : C.Arity} (E : Environment M Γ Δ) (e : Expr Δ) (w : Filler M Γ)
    (hw : w ∈ E.interpret e) :
  ¬ w.boundary.IsEq
  := by
  cases e with
  | ap x args =>
      obtain ⟨hne, hw⟩ := Part.mem_assert_iff.mp hw
      obtain ⟨s, _, rfl⟩ := (Part.mem_map_iff _).mp hw
      apply (Boundary.isEq_subst _ _).not.mpr hne

/-- The empty environment is typed by the empty ambient. -/
theorem Typed.empty (Γ : M.Ob) :
  (Environment.empty (M := M) Γ).Typed .nil
  := by
  intro _ x
  apply (C.unit_is_empty x).elim

/-- Let `R` interpret `rest` at `E` extended by the one-entry decoration of `T₀` and `B`,
and let `t` be a term that the entry reindexed along the identity is given by the
interpretation of the filler of `τ`. Then `R` reindexed along the pairing of the
identity with `t` interprets `rest` instantiated by `τ`. -/
theorem interpretTelescope_pair
    {Γ : M.Ob} {Δ α Ω : C.Arity} {E : Environment M Γ Δ} {T₀ : Telescope M Γ α}
    {B : Boundary M T₀.chain.last} {A : M.Ty Γ} {hA : A = T₀.chain.Bind B.ty}
    (τ : Subst (C.single α) Δ) {rest : dTel (Δ ⋈ C.single α) Ω}
    {R : Telescope M (M.extend Γ A) Ω}
    (hR : R ∈ (E.extend (Decoration.cons T₀.decoration B A hA .nil)).interpretTelescope rest)
    {t} (ht : t ∈ (T₀.chain.subst (M.identity Γ)).entryTerm (B.subst (T₀.chain.lift (M.identity Γ)))
      ((E.extend (T₀.decoration.subst (M.identity Γ))).interpret (τ (C.singleSlot α)))) :
  R.subst (M.pair (M.identity Γ) (Chain.Bind_subst_entry hA (M.identity Γ) ▸ t))
    ∈ E.interpretTelescope (dTel.instantiate τ rest)
  := by
  apply interpretTelescope_instantiate E τ _ _ _ rest _ hR
  apply (mem_interpretFilling_cons E τ T₀.decoration B A hA .nil (M.identity Γ) _).mpr
  use t, ht
  apply Part.mem_some

end Environment

open Environment

/-! ### The judgements -/

mutual

/-- A well-formed expression is interpreted at every environment typed by its
ambient, with a boundary interpreted from its computed boundary. -/
theorem Wf_e.sound :
    ∀ {Δ : C.Arity} {Ξ : Ambient Δ} {e : Expr Δ}, Wf_e Ξ e →
      ∀ {Γ : M.Ob} (E : Environment M Γ Δ), E.Typed Ξ →
        ∃ w ∈ E.interpret e, w.boundary ∈ E.interpretBoundary (Ξ.boundaryOf e)
  | _, _, _, .ap x args head fill, _, E, hE => by
      obtain ⟨hT, hB⟩ := hE x
      obtain ⟨s, hs⟩ := Wf_s.sound fill E hE _ hT
      use (E x).filler.subst s
      constructor
      · apply Part.mem_assert_iff.mpr
        use (isEq_of_mem_interpretBoundary _ _ _ hB).not.mpr head
        apply Part.mem_map
        apply hs
      · rw [dTel.boundaryOf_ap]
        apply interpretBoundary_instantiate E args _ s hs _ _ hB

/-- Equal expressions are interpreted as one filler at every environment typed by
their ambient. -/
theorem Eq_e.sound :
    ∀ {Δ : C.Arity} {Ξ : Ambient Δ} {e e' : Expr Δ}, Eq_e Ξ e e' →
      ∀ {Γ : M.Ob} (E : Environment M Γ Δ), E.Typed Ξ →
        ∃ w, w ∈ E.interpret e ∧ w ∈ E.interpret e'
  | _, _, _, _, .refl h, _, E, hE => by
      obtain ⟨w, hw, _⟩ := Wf_e.sound h E hE
      use w
  | _, _, _, _, .symm h, _, E, hE => by
      obtain ⟨w, hw₁, hw₂⟩ := Eq_e.sound h E hE
      use w
  | _, _, _, _, .trans h h', _, E, hE => by
      obtain ⟨w, hw₁, hw₂⟩ := Eq_e.sound h E hE
      obtain ⟨v, hv₁, hv₂⟩ := Eq_e.sound h' E hE
      obtain rfl := Part.mem_unique hw₂ hv₁
      use w
  | _, _, _, _, .hyp q l r args decl _ _ fill, _, E, hE => by
      obtain ⟨hT, hB⟩ := hE q
      rw [decl] at hB
      obtain ⟨s, hs⟩ := Wf_s.sound fill E hE _ hT
      rcases (mem_interpretBoundary_eq _ l r _).mp hB with
        ⟨tl, tr, hl, hr, hBe⟩ | ⟨S, tl, tr, hl, hr, hBe⟩
      · obtain rfl := M.IdSort_reflect (hBe ▸ (E q).filler.tm)
        use (Filler.mk .sort tl).subst s
        constructor
        · apply interpret_instantiate E args _ s hs l _ hl
        · apply interpret_instantiate E args _ s hs r _ hr
      · obtain rfl := M.IdElement_reflect (hBe ▸ (E q).filler.tm)
        use (Filler.mk (.of S) tl).subst s
        constructor
        · apply interpret_instantiate E args _ s hs l _ hl
        · apply interpret_instantiate E args _ s hs r _ hr
  | _, _, _, _, .congr σ θ hΘ hσ _ agree h, _, E, hE => by
      obtain ⟨T, hT⟩ := Wf_t.sound hΘ E hE
      obtain ⟨v, hv₁, hv₂⟩ := Eq_e.sound h (E.extend T.decoration) (Typed.extend hE hT)
      obtain ⟨s, hs⟩ := Wf_s.sound hσ E hE _ hT
      use v.subst s
      constructor
      · apply interpret_instantiate E σ _ s hs _ _ hv₁
      · apply interpret_instantiate E θ _ s (Eq_s.sound agree E hE _ hT s hs) _ _ hv₂

/-- Equal boundaries have the same interpretation at every environment typed by their
ambient. -/
theorem Eq_bd.sound :
    ∀ {Δ : C.Arity} {Ξ : Ambient Δ} {β β' : Bd Δ}, Eq_bd Ξ β β' →
      ∀ {Γ : M.Ob} (E : Environment M Γ Δ), E.Typed Ξ →
        E.interpretBoundary β = E.interpretBoundary β'
  | _, _, _, _, .sort, _, _, _ => rfl
  | _, _, _, _, .of h, _, E, hE => by
      obtain ⟨w, hw₁, hw₂⟩ := Eq_e.sound h E hE
      rw [interpretBoundary, interpretBoundary, Part.eq_some_iff.mpr hw₁, Part.eq_some_iff.mpr hw₂]
  | _, _, _, _, .eq hl hr, _, E, hE => by
      obtain ⟨wl, hwl₁, hwl₂⟩ := Eq_e.sound hl E hE
      obtain ⟨wr, hwr₁, hwr₂⟩ := Eq_e.sound hr E hE
      rw [interpretBoundary, interpretBoundary, Part.eq_some_iff.mpr hwl₁,
        Part.eq_some_iff.mpr hwl₂, Part.eq_some_iff.mpr hwr₁, Part.eq_some_iff.mpr hwr₂]

/-- A filling of a telescope is interpreted, from the identity, along every
interpretation of the telescope at an environment typed by the ambient. -/
theorem Wf_s.sound :
    ∀ {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω} {σ : Subst Ω Δ}, Wf_s Ξ Θ σ →
      ∀ {Γ : M.Ob} (E : Environment M Γ Δ), E.Typed Ξ →
        ∀ T ∈ E.interpretTelescope Θ, ∃ s, s ∈ E.interpretFilling σ T.decoration (M.identity Γ)
  | _, _, _, _, _, .nil, Γ, E, _, T, hT => by
      obtain rfl := (mem_interpretTelescope_nil E T).mp hT
      use M.identity Γ
      apply (mem_interpretFilling_nil _ _ _ _).mpr rfl
  | _, _, _, _, σ, .cons (bind := bind) (boundary := boundary) (rest := rest)
      equation filler declared hrest, Γ, E, hE, T, hT => by
      obtain ⟨T₀, hT₀, B, hB, A, hA, R, hR, rfl⟩ :=
        (mem_interpretTelescope_cons E bind boundary rest T).mp hT
      rw [← Telescope.subst_identity T₀] at hT₀
      have hE₁ := Typed.extend hE hT₀
      have hequation := fun l r (h : boundary = .eq l r) => Eq_e.sound (equation l r h) _ hE₁
      have hEid : E.subst (M.identity Γ) = E := by
        funext _ x
        apply Value.subst_identity
      have hB₁ := interpretBoundary_subst _ (T₀.chain.lift (M.identity Γ)) _ _ hB
      rw [← extend_subst, hEid] at hB₁
      obtain ⟨t, ht⟩ : ∃ t, t ∈ (T₀.chain.subst (M.identity Γ)).entryTerm
          (B.subst (T₀.chain.lift (M.identity Γ)))
          ((E.extend (T₀.decoration.subst (M.identity Γ))).interpret
            (σ (C.inl (C.singleSlot _)))) := by
        by_cases hbe : boundary.isEq
        · cases boundary with
          | eq l r =>
              obtain ⟨v, hvl, hvr⟩ := hequation l r rfl
              rcases (mem_interpretBoundary_eq _ l r _).mp hB₁ with
                ⟨tl, tr, hl, hr, hBe⟩ | ⟨S, tl, tr, hl, hr, hBe⟩
              · obtain rfl := Part.mem_unique hl hvl
                cases Part.mem_unique hvr hr
                rw [hBe]
                exact ⟨_, (Chain.mem_entryTerm_eqSort _ _ _ _).mpr ⟨rfl, rfl⟩⟩
              · obtain rfl := Part.mem_unique hl hvl
                cases Part.mem_unique hvr hr
                rw [hBe]
                exact ⟨_, (Chain.mem_entryTerm_eqElement _ _ _ _ _).mpr ⟨rfl, rfl⟩⟩
          | _ => apply False.elim hbe
        · obtain ⟨⟨Bw, tw⟩, hw, hwb⟩ := Wf_e.sound (filler hbe) _ hE₁
          rw [Eq_bd.sound (declared hbe) _ hE₁] at hwb
          obtain rfl := Part.mem_unique hwb hB₁
          cases B with
          | sort => exact ⟨_, (Chain.mem_entryTerm_sort _ _).mpr ⟨tw, hw, rfl⟩⟩
          | of S => exact ⟨_, (Chain.mem_entryTerm_of _ _ _).mpr ⟨tw, hw, rfl⟩⟩
          | _ => apply (not_isEq_of_mem_interpret _ _ _ hw trivial).elim
      obtain ⟨s', hs'⟩ :=
        Wf_s.sound hrest E hE _ (interpretTelescope_pair (fun _ i => σ (C.inl i)) hR ht)
      have hcomp := pairFillers_comp (Y := M.extend Γ A) E R.decoration
        (M.pair (M.identity Γ) (Chain.Bind_subst_entry hA (M.identity Γ) ▸ t)) (M.identity Γ)
      rw [M.comp_identity] at hcomp
      use M.comp (R.chain.lift _) s'
      apply (mem_interpretFilling_cons E σ T₀.decoration B A hA R.decoration _ _).mpr
      use t, ht
      rw [interpretFilling, hcomp]
      apply Part.mem_map
      apply hs'

/-- Along every interpretation of a telescope at an environment typed by the ambient,
an interpretation, from the identity, of a filling is also one of every filling
agreeing with it. -/
theorem Eq_s.sound :
    ∀ {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω} {σ θ : Subst Ω Δ}, Eq_s Ξ Θ σ θ →
      ∀ {Γ : M.Ob} (E : Environment M Γ Δ), E.Typed Ξ →
        ∀ T ∈ E.interpretTelescope Θ, ∀ s ∈ E.interpretFilling σ T.decoration (M.identity Γ),
          s ∈ E.interpretFilling θ T.decoration (M.identity Γ)
  | _, _, _, _, _, _, .nil, _, E, _, T, hT, s, hs => by
      obtain rfl := (mem_interpretTelescope_nil E T).mp hT
      apply hs
  | _, _, _, _, σ, θ, .cons (bind := bind) (boundary := boundary) (rest := rest) slot hrest,
      Γ, E, hE, T, hT, s, hs => by
      obtain ⟨T₀, hT₀, B, hB, A, hA, R, hR, rfl⟩ :=
        (mem_interpretTelescope_cons E bind boundary rest T).mp hT
      obtain ⟨t, ht, hs₁⟩ :=
        (mem_interpretFilling_cons E σ T₀.decoration B A hA R.decoration _ s).mp hs
      apply (mem_interpretFilling_cons E θ T₀.decoration B A hA R.decoration _ s).mpr
      use t
      constructor
      · by_cases hbe : boundary.isEq
        · cases B with
          | sort | of _ => apply ((isEq_of_mem_interpretBoundary _ _ _ hB).mpr hbe).elim
          | _ => apply ht
        · rw [← Telescope.subst_identity T₀] at hT₀
          obtain ⟨v, hvσ, hvθ⟩ := Eq_e.sound (slot hbe) _ (Typed.extend hE hT₀)
          apply Chain.entryTerm_mono _ _ _ _ _ ht
          intro v' hv'
          obtain rfl := Part.mem_unique hv' hvσ
          apply hvθ
      · have hcomp := pairFillers_comp (Y := M.extend Γ A) E R.decoration
          (M.pair (M.identity Γ) (Chain.Bind_subst_entry hA (M.identity Γ) ▸ t)) (M.identity Γ)
        rw [M.comp_identity] at hcomp
        rw [interpretFilling, hcomp] at hs₁
        obtain ⟨s', hs', rfl⟩ := (Part.mem_map_iff _).mp hs₁
        rw [interpretFilling, hcomp]
        apply Part.mem_map
        apply Eq_s.sound hrest E hE _ (interpretTelescope_pair (fun _ i => σ (C.inl i)) hR ht) _ hs'

/-- A well-formed declaration is interpreted at an environment typed by the ambient,
extended by the decoration of every interpretation of its bound entries. -/
theorem Wf_bd.sound :
    ∀ {Δ Λ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Λ} {β : Bd (Δ ⋈ Λ)}, Wf_bd Ξ Θ β →
      ∀ {Γ : M.Ob} (E : Environment M Γ Δ), E.Typed Ξ →
        ∀ T ∈ E.interpretTelescope Θ, ∃ B, B ∈ (E.extend T.decoration).interpretBoundary β
  | _, _, _, _, _, .sort, _, _, _, _, _ => ⟨.sort, Part.mem_some _⟩
  | _, _, _, _, _, .of hS hsort, _, E, hE, T, hT => by
      have hE₁ := Typed.extend hE hT
      obtain ⟨⟨Bw, tw⟩, hw, hwb⟩ := Wf_e.sound hS _ hE₁
      rw [Eq_bd.sound hsort _ hE₁, mem_interpretBoundary_sort] at hwb
      obtain rfl := hwb
      use .of tw
      apply (mem_interpretBoundary_of _ _ _).mpr
      use tw, hw
  | _, _, _, _, _, .eq hl hr heq, _, E, hE, T, hT => by
      have hE₁ := Typed.extend hE hT
      obtain ⟨⟨Bl, tl⟩, hwl, hwlb⟩ := Wf_e.sound hl _ hE₁
      obtain ⟨⟨Br, tr⟩, hwr, hwrb⟩ := Wf_e.sound hr _ hE₁
      rw [Eq_bd.sound heq _ hE₁] at hwlb
      obtain rfl := Part.mem_unique hwlb hwrb
      cases Bl with
      | sort =>
          use .eqSort tl tr
          apply (mem_interpretBoundary_eq _ _ _ _).mpr
          left
          use tl, tr, hwl, hwr
      | of S =>
          use .eqElement S tl tr
          apply (mem_interpretBoundary_eq _ _ _ _).mpr
          right
          use S, tl, tr, hwl, hwr
      | _ => apply (not_isEq_of_mem_interpret _ _ _ hwl trivial).elim

/-- A well-formed telescope is interpreted at every environment typed by its
ambient. -/
theorem Wf_t.sound :
    ∀ {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω}, Wf_t Ξ Θ →
      ∀ {Γ : M.Ob} (E : Environment M Γ Δ), E.Typed Ξ → ∃ T, T ∈ E.interpretTelescope Θ
  | _, _, _, _, .nil, _, _, _ => ⟨⟨.nil, .nil⟩, Part.mem_some _⟩
  | _, _, _, _, .cons (bind := bind) (boundary := boundary) (rest := rest) hbind hboundary hrest,
      Γ, E, hE => by
      obtain ⟨T₀, hT₀⟩ := Wf_t.sound hbind E hE
      obtain ⟨B, hB⟩ := Wf_bd.sound hboundary E hE T₀ hT₀
      have h₁ : ⟨.cons (T₀.chain.Bind B.ty) .nil, .cons T₀.decoration B _ rfl .nil⟩
          ∈ E.interpretTelescope (.cons bind boundary .nil) := by
        apply (mem_interpretTelescope_cons _ _ _ _ _).mpr
        use T₀, hT₀, B, hB, T₀.chain.Bind B.ty, rfl, ⟨.nil, .nil⟩, Part.mem_some _
        rfl
      obtain ⟨R, hR⟩ := Wf_t.sound hrest _ (Typed.extend hE h₁)
      use ⟨.cons (T₀.chain.Bind B.ty) R.chain, .cons T₀.decoration B _ rfl R.decoration⟩
      apply (mem_interpretTelescope_cons _ _ _ _ _).mpr
      use T₀, hT₀, B, hB, T₀.chain.Bind B.ty, rfl, R, hR

end

/-- At every environment typed by their ambient, an interpretation of the first of two
equal telescopes is also one of the second. -/
theorem Eq_t.sound :
    ∀ {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ Θ' : dTel Δ Ω}, Eq_t Ξ Θ Θ' →
      ∀ {Γ : M.Ob} (E : Environment M Γ Δ), E.Typed Ξ →
        ∀ T ∈ E.interpretTelescope Θ, T ∈ E.interpretTelescope Θ'
  | _, _, _, .nil, _, h, _, _, _, T, hT => by
      obtain rfl := h
      apply hT
  | _, _, _, .cons bind boundary rest, _, h, _, E, hE, T, hT => by
      obtain ⟨bind', boundary', rest', rfl, hbind, hboundary, hrest⟩ := h
      obtain ⟨T₀, hT₀, B, hB, A, hA, R, hR, rfl⟩ :=
        (mem_interpretTelescope_cons E bind boundary rest T).mp hT
      have h₁ : ⟨.cons A .nil, .cons T₀.decoration B A hA .nil⟩
          ∈ E.interpretTelescope (.cons bind boundary .nil) := by
        apply (mem_interpretTelescope_cons _ _ _ _ _).mpr
        use T₀, hT₀, B, hB, A, hA, ⟨.nil, .nil⟩, Part.mem_some _
        rfl
      apply (mem_interpretTelescope_cons E bind' boundary' rest' _).mpr
      use T₀, Eq_t.sound hbind E hE T₀ hT₀, B
      constructor
      · rw [← Eq_bd.sound hboundary _ (Typed.extend hE hT₀)]
        apply hB
      · use A, hA, R, Eq_t.sound hrest _ (Typed.extend hE h₁) R hR

/-- A well-formed ambient is interpreted at the empty environment over every
object. -/
theorem Ambient.Wf.sound
    {Δ : C.Arity} {Ξ : Ambient Δ} (h : Ambient.Wf Ξ) (Γ : M.Ob) :
  ∃ T, T ∈ (Environment.empty Γ).interpretTelescope Ξ
  := by
  apply Wf_t.sound h _ (Typed.empty Γ)

end HrS
