import HigherRankSyntax.Initiality.Naturality

/-!
# The substitution lemma

A filling of an environment `E` for the arity `Φ` by an environment `E'` for `Δ`,
both over one object, along a syntactic substitution `fill : Subst Φ Δ`, relates the
slots one by one: a slot is either renamed, `fill` sending it to the η-expansion of a
slot of `Δ` with the same value, or filled, its arity lying below a bound `Ω` and,
unless its boundary is an equation, the filler of its value being an interpretation of
its image under `fill` at `E'` extended by the value's binding decoration.

Whatever an expression, a boundary, a telescope or a filling of a decoration is
interpreted as at `E`, it is interpreted as at `E'` after substituting `fill`. The
proof is by well-founded induction on the bound `Ω` and, inside, by recursion on the
syntax.

Instantiating the block `Ω` of an expression over `Δ ⋈ Ω` by a filling `σ` of a
decoration is substituting `Subst.copair (Subst.id Δ) σ`, along which the extended
environment, reindexed along the interpretation of `σ`, is filled by the environment.
-/

universe u

namespace HrS

variable {M : Structure.{u}}

/-! ### Monotonicity -/

/-- The terms an entry is given by the fillers of `w` are terms it is given by the
fillers of `w'` when every filler of `w` is one of `w'`. -/
theorem Chain.entryTerm_mono
    {Γ : M.Ob} {α : C.Arity} (b : Chain M Γ α) (B : Boundary M b.last)
    (w w' : Part (Filler M b.last)) (hw : ∀ v ∈ w, v ∈ w') {t} (ht : t ∈ b.entryTerm B w) :
  t ∈ b.entryTerm B w'
  := by
  cases B with
  | sort =>
      obtain ⟨s, hs, rfl⟩ := (mem_entryTerm_sort b w).mp ht
      apply (mem_entryTerm_sort b w').mpr
      use s, hw _ hs
  | of S =>
      obtain ⟨e, he, rfl⟩ := (mem_entryTerm_of b S w).mp ht
      apply (mem_entryTerm_of b S w').mpr
      use e, hw _ he
  | eqSort S S' =>
      apply (mem_entryTerm_eqSort b S S' w').mpr
      apply (mem_entryTerm_eqSort b S S' w).mp ht
  | eqElement S l r =>
      apply (mem_entryTerm_eqElement b S l r w').mpr
      apply (mem_entryTerm_eqElement b S l r w).mp ht

namespace Environment

/-- A pairing of fillers at `E₁` is a pairing of other fillers at `E₂` along the same
decoration from the same substitution, when at every extension by a decoration every
filler of the first kind is one of the second. -/
theorem pairFillers_mono
    {Γ : M.Ob} {Δ₁ Δ₂ : C.Arity} (E₁ : Environment M Γ Δ₁) (E₂ : Environment M Γ Δ₂) :
    ∀ {Y : M.Ob} {Ω : C.Arity} {c : Chain M Y Ω} (d : Decoration M c) (g : M.Sub Γ Y)
      (fillers₁ : ∀ ⦃Λ : C.Arity⦄, Ω ∋ Λ → ∀ {Z : M.Ob}, Environment M Z (Δ₁ ⋈ Λ) →
        Part (Filler M Z))
      (fillers₂ : ∀ ⦃Λ : C.Arity⦄, Ω ∋ Λ → ∀ {Z : M.Ob}, Environment M Z (Δ₂ ⋈ Λ) →
        Part (Filler M Z)),
      (∀ ⦃Λ : C.Arity⦄ (i : Ω ∋ Λ) {c' : Chain M Γ Λ} (D : Decoration M c')
        (v : Filler M c'.last), v ∈ fillers₁ i (E₁.extend D) → v ∈ fillers₂ i (E₂.extend D)) →
      ∀ s ∈ E₁.pairFillers d g fillers₁, s ∈ E₂.pairFillers d g fillers₂
  | _, _, _, .nil, _, _, _, _, _, hs => hs
  | _, _, _, .cons _ _ _ _ d, _, _, _, h, s, hs => by
      obtain ⟨t, ht, hs'⟩ := Part.mem_bind_iff.mp hs
      apply Part.mem_bind_iff.mpr
      use t, Chain.entryTerm_mono _ _ _ _ (h _ _) ht
      apply pairFillers_mono E₁ E₂ d _ _ _ (fun _ j => h (C.inr j)) s hs'

/-! ### Fillings of environments -/

/-- A filling of `E` by `E'` along `fill` at `Ω`: every slot `x` of `E` is either
renamed, `fill x` being the η-expansion of a slot of `E'` with the same value, or
filled, the arity of `x` lying below `Ω` and, unless its boundary is an equation, the
filler of the value of `x` being an interpretation of `fill x` at `E'` extended by the
binding decoration of that value. -/
def Filling {Γ : M.Ob} {Φ Δ : C.Arity} (E : Environment M Γ Φ) (E' : Environment M Γ Δ)
    (fill : Subst Φ Δ) (Ω : C.Arity) : Prop :=
  ∀ ⦃α : C.Arity⦄ (x : Φ ∋ α),
    (∃ y : Δ ∋ α, fill x = Expr.η y ∧ E x = E' y)
      ∨ (Carrier.Sub α Ω ∧ (¬ (E x).filler.boundary.IsEq →
          (E x).filler ∈ (E'.extend (E x).binding.decoration).interpret (fill x)))

/-- Extending both environments of a filling by one decoration gives a filling along
`fill` lifted through the new slots: the old slots are renamed or filled as before, and
the new slots are renamed. -/
theorem Filling.extend
    {Γ : M.Ob} {Φ Δ Ω Λ : C.Arity} {E : Environment M Γ Φ} {E' : Environment M Γ Δ}
    {fill : Subst Φ Δ} (h : E.Filling E' fill Ω) {c : Chain M Γ Λ} (d : Decoration M c) :
  (E.extend d).Filling (E'.extend d) (Subst.lift fill Λ) Ω
  := by
  intro _ x
  obtain ⟨y, rfl⟩ | ⟨z, rfl⟩ := C.cover _ _ x
  · rcases h y with ⟨y', hη, hE⟩ | ⟨hsub, hval⟩
    · left
      use C.inl y'
      constructor
      · rw [Subst.lift_inl, hη, Renaming.act_eta]
        rfl
      · rw [extend_inl, extend_inl, hE]
    · right
      use hsub
      intro hne
      rw [extend_inl] at hne ⊢
      erw [Subst.lift_inl, interpret_rename, ← extend_rename, rename_inl_extend, extend_subst]
      apply interpret_subst _ _ _ _ (hval (mt (Boundary.isEq_subst _ _).mpr hne))
  · left
    use C.inr z
    constructor
    · apply Subst.lift_inr
    · rw [extend_inr, extend_inr]

/-- An environment `E` extended by a decoration and reindexed along an interpretation of
a filling `τ` of the decoration from the identity is filled by `E` along
`Subst.copair (Subst.id Δ) τ` at the arity of the decoration: the old slots are
renamed, and the new slots are filled by `τ`. -/
theorem Filling.ofSection
    {Γ : M.Ob} {Δ Ω : C.Arity} (E : Environment M Γ Δ) (τ : Subst Ω Δ)
    {c : Chain M Γ Ω} (d : Decoration M c) (s : M.Sub Γ c.last)
    (hs : s ∈ E.interpretFilling τ d (M.identity Γ)) :
  ((E.extend d).subst s).Filling E (Subst.copair (Subst.id Δ) τ) Ω
  := by
  intro _ x
  obtain ⟨y, rfl⟩ | ⟨z, rfl⟩ := C.cover _ _ x
  · left
    use y
    constructor
    · apply Subst.copair_inl
    · rw [subst, extend_inl, ← Value.subst_comp, interpretFilling_projection E τ d _ s hs,
        Value.subst_identity]
  · right
    use ⟨z⟩
    intro hne
    rw [subst, extend_inr] at hne ⊢
    rw [Subst.copair_inr]
    apply interpretFilling_slot E τ d _ s hs z (mt (Boundary.isEq_subst _ _).mpr hne)

/-! ### The substitution lemma -/

/-- If the substitution lemma holds along fillings at every arity below `Ω`, it holds
along fillings at `Ω`: along a filling of `E` by `E'` along `fill` at `Ω`, whatever an
expression is interpreted as at `E`, it is interpreted as at `E'` after substituting
`fill`. -/
theorem interpret_fill_step
    (Ω : C.Arity)
    (ih : ∀ ⦃α : C.Arity⦄, Carrier.Sub α Ω →
      ∀ {Γ : M.Ob} {Φ Δ : C.Arity} {E : Environment M Γ Φ} {E' : Environment M Γ Δ}
        {fill : Subst Φ Δ}, E.Filling E' fill α →
        ∀ (e : Expr Φ) (w : Filler M Γ), w ∈ E.interpret e → w ∈ E'.interpret (fill ⋆ e)) :
    ∀ {Γ : M.Ob} {Φ Δ : C.Arity} {E : Environment M Γ Φ} {E' : Environment M Γ Δ}
      {fill : Subst Φ Δ}, E.Filling E' fill Ω →
      ∀ (e : Expr Φ) (w : Filler M Γ), w ∈ E.interpret e → w ∈ E'.interpret (fill ⋆ e)
  | Γ, _, _, E, E', fill, hF, .ap x args, _, hw => by
      rw [interpret_ap] at hw
      obtain ⟨hne, hw⟩ := Part.mem_assert_iff.mp hw
      obtain ⟨s, hs, rfl⟩ := (Part.mem_map_iff _).mp hw
      have hs' : s ∈ E'.interpretFilling (fill ⋆ args) (E x).binding.decoration (M.identity Γ) := by
        apply pairFillers_mono E E' _ _ _ _ _ s hs
        intro _ i _ D v hv
        rw [Subst.applyEach, ← Subst.act_lift_depth]
        apply interpret_fill_step Ω ih (hF.extend D) (args i) v hv
      rcases hF x with ⟨y, hη, hE⟩ | ⟨hsub, hval⟩
      · erw [Subst.apply, act_ap_eta fill x y hη args, interpret_ap]
        apply Part.mem_assert_iff.mpr
        rw [← hE]
        use hne
        apply Part.mem_map
        apply hs'
      · erw [Subst.apply, act_ap fill x args, ← act_copair_prefix]
        apply ih hsub (Filling.ofSection E' (fill ⋆ args) _ s hs') (fill x)
        apply interpret_subst _ s (fill x) _ (hval hne)

/-- Along a filling of `E` by `E'` along `fill`, whatever an expression is interpreted
as at `E`, it is interpreted as at `E'` after substituting `fill`. -/
theorem interpret_fill :
    ∀ (Ω : C.Arity) {Γ : M.Ob} {Φ Δ : C.Arity} {E : Environment M Γ Φ}
      {E' : Environment M Γ Δ} {fill : Subst Φ Δ}, E.Filling E' fill Ω →
      ∀ (e : Expr Φ) (w : Filler M Γ), w ∈ E.interpret e → w ∈ E'.interpret (fill ⋆ e)
  := by
  intro Ω
  induction Ω using C.subWf.induction with
  | _ Ω ih => exact interpret_fill_step Ω ih

/-- Along a filling of `E` by `E'` along `fill`, whatever a boundary is interpreted as
at `E`, it is interpreted as at `E'` after substituting `fill`. -/
theorem interpretBoundary_fill
    {Γ : M.Ob} {Φ Δ Ω : C.Arity} {E : Environment M Γ Φ} {E' : Environment M Γ Δ}
    {fill : Subst Φ Δ} (h : E.Filling E' fill Ω) (β : Bd Φ) (B : Boundary M Γ)
    (hB : B ∈ E.interpretBoundary β) :
  B ∈ E'.interpretBoundary (fill ⋆ β)
  := by
  cases β with
  | sort =>
      apply (mem_interpretBoundary_sort _ _).mpr
      apply (mem_interpretBoundary_sort E B).mp hB
  | of S =>
      obtain ⟨t, ht, rfl⟩ := (mem_interpretBoundary_of E S B).mp hB
      apply (mem_interpretBoundary_of _ _ _).mpr
      use t, interpret_fill Ω h S _ ht
  | eq l r =>
      apply (mem_interpretBoundary_eq _ _ _ _).mpr
      rcases (mem_interpretBoundary_eq E l r B).mp hB with
        ⟨tl, tr, hl, hr, rfl⟩ | ⟨S, tl, tr, hl, hr, rfl⟩
      · left
        use tl, tr, interpret_fill Ω h l _ hl, interpret_fill Ω h r _ hr
      · right
        use S, tl, tr, interpret_fill Ω h l _ hl, interpret_fill Ω h r _ hr

/-- Along a filling of `E` by `E'` along `fill`, whatever a telescope is interpreted as
at `E`, it is interpreted as at `E'` after substituting `fill` in its base. -/
theorem interpretTelescope_fill :
    ∀ {Γ : M.Ob} {Φ Δ Ω Λ : C.Arity} {E : Environment M Γ Φ} {E' : Environment M Γ Δ}
      {fill : Subst Φ Δ}, E.Filling E' fill Ω → ∀ (Θ : dTel Φ Λ) (T : Telescope M Γ Λ),
      T ∈ E.interpretTelescope Θ → T ∈ E'.interpretTelescope (fill ⋆ Θ)
  | _, _, _, _, _, E, _, _, _, .nil, T, hT => by
      apply (mem_interpretTelescope_nil _ _).mpr
      apply (mem_interpretTelescope_nil E T).mp hT
  | _, _, _, _, _, E, _, _, h, .cons bind boundary rest, T, hT => by
      obtain ⟨T₀, hT₀, B, hB, A, hA, R, hR, rfl⟩ :=
        (mem_interpretTelescope_cons E bind boundary rest T).mp hT
      apply (mem_interpretTelescope_cons _ _ _ _ _).mpr
      use T₀, interpretTelescope_fill h bind T₀ hT₀, B
      constructor
      · rw [← Bd.act_lift_depth]
        apply interpretBoundary_fill (h.extend _) boundary B hB
      · use A, hA, R, interpretTelescope_fill (h.extend _) rest R hR

/-- Along a filling of `E` by `E'` along `fill`, an interpretation at `E` of a filling `τ`
of a decoration is an interpretation at `E'` of `τ` with `fill` substituted in its
fillers. -/
theorem interpretFilling_fill
    {Γ Y : M.Ob} {Φ Δ Ω Λ : C.Arity} {E : Environment M Γ Φ} {E' : Environment M Γ Δ}
    {fill : Subst Φ Δ} (h : E.Filling E' fill Ω) (τ : Subst Λ Φ) {c : Chain M Y Λ}
    (d : Decoration M c) (g : M.Sub Γ Y) (s : M.Sub Γ c.last)
    (hs : s ∈ E.interpretFilling τ d g) :
  s ∈ E'.interpretFilling (fill ⋆ τ) d g
  := by
  apply pairFillers_mono E E' d g _ _ _ s hs
  intro _ i _ D v hv
  rw [Subst.applyEach, ← Subst.act_lift_depth]
  apply interpret_fill Ω (h.extend D) (τ i) v hv

/-! ### Instantiation -/

/-- Whatever an expression over `Δ ⋈ Ω` is interpreted as at an environment extended
by a decoration, reindexed along the interpretation of a filling `σ` of the
decoration from the identity, the expression with its block `Ω` instantiated by `σ` is
interpreted as at the environment. -/
theorem interpret_instantiate
    {Γ : M.Ob} {Δ Ω : C.Arity} (E : Environment M Γ Δ) (σ : Subst Ω Δ) {c : Chain M Γ Ω}
    (d : Decoration M c) (s : M.Sub Γ c.last) (hs : s ∈ E.interpretFilling σ d (M.identity Γ))
    (g : Expr (Δ ⋈ Ω)) (v : Filler M c.last) (hv : v ∈ (E.extend d).interpret g) :
  v.subst s ∈ E.interpret (σ ⋆ g)
  := by
  rw [Subst.instantiate, ← act_copair_prefix]
  apply interpret_fill Ω (Filling.ofSection E σ d s hs) g
  apply interpret_subst (E.extend d) s g v hv

/-- Whatever a boundary over `Δ ⋈ Ω` is interpreted as at an environment extended by
a decoration, reindexed along the interpretation of a filling `σ` of the decoration
from the identity, the boundary with its block `Ω` instantiated by `σ` is interpreted
as at the environment. -/
theorem interpretBoundary_instantiate
    {Γ : M.Ob} {Δ Ω : C.Arity} (E : Environment M Γ Δ) (σ : Subst Ω Δ) {c : Chain M Γ Ω}
    (d : Decoration M c) (s : M.Sub Γ c.last) (hs : s ∈ E.interpretFilling σ d (M.identity Γ))
    (β : Bd (Δ ⋈ Ω)) (B : Boundary M c.last) (hB : B ∈ (E.extend d).interpretBoundary β) :
  B.subst s ∈ E.interpretBoundary (σ ⋆ β)
  := by
  rw [Bd.instantiate, ← Bd.act_copair_prefix]
  apply interpretBoundary_fill (Filling.ofSection E σ d s hs) β
  apply interpretBoundary_subst (E.extend d) s β B hB

/-- Whatever a telescope over `Δ ⋈ Ω` is interpreted as at an environment extended by
a decoration, reindexed along the interpretation of a filling `σ` of the decoration
from the identity, the telescope with its block `Ω` instantiated by `σ` is interpreted
as at the environment. -/
theorem interpretTelescope_instantiate
    {Γ : M.Ob} {Δ Ω Λ : C.Arity} (E : Environment M Γ Δ) (σ : Subst Ω Δ) {c : Chain M Γ Ω}
    (d : Decoration M c) (s : M.Sub Γ c.last) (hs : s ∈ E.interpretFilling σ d (M.identity Γ))
    (Θ : dTel (Δ ⋈ Ω) Λ) (T : Telescope M c.last Λ)
    (hT : T ∈ (E.extend d).interpretTelescope Θ) :
  T.subst s ∈ E.interpretTelescope (σ ⋆ Θ)
  := by
  apply interpretTelescope_fill (Filling.ofSection E σ d s hs) Θ
  apply interpretTelescope_subst (E.extend d) s Θ T hT

end Environment

end HrS
