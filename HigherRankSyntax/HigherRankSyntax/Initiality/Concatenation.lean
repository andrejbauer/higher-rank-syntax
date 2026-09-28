import HigherRankSyntax.Initiality.Soundness

/-!
# Concatenation and the η-expansion of slots

A chain over the end of a chain appends to it: the entries of the second follow
those of the first. Decorations and telescopes append likewise. Extending an
environment by an appended decoration is extending it by the first decoration and
then by the second, and the interpretation of a concatenation of syntactic
telescopes is the append of the interpretations.

The η-expansion of a slot is interpreted as the filler of the slot's value, at the
environment extended by the value's binding decoration. More generally, a filling
whose fillers are the η-expansions of slots holding generic values read along a
section is interpreted as that section.
-/

universe u

namespace HrS

variable {M : Structure.{u}}

/-! ### Appending chains, decorations and telescopes -/

/-- A chain over `Γ` followed by a chain over its end: the entries of the first, then
those of the second. -/
def Chain.append : {Γ : M.Ob} → {Φ Λ : C.Arity} → (c : Chain M Γ Φ) → Chain M c.last Λ →
    Chain M Γ (Φ ⋈ Λ)
  | _, _, _, .nil, c' => c'
  | _, _, _, @Chain.cons _ _ α _ A c, c' => .cons (α := α) A (c.append c')

/-- The end of an appended chain is the end of the second chain. -/
theorem Chain.last_append :
    ∀ {Γ : M.Ob} {Φ Λ : C.Arity} (c : Chain M Γ Φ) (c' : Chain M c.last Λ),
      (c.append c').last = c'.last
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons _ c, c' => Chain.last_append c c'

/-- The projection of an appended chain is the projection of the second chain
followed by the projection of the first. -/
theorem Chain.projection_append :
    ∀ {Γ : M.Ob} {Φ Λ : C.Arity} (c : Chain M Γ Φ) (c' : Chain M c.last Λ),
      HEq (c.append c').projection (M.comp c.projection c'.projection)
  | _, _, _, .nil, c' => by
      apply heq_of_eq
      symm
      apply M.identity_comp
  | _, _, _, .cons A c, c' => by
      erw [append, projection, projection, M.comp_assoc]
      congr 1
      · apply last_append
      · apply projection_append

/-- A decoration of a chain followed by a decoration of a chain over its end: a
decoration of the appended chain. -/
def Decoration.append : {Γ : M.Ob} → {Φ Λ : C.Arity} → {c : Chain M Γ Φ} →
    {c' : Chain M c.last Λ} → Decoration M c → Decoration M c' → Decoration M (c.append c')
  | _, _, _, _, _, .nil, d' => d'
  | _, _, _, _, _, .cons db B A hA d, d' => .cons db B A hA (d.append d')

/-- A telescope followed by a telescope over its end. -/
def Telescope.append {Γ : M.Ob} {Φ Λ : C.Arity} (T : Telescope M Γ Φ)
    (T' : Telescope M T.chain.last Λ) : Telescope M Γ (Φ ⋈ Λ) :=
  ⟨T.chain.append T'.chain, T.decoration.append T'.decoration⟩

namespace Environment

/-- Extending an environment by the empty decoration leaves it unchanged. -/
theorem extend_nil
    {Γ : M.Ob} {Δ : C.Arity} (E : Environment M Γ Δ) :
  E.extend Decoration.nil = E
  := by
  funext β x
  obtain ⟨y, rfl⟩ | ⟨z, rfl⟩ := C.cover Δ 1 x
  · rw [extend_inl, C.unit_right]
    apply Value.subst_identity
  · apply (C.unit_is_empty z).elim

/-- Extending an environment by an appended decoration is extending it by the first
decoration and then by the second. The two sides lie over objects that are equal by
`Chain.last_append`. -/
theorem extend_append :
    ∀ {Γ : M.Ob} {Δ Φ Λ : C.Arity} (E : Environment M Γ Δ) {c : Chain M Γ Φ}
      (d : Decoration M c) {c' : Chain M c.last Λ} (d' : Decoration M c'),
      HEq (E.extend (d.append d')) ((E.extend d).extend d')
  | _, Δ, _, Λ, E, _, .nil, _, d' => by
      apply heq_of_eq
      funext β x
      obtain ⟨y, rfl⟩ | ⟨z, rfl⟩ := C.cover Δ (1 ⋈ Λ) x
      · rw [extend_inl, C.inl_inl Δ 1 Λ y]
        erw [extend_inl, extend_inl, Value.subst_identity]
        rfl
      · obtain ⟨w, rfl⟩ | ⟨u, rfl⟩ := C.cover 1 Λ z
        · apply (C.unit_is_empty w).elim
        · rw [extend_inr, C.inr_inr Δ 1 Λ u, C.unit_left]
          erw [extend_inr]
          rfl
  | _, _, _, _, E, _, .cons db B A hA d, _, d' => by
      erw [extend_cons E db B A hA (d.append d')]
      rw [extend_cons E db B A hA d]
      apply extend_append

/-- The concatenation of two syntactic telescopes is interpreted as the append of an
interpretation of the first and an interpretation of the second at the environment
extended by the first. -/
theorem interpretTelescope_concatenate :
    ∀ {Γ : M.Ob} {Δ Φ Λ : C.Arity} (E : Environment M Γ Δ) (Ξ : dTel Δ Φ)
      (Θ : dTel (Δ ⋈ Φ) Λ) (T : Telescope M Γ Φ) (T' : Telescope M T.chain.last Λ),
      T ∈ E.interpretTelescope Ξ → T' ∈ (E.extend T.decoration).interpretTelescope Θ →
      T.append T' ∈ E.interpretTelescope (Ξ ⋈ Θ)
  | _, _, _, _, E, .nil, Θ, T, T', hT, hT' => by
      obtain rfl := (mem_interpretTelescope_nil E T).mp hT
      rw [extend_nil] at hT'
      apply hT'
  | _, _, _, _, E, .cons bind boundary rest, Θ, T, T', hT, hT' => by
      obtain ⟨T₀, hT₀, B, hB, A, hA, R, hR, rfl⟩ :=
        (mem_interpretTelescope_cons E bind boundary rest T).mp hT
      erw [extend_cons] at hT'
      apply (mem_interpretTelescope_cons E bind boundary (rest ⋈ Θ) _).mpr
      use T₀, hT₀, B, hB, A, hA, R.append T'
      constructor
      · apply interpretTelescope_concatenate _ rest Θ R T' hR hT'
      · rfl

end Environment

/-! ### The η-expansion of slots -/

/-- An entry with binding chain `b` and boundary `B` is given the term `b.lam u` by
fillers that contain `⟨B, u⟩` when `B` is not an equation. -/
theorem Chain.lam_mem_entryTerm
    {Γ : M.Ob} {α : C.Arity} (b : Chain M Γ α) (B : Boundary M b.last) (u : M.Tm b.last B.ty)
    {w : Part (Filler M b.last)} (hw : ¬ B.IsEq → ⟨B, u⟩ ∈ w) :
  b.lam u ∈ b.entryTerm B w
  := by
  cases B with
  | sort =>
      apply (mem_entryTerm_sort b w).mpr
      use u, hw not_false
  | of S =>
      apply (mem_entryTerm_of b S w).mpr
      use u, hw not_false
  | eqSort S S' =>
      apply (mem_entryTerm_eqSort b S S' w).mpr
      use M.IdSort_reflect u
      congr 1
      apply M.IdSort_irrelevant
  | eqElement S l r =>
      apply (mem_entryTerm_eqElement b S l r w).mpr
      use M.IdElement_reflect u
      congr 1
      apply M.IdElement_irrelevant

namespace Environment

/-- When the slots `ι i` of `F` hold the generic values of the slots `i` of `d`,
reindexed along `k`, and each of them is interpreted by its η-expansion wherever it is
not an equation, the filling of `d` by the η-expansions of the slots `ι i` is
interpreted, from the projection of `k` to the base, as `k`. -/
theorem interpretFilling_ofRenaming
    {Z : M.Ob} {Δ : C.Arity} (F : Environment M Z Δ) :
    ∀ {Y : M.Ob} {Ω : C.Arity} {c : Chain M Y Ω} (d : Decoration M c) (k : M.Sub Z c.last)
      (ι : Ω →ʳ Δ),
      (∀ ⦃β : C.Arity⦄ (i : Ω ∋ β), F (ι i) = (d.slot i).subst k) →
      (∀ ⦃β : C.Arity⦄ (i : Ω ∋ β), ¬ (F (ι i)).filler.boundary.IsEq →
        (F (ι i)).filler ∈ (F.extend (F (ι i)).binding.decoration).interpret (Expr.η (ι i))) →
      k ∈ F.interpretFilling (Subst.ofRenaming ι) d (M.comp c.projection k)
  | _, _, _, .nil, k, _, _, _ => by
      apply (mem_interpretFilling_nil F _ _ k).mpr
      symm
      apply M.identity_comp
  | _, _, _, @Decoration.cons _ _ α _ b db B A hA c d, k, ι, hslot, heta => by
      obtain ⟨g, t, hgt⟩ : ∃ g t, M.pair g t = M.comp c.projection k :=
        ⟨_, _, M.pair_components _⟩
      rw [Chain.projection, M.comp_assoc]
      erw [← hgt]
      rw [M.projection_pair]
      apply (mem_interpretFilling_cons F _ db B A hA d g k).mpr
      have hvalue : F (ι (C.inl (C.singleSlot α)))
          = (Decoration.headValue db B A hA).subst (M.pair g t) := by
        rw [hgt, hslot, Decoration.slot_head]
        symm
        apply Value.subst_comp
      rw [Decoration.headValue_subst_pair] at hvalue
      have hfiller := heta (C.inl (C.singleSlot α))
      rw [hvalue] at hfiller
      use (b.subst g).lam ((b.subst g).unlam (Chain.Bind_subst_entry hA g ▸ t))
      constructor
      · apply Chain.lam_mem_entryTerm
        apply hfiller
      · rw [Chain.lam_unlam]
        convert interpretFilling_ofRenaming F d k (fun _ j => ι (C.inr j))
          (fun _ j => by
            rw [hslot, Decoration.slot_tail]
            rfl)
          (fun _ j => heta (C.inr j)) using 2
        rw [← hgt]
        congr 1
        apply eq_of_heq
        apply HEq.trans (eqRec_heq _ _)
        apply eqRec_heq

/-- The η-expansion of a slot whose value is not an equation is interpreted, at the
environment extended by the value's binding decoration, as the value's filler. -/
theorem interpret_eta :
    ∀ {Γ : M.Ob} {Δ α : C.Arity} (E : Environment M Γ Δ) (x : Δ ∋ α),
      ¬ (E x).filler.boundary.IsEq →
      (E x).filler ∈ (E.extend (E x).binding.decoration).interpret (Expr.η x)
  := by
  intro Γ Δ α
  induction α using C.subWf.induction generalizing Γ Δ with
  | _ α ih =>
      intro E x hne
      rw [Expr.η.eq_1, interpret_ap, extend_inl]
      apply Part.mem_assert_iff.mpr
      use fun h => hne ((Boundary.isEq_subst _ _).mp h)
      have hs := interpretFilling_ofRenaming (E.extend (E x).binding.decoration)
        (E x).binding.decoration (M.identity _) (Renaming.inr Δ α)
        (fun _ i => by
          rw [Value.subst_identity]
          apply extend_inr)
        (fun β i => ih β ⟨i⟩ _ _)
      rw [interpretFilling, pairFillers_comp] at hs
      obtain ⟨s, hs, hcomp⟩ := (Part.mem_map_iff _).mp hs
      apply (Part.mem_map_iff _).mpr
      use s, hs
      simp only [Value.subst, Telescope.subst]
      rw [← Filler.subst_comp, hcomp, Filler.subst_identity]

/-- The filling of a decoration `d` by the η-expansions of its own slots, at the
environment extended by `d`, is interpreted, along `d` reindexed along the projection
of its chain and from the identity, as a section of the lift of that projection. -/
theorem interpretFilling_eta
    {Γ : M.Ob} {Δ Ω : C.Arity} (E : Environment M Γ Δ) {c : Chain M Γ Ω}
    (d : Decoration M c) :
  ∃ s ∈ (E.extend d).interpretFilling (Subst.instId Δ Ω) (d.subst c.projection)
      (M.identity c.last),
    M.comp (c.lift c.projection) s = M.identity c.last
  := by
  have hs := interpretFilling_ofRenaming (E.extend d) d (M.identity c.last) (Renaming.inr Δ Ω)
    (fun _ i => by
      rw [Value.subst_identity]
      apply extend_inr)
    (fun _ i => interpret_eta _ _)
  rw [interpretFilling, pairFillers_comp] at hs
  apply (Part.mem_map_iff _).mp hs

end Environment

end HrS
