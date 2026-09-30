import Mathlib.Data.Part
import HigherRankSyntax.Initiality.Environment
import HigherRankSyntax.Typing.Telescope

/-!
# The interpretation of the syntax in a model

The interpretation is partial and relative to an environment `E` over an object `Γ`
of a model `M`, which gives every slot of the arity a value over `Γ`.

* An expression `ap x args` is interpreted as the filler of the value of `x`,
  reindexed along the substitution that pairs the identity, entry by entry along the
  binding decoration of `x`, with the terms that the interpreted arguments give,
  provided the boundary of that filler is not an equation.
* A syntactic filling of a telescope is interpreted in the same way, as a
  substitution into the end of a decorated chain.
* A boundary is interpreted as a semantic boundary: `sort` as `sort`, `of S` as `of`
  the sort `S` is interpreted as, and `eq l r` as the equation of two sorts or of two
  elements of one sort, according to what `l` and `r` are interpreted as.
* A telescope is interpreted entry by entry: each entry's binding telescope at the
  environment extended by the entries before it, and its boundary at that environment
  extended further by the interpreted binding decoration.

An interpretation is undefined when the boundary of a head's value is an equation, a
filler does not fit the entry it fills, `S` in `of S` is not interpreted as a sort,
`l` and `r` in `eq l r` are not interpreted as two sorts or as two elements of one
sort, or an equation between terms of the model does not hold.
An environment is typed by an ambient when the binding telescope and the boundary of
the value of each slot are the interpretations of the slot's binding telescope and
declaration.
-/

universe u

namespace HrS

variable {M : Structure.{u}}

/-! ### Checks on fillers -/

/-- The sort a filler is, defined when its boundary is `sort`. -/
def Filler.asSort {Γ : M.Ob} : Filler M Γ → Part (M.Tm Γ (M.U Γ))
  | ⟨.sort, t⟩ => Part.some t
  | _ => Part.none

/-- The element of the sort `S` a filler is, defined when its boundary is `of S'` for a
sort `S'` equal to `S`. -/
def Filler.asElement {Γ : M.Ob} :
    Filler M Γ → (S : M.Tm Γ (M.U Γ)) → Part (M.Tm Γ (M.El S))
  | ⟨.of S', t⟩, S => Part.assert (S' = S) fun h => Part.some (h ▸ t)
  | _, _ => Part.none

/-- `t` is the sort a filler is exactly when the filler is `t` with boundary `sort`. -/
theorem Filler.mem_asSort
    {Γ : M.Ob} (w : Filler M Γ) (t : M.Tm Γ (M.U Γ)) :
  t ∈ w.asSort ↔ w = ⟨.sort, t⟩
  := by
  constructor
  · intro h
    obtain ⟨B, s⟩ := w
    cases B with
    | sort => rw [Part.mem_some_iff.mp h]
    | _ => cases Part.notMem_none _ h
  · rintro rfl
    apply Part.mem_some

/-- `t` is the element of `S` a filler is exactly when the filler is `t` with boundary
`of S`. -/
theorem Filler.mem_asElement
    {Γ : M.Ob} (w : Filler M Γ) (S : M.Tm Γ (M.U Γ)) (t : M.Tm Γ (M.El S)) :
  t ∈ w.asElement S ↔ w = ⟨.of S, t⟩
  := by
  constructor
  · intro h
    obtain ⟨B, s⟩ := w
    cases B with
    | of S' =>
        obtain ⟨rfl, h'⟩ := Part.mem_assert_iff.mp h
        rw [Part.mem_some_iff.mp h']
    | _ => cases Part.notMem_none _ h
  · rintro rfl
    apply Part.mem_assert_iff.mpr
    use rfl
    apply Part.mem_some

/-! ### Filling one entry -/

/-- The term over `Γ` of the type `b.Bind B.ty` of an entry with binding chain `b` and
boundary `B`, given by a partial filler `w` over the end of `b`. For `B` = `sort` or
`of S`, it is the term of `w` read over `Γ` by `lam`, defined when `w` is defined with
boundary `B`. For `B` an equation, `w` is not used: the term is reflexivity read over
`Γ` by `lam`, defined when the two sides of the equation are equal. -/
def Chain.entryTerm {Γ : M.Ob} {α : C.Arity} (b : Chain M Γ α) :
    (B : Boundary M b.last) → Part (Filler M b.last) → Part (M.Tm Γ (b.Bind B.ty))
  | .sort, w => w.bind fun v => v.asSort.map b.lam
  | .of S, w => w.bind fun v => (v.asElement S).map b.lam
  | .eqSort S S', _ => Part.assert (S = S') fun h => Part.some (b.lam (h ▸ M.IdSort_refl S))
  | .eqElement _ l r, _ =>
      Part.assert (l = r) fun h => Part.some (b.lam (h ▸ M.IdElement_refl l))

/-- The entry with boundary `sort` is given the term `t` by `w` exactly when `w`
contains the filler `⟨sort, s⟩` of a sort `s` with `t = b.lam s`. -/
theorem Chain.mem_entryTerm_sort
    {Γ : M.Ob} {α : C.Arity} (b : Chain M Γ α) (w : Part (Filler M b.last))
    {t} :
  t ∈ b.entryTerm .sort w ↔ ∃ s, ⟨.sort, s⟩ ∈ w ∧ t = b.lam s
  := by
  simp only [entryTerm, Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨_, hv, s, hs, rfl⟩
    obtain rfl := (Filler.mem_asSort _ _).mp hs
    use s, hv
  · rintro ⟨s, hs, rfl⟩
    use ⟨.sort, s⟩, hs, s, Part.mem_some s

/-- The entry with boundary `of S` is given the term `t` by `w` exactly when `w`
contains the filler `⟨of S, e⟩` of an element `e` of `S` with `t = b.lam e`. -/
theorem Chain.mem_entryTerm_of
    {Γ : M.Ob} {α : C.Arity} (b : Chain M Γ α) (S : M.Tm b.last (M.U b.last))
    (w : Part (Filler M b.last)) {t} :
  t ∈ b.entryTerm (.of S) w ↔ ∃ e, ⟨.of S, e⟩ ∈ w ∧ t = b.lam e
  := by
  simp only [entryTerm, Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨_, hv, e, he, rfl⟩
    obtain rfl := (Filler.mem_asElement _ _ _).mp he
    use e, hv
  · rintro ⟨e, he, rfl⟩
    use ⟨.of S, e⟩, he, e, (Filler.mem_asElement _ _ _).mpr rfl

/-- The entry declaring the equation of the sorts `S` and `S'` is given the term `t` by
`w` exactly when `S = S'` and `t` is reflexivity read over `Γ` by `lam`. -/
theorem Chain.mem_entryTerm_eqSort
    {Γ : M.Ob} {α : C.Arity} (b : Chain M Γ α) (S S' : M.Tm b.last (M.U b.last))
    (w : Part (Filler M b.last)) {t} :
  t ∈ b.entryTerm (.eqSort S S') w ↔ ∃ h : S = S', t = b.lam (h ▸ M.IdSort_refl S)
  := by
  simp only [entryTerm, Part.mem_assert_iff, Part.mem_some_iff]

/-- The entry declaring the equation of the elements `l` and `r` is given the term `t`
by `w` exactly when `l = r` and `t` is reflexivity read over `Γ` by `lam`. -/
theorem Chain.mem_entryTerm_eqElement
    {Γ : M.Ob} {α : C.Arity} (b : Chain M Γ α) (S : M.Tm b.last (M.U b.last))
    (l r : M.Tm b.last (M.El S)) (w : Part (Filler M b.last)) {t} :
  t ∈ b.entryTerm (.eqElement S l r) w ↔ ∃ h : l = r, t = b.lam (h ▸ M.IdElement_refl l)
  := by
  simp only [entryTerm, Part.mem_assert_iff, Part.mem_some_iff]

/-- For equal chains `b₁ = b₂` and heterogeneously equal boundaries and partial fillers,
every term in `b₁.entryTerm B₁ w₁` is heterogeneously equal to a term in
`b₂.entryTerm B₂ w₂`. -/
theorem Chain.entryTerm_congr
    {Γ : M.Ob} {α : C.Arity} {b₁ b₂ : Chain M Γ α} (hb : b₁ = b₂)
    {B₁ : Boundary M b₁.last} {B₂ : Boundary M b₂.last} (hB : HEq B₁ B₂)
    {w₁ : Part (Filler M b₁.last)} {w₂ : Part (Filler M b₂.last)} (hw : HEq w₁ w₂)
    {t₁ : M.Tm Γ (b₁.Bind B₁.ty)} (ht : t₁ ∈ b₁.entryTerm B₁ w₁) :
  ∃ t₂ ∈ b₂.entryTerm B₂ w₂, HEq t₁ t₂
  := by
  subst hb
  obtain rfl := eq_of_heq hB
  obtain rfl := eq_of_heq hw
  use t₁, ht

namespace Environment

/-! ### The interpretation -/

/-- The substitution from `Γ` into the end of the chain of `d` that pairs `g` with one
term for each entry of `d`, in turn. The term for an entry is its `entryTerm`, with the
entry reindexed along the substitution paired so far; the entry's filler is given by
`fillers` at `E` extended by the entry's reindexed binding decoration. -/
def pairFillers {Γ : M.Ob} {Δ : C.Arity} (E : Environment M Γ Δ) :
    {Y : M.Ob} → {Ω : C.Arity} → {c : Chain M Y Ω} → Decoration M c → M.Sub Γ Y →
    (∀ ⦃Λ : C.Arity⦄, Ω ∋ Λ → ∀ {Z : M.Ob}, Environment M Z (Δ ⋈ Λ) → Part (Filler M Z)) →
    Part (M.Sub Γ c.last)
  | _, _, _, .nil, g, _ => Part.some g
  | _, _, _, @Decoration.cons _ _ α _ b db B A hA c d, g, fillers =>
      ((b.subst g).entryTerm (B.subst (b.lift g))
          (fillers (C.inl (C.singleSlot α)) (E.extend (db.subst g)))).bind
        fun t => pairFillers E (c := c) d (M.pair g (Chain.Bind_subst_entry hA g ▸ t))
          (fun _ j _ E' => fillers (C.inr j) E')

/-- The interpretation of an expression at an environment. The expression `ap x args`
is interpreted, when the boundary of the value of `x` is not an equation, as the filler
of that value, reindexed along the substitution that pairs the identity, along the
binding decoration of `x`, with the terms the arguments give; each argument is
interpreted at the environment extended by the binding decoration of the entry it fills,
that decoration reindexed along the substitution paired before that entry. -/
def interpret : {Γ : M.Ob} → {Δ : C.Arity} → Environment M Γ Δ → Expr Δ → Part (Filler M Γ)
  | Γ, _, E, .ap x args =>
      Part.assert (¬ (E x).filler.boundary.IsEq) fun _ =>
        (E.pairFillers (E x).binding.decoration (M.identity Γ)
            (fun _ i _ E' => interpret E' (args i))).map (E x).filler.subst

/-- The interpretation of a filling `σ` of a telescope along a decoration `d` over `Y`,
from a substitution `g` from `Γ` to `Y`: the substitution into the end of the chain of
`d` that pairs `g` with the terms the fillers of `σ` give. -/
def interpretFilling {Γ : M.Ob} {Δ Ω : C.Arity} (E : Environment M Γ Δ) (σ : Subst Ω Δ)
    {Y : M.Ob} {c : Chain M Y Ω} (d : Decoration M c) (g : M.Sub Γ Y) :
    Part (M.Sub Γ c.last) :=
  E.pairFillers d g (fun _ i _ E' => E'.interpret (σ i))

/-- The interpretation of a boundary: `sort` is `sort`; `of S` is `of` the sort `S` is
interpreted as; `eq l r` is the equation of the sorts `l` and `r` are interpreted as,
or of the elements of one sort they are interpreted as. -/
def interpretBoundary {Γ : M.Ob} {Δ : C.Arity} (E : Environment M Γ Δ) :
    Bd Δ → Part (Boundary M Γ)
  | .sort => Part.some .sort
  | .of S => (E.interpret S).bind fun w => w.asSort.map .of
  | .eq l r => (E.interpret l).bind fun wl => (E.interpret r).bind fun wr =>
      match wl with
      | ⟨.sort, tl⟩ => wr.asSort.map (.eqSort tl)
      | ⟨.of S, tl⟩ => (wr.asElement S).map (.eqElement S tl)
      | _ => Part.none

/-- The interpretation of a telescope, entry by entry: the binding telescope of an
entry, then its boundary at the environment extended by the interpreted binding
decoration; the entry's type is `Bind` of the interpreted binding chain at the type of
the interpreted boundary, and the remaining entries are interpreted at the environment
extended by that one entry. -/
def interpretTelescope : {Γ : M.Ob} → {Δ Ω : C.Arity} → Environment M Γ Δ → dTel Δ Ω →
    Part (Telescope M Γ Ω)
  | _, _, _, _, .nil => Part.some ⟨.nil, .nil⟩
  | _, _, _, E, .cons (α := α) bind boundary rest =>
      (interpretTelescope E bind).bind fun T =>
        ((E.extend T.decoration).interpretBoundary boundary).bind fun B =>
          (interpretTelescope (E.extend (Decoration.cons T.decoration B _ rfl .nil)) rest).map
            fun R => ⟨.cons (α := α) (T.chain.Bind B.ty) R.chain,
              .cons T.decoration B _ rfl R.decoration⟩

/-- An environment is typed by an ambient when, for every slot, the binding telescope
of its value is the interpretation of the slot's binding telescope, and the boundary
of its value is the interpretation of the slot's declaration at the environment
extended by that binding decoration. -/
def Typed {Γ : M.Ob} {Δ : C.Arity} (E : Environment M Γ Δ) (Ξ : Ambient Δ) : Prop :=
  ∀ ⦃α : C.Arity⦄ (x : Δ ∋ α),
    (E x).binding ∈ E.interpretTelescope (Ξ.binding x) ∧
      (E x).filler.boundary
        ∈ (E.extend (E x).binding.decoration).interpretBoundary (Ξ.declaration x)

/-! ### The interpretation, clause by clause -/

/-- `ap x args` is interpreted, when the boundary of the value of `x` is not an
equation, as the filler of that value, reindexed along the interpretation of `args` as
a filling along the binding decoration of `x`, from the identity. -/
theorem interpret_ap
    {Γ : M.Ob} {Δ α : C.Arity} (E : Environment M Γ Δ) (x : Δ ∋ α) (args : Subst α Δ) :
  E.interpret (.ap x args)
    = Part.assert (¬ (E x).filler.boundary.IsEq) fun _ =>
        (E.interpretFilling args (E x).binding.decoration (M.identity Γ)).map
          (E x).filler.subst
  := rfl

/-- A filling along the empty decoration is interpreted as the substitution it
starts from. -/
theorem mem_interpretFilling_nil
    {Γ Y : M.Ob} {Δ : C.Arity} (E : Environment M Γ Δ) (σ : Subst 1 Δ) (g : M.Sub Γ Y)
    (s : M.Sub Γ Y) :
  s ∈ E.interpretFilling σ .nil g ↔ s = g
  := by
  apply Part.mem_some_iff

/-- A filling along a decoration with a first entry is interpreted by pairing the
substitution it starts from with the term the first filler gives the reindexed entry,
and continuing along the rest of the decoration with the remaining fillers. -/
theorem mem_interpretFilling_cons
    {Γ Y : M.Ob} {Δ α Ω : C.Arity} (E : Environment M Γ Δ)
    (σ : Subst (C.single α ⋈ Ω) Δ) {b : Chain M Y α} (db : Decoration M b)
    (B : Boundary M b.last) (A : M.Ty Y) (hA : A = b.Bind B.ty)
    {c : Chain M (M.extend Y A) Ω} (d : Decoration M c) (g : M.Sub Γ Y)
    (s : M.Sub Γ c.last) :
  s ∈ E.interpretFilling σ (.cons db B A hA d) g
    ↔ ∃ t ∈ (b.subst g).entryTerm (B.subst (b.lift g))
          ((E.extend (db.subst g)).interpret (σ (C.inl (C.singleSlot α)))),
        s ∈ E.interpretFilling (fun _ j => σ (C.inr j)) d
          (M.pair g (Chain.Bind_subst_entry hA g ▸ t))
  := by
  apply Part.mem_bind_iff

/-- `sort` is interpreted as `sort`. -/
theorem mem_interpretBoundary_sort
    {Γ : M.Ob} {Δ : C.Arity} (E : Environment M Γ Δ) (B : Boundary M Γ) :
  B ∈ E.interpretBoundary .sort ↔ B = .sort
  := by
  apply Part.mem_some_iff

/-- `of S` is interpreted as `of t` for a sort `t` that `S` is interpreted as. -/
theorem mem_interpretBoundary_of
    {Γ : M.Ob} {Δ : C.Arity} (E : Environment M Γ Δ) (S : Expr Δ) (B : Boundary M Γ) :
  B ∈ E.interpretBoundary (.of S) ↔ ∃ t, ⟨.sort, t⟩ ∈ E.interpret S ∧ B = .of t
  := by
  simp only [interpretBoundary, Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨_, hw, t, ht, rfl⟩
    obtain rfl := (Filler.mem_asSort _ _).mp ht
    use t, hw
  · rintro ⟨t, ht, rfl⟩
    use ⟨.sort, t⟩, ht, t, Part.mem_some t

/-- `eq l r` is interpreted as the equation of two sorts that `l` and `r` are
interpreted as, or as the equation of two elements of one sort that `l` and `r` are
interpreted as. -/
theorem mem_interpretBoundary_eq
    {Γ : M.Ob} {Δ : C.Arity} (E : Environment M Γ Δ) (l r : Expr Δ) (B : Boundary M Γ) :
  B ∈ E.interpretBoundary (.eq l r)
    ↔ (∃ tl tr, ⟨.sort, tl⟩ ∈ E.interpret l ∧ ⟨.sort, tr⟩ ∈ E.interpret r
          ∧ B = .eqSort tl tr)
      ∨ ∃ S tl tr, ⟨.of S, tl⟩ ∈ E.interpret l ∧ ⟨.of S, tr⟩ ∈ E.interpret r
          ∧ B = .eqElement S tl tr
  := by
  simp only [interpretBoundary, Part.mem_bind_iff]
  constructor
  · rintro ⟨⟨Bl, tl⟩, hl, wr, hr, hB⟩
    cases Bl with
    | sort =>
        left
        obtain ⟨tr, htr, rfl⟩ := (Part.mem_map_iff _).mp hB
        obtain rfl := (Filler.mem_asSort _ _).mp htr
        use tl, tr
    | of S =>
        right
        obtain ⟨tr, htr, rfl⟩ := (Part.mem_map_iff _).mp hB
        obtain rfl := (Filler.mem_asElement _ _ _).mp htr
        use S, tl, tr
    | _ => cases Part.notMem_none _ hB
  · rintro (⟨tl, tr, hl, hr, rfl⟩ | ⟨S, tl, tr, hl, hr, rfl⟩)
    · use ⟨.sort, tl⟩, hl, ⟨.sort, tr⟩, hr
      apply Part.mem_map
      apply Part.mem_some
    · use ⟨.of S, tl⟩, hl, ⟨.of S, tr⟩, hr
      apply Part.mem_map
      apply (Filler.mem_asElement _ _ _).mpr rfl

/-- The empty telescope is interpreted as the empty telescope. -/
theorem mem_interpretTelescope_nil
    {Γ : M.Ob} {Δ : C.Arity} (E : Environment M Γ Δ) (T : Telescope M Γ 1) :
  T ∈ E.interpretTelescope .nil ↔ T = ⟨.nil, .nil⟩
  := by
  apply Part.mem_some_iff

/-- A telescope with a first entry is interpreted by interpreting the entry's binding
telescope, then its boundary at the environment extended by the interpreted binding
decoration, then the remaining entries at the environment extended by the one
interpreted entry, whose type is any type equal to `Bind` of the interpreted binding
chain at the type of the interpreted boundary. -/
theorem mem_interpretTelescope_cons
    {Γ : M.Ob} {Δ α Ω : C.Arity} (E : Environment M Γ Δ)
    (bind : dTel Δ α) (boundary : Bd (Δ ⋈ α)) (rest : dTel (Δ ⋈ C.single α) Ω)
    (T : Telescope M Γ (C.single α ⋈ Ω)) :
  T ∈ E.interpretTelescope (.cons bind boundary rest)
    ↔ ∃ T₀ ∈ E.interpretTelescope bind,
        ∃ B ∈ (E.extend T₀.decoration).interpretBoundary boundary,
          ∃ (A : M.Ty Γ) (hA : A = T₀.chain.Bind B.ty),
            ∃ R ∈ (E.extend (Decoration.cons T₀.decoration B A hA .nil)).interpretTelescope rest,
              T = ⟨.cons A R.chain, .cons T₀.decoration B A hA R.decoration⟩
  := by
  simp only [interpretTelescope, Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨T₀, hT₀, B, hB, R, hR, rfl⟩
    use T₀, hT₀, B, hB, T₀.chain.Bind B.ty, rfl, R, hR
  · rintro ⟨T₀, hT₀, B, hB, A, rfl, R, hR, rfl⟩
    use T₀, hT₀, B, hB, R, hR

end Environment

end HrS
