import HigherRankSyntax.Initiality.Chain

/-!
# Semantic telescopes, values and environments

The semantic counterparts, in a model `M`, of the syntactic boundaries, decorated
telescopes and fillers.

* A `Boundary` over an object declares a sort, an element of a sort `S`, or one of
  the two equations; the type it declares is `U`, `El S`, `IdSort S S'` or
  `IdElement l r`.
* A `Decoration` of a chain records, for each type of the chain, a decorated binding
  chain and a boundary at its end, and that the type is `Bind` of that binding chain
  at the type the boundary declares. A `Telescope` is a chain together with a
  decoration.
* A `Filler` over an object is a boundary together with a term of its type.
* The `Value` of a slot is its binding telescope together with a filler over the end
  of that telescope.
* An `Environment` over an object assigns a value to every slot of an arity.

Everything reindexes along substitutions, functorially. Extending an environment by
a decoration keeps the values of the old slots, reindexed along the projection, and
gives the new slots their generic values, built from the generic term of the entry's
type read over the end of its binding chain by `unlam`.
-/

universe u

namespace HrS

variable {M : Structure.{u}}

/-! ### Boundaries -/

variable (M) in
/-- A semantic boundary over `Γ`, declaring a sort, an element of the sort `S`, the
equation of two sorts, or the equation of two elements of a sort. -/
inductive Boundary (Γ : M.Ob) : Type u
  | sort
  | of (S : M.Tm Γ (M.U Γ))
  | eqSort (S S' : M.Tm Γ (M.U Γ))
  | eqElement (S : M.Tm Γ (M.U Γ)) (l r : M.Tm Γ (M.El S))

namespace Boundary

/-- The type a boundary declares: `U`, `El S`, `IdSort S S'` or `IdElement l r`. -/
def ty {Γ : M.Ob} : Boundary M Γ → M.Ty Γ
  | .sort => M.U Γ
  | .of S => M.El S
  | .eqSort S S' => M.IdSort S S'
  | .eqElement _ l r => M.IdElement l r

/-- The boundary is one of the two equations `eqSort`, `eqElement`. -/
def IsEq {Γ : M.Ob} : Boundary M Γ → Prop
  | .eqSort _ _ => True
  | .eqElement _ _ _ => True
  | _ => False

/-- A boundary reindexed along `σ`: each sort and element in it reindexed along `σ`,
and transported along `U_subst` and `El_subst` to a sort and an element again. -/
def subst {Γ Δ : M.Ob} : Boundary M Γ → M.Sub Δ Γ → Boundary M Δ
  | .sort, _ => .sort
  | .of S, σ => .of (M.U_subst σ ▸ M.substTm S σ)
  | .eqSort S S', σ => .eqSort (M.U_subst σ ▸ M.substTm S σ) (M.U_subst σ ▸ M.substTm S' σ)
  | .eqElement S l r, σ =>
      .eqElement (M.U_subst σ ▸ M.substTm S σ) (M.El_subst S σ ▸ M.substTm l σ)
        (M.El_subst S σ ▸ M.substTm r σ)

/-- Reindexing the type a boundary declares gives the type the reindexed boundary
declares. -/
theorem subst_ty
    {Γ Δ : M.Ob} (B : Boundary M Γ) (σ : M.Sub Δ Γ) :
  M.substTy B.ty σ = (B.subst σ).ty
  := by
  cases B with
  | sort => apply M.U_subst
  | of S => apply M.El_subst
  | eqSort S S' => apply M.IdSort_subst
  | eqElement S l r => apply M.IdElement_subst

/-- Reindexing a boundary along a composite is reindexing it along each factor in
turn. -/
theorem subst_comp
    {Γ Δ Ξ : M.Ob} (B : Boundary M Γ) (σ : M.Sub Δ Γ) (θ : M.Sub Ξ Δ) :
  B.subst (M.comp σ θ) = (B.subst σ).subst θ
  := by
  cases B with
  | sort => rfl
  | of S =>
      apply congrArg of
      apply eq_of_heq (M.substTm_comp_heq ..)
  | eqSort S S' =>
      simp only [subst]
      congr 1 <;> apply eq_of_heq (M.substTm_comp_heq ..)
  | eqElement S l r =>
      simp only [subst]
      congr 1
      · apply eq_of_heq (M.substTm_comp_heq ..)
      · apply M.substTm_comp_heq
      · apply M.substTm_comp_heq

/-- Reindexing a boundary along the identity leaves it unchanged. -/
theorem subst_identity
    {Γ : M.Ob} (B : Boundary M Γ) :
  B.subst (M.identity Γ) = B
  := by
  cases B with
  | sort => rfl
  | of S =>
      apply congrArg of
      apply eq_of_heq (M.substTm_identity_heq ..)
  | eqSort S S' =>
      rw [subst]
      congr 1 <;> apply eq_of_heq (M.substTm_identity_heq ..)
  | eqElement S l r =>
      rw [subst]
      congr 1
      · apply eq_of_heq (M.substTm_identity_heq ..)
      · apply M.substTm_identity_heq
      · apply M.substTm_identity_heq

/-- A reindexed boundary is an equation exactly when the boundary is. -/
theorem isEq_subst
    {Γ Δ : M.Ob} (B : Boundary M Γ) (σ : M.Sub Δ Γ) :
  (B.subst σ).IsEq ↔ B.IsEq
  := by
  cases B <;> apply Iff.rfl

end Boundary

/-- A type `A` equal to `Bind` of a chain `b` at the type of a boundary `B`, reindexed
along `σ`, is `Bind` of `b` reindexed along `σ` at the type of `B` reindexed along the
lift of `σ` through `b`. -/
theorem Chain.Bind_subst_entry
    {Γ Δ : M.Ob} {α : C.Arity} {b : Chain M Γ α} {B : Boundary M b.last} {A : M.Ty Γ}
    (hA : A = b.Bind B.ty) (σ : M.Sub Δ Γ) :
  M.substTy A σ = (b.subst σ).Bind (B.subst (b.lift σ)).ty
  := by
  rw [← Boundary.subst_ty, ← Bind_subst, hA]

/-! ### Decorations and telescopes -/

variable (M) in
/-- A decoration of a chain. For each type `A` of the chain it records a decorated
binding chain `b` over the object before `A`, a boundary `B` at the end of `b`, and
that `A` is `Bind` of `b` at the type of `B`. -/
inductive Decoration : {Γ : M.Ob} → {Ω : C.Arity} → Chain M Γ Ω → Type u
  | nil {Γ : M.Ob} : Decoration (Chain.nil (Γ := Γ))
  | cons {Γ : M.Ob} {α Ω : C.Arity} {b : Chain M Γ α} (db : Decoration b)
      (B : Boundary M b.last) (A : M.Ty Γ) (hA : A = b.Bind B.ty)
      {c : Chain M (M.extend Γ A) Ω} (d : Decoration c) :
      Decoration (Chain.cons (α := α) A c)

/-- A decoration of a chain reindexed along `σ`: the binding decoration and the type of
each entry reindexed along `σ` lifted through the types before the entry, and its
boundary along that substitution lifted further through the entry's binding chain. -/
def Decoration.subst : {Γ Δ : M.Ob} → {Ω : C.Arity} → {c : Chain M Γ Ω} →
    Decoration M c → (σ : M.Sub Δ Γ) → Decoration M (c.subst σ)
  | _, _, _, _, .nil, _ => .nil
  | _, _, _, _, .cons (b := b) db B A hA d, σ =>
      .cons (db.subst σ) (B.subst (b.lift σ)) (M.substTy A σ) (Chain.Bind_subst_entry hA σ)
        (d.subst (M.lift A σ))

/-- Reindexing a decoration along a composite is reindexing it along each factor in
turn. The two sides decorate chains that are equal by `Chain.subst_comp`. -/
theorem Decoration.subst_comp :
    ∀ {Γ Δ Ξ : M.Ob} {Ω : C.Arity} {c : Chain M Γ Ω} (d : Decoration M c) (σ : M.Sub Δ Γ)
      (θ : M.Sub Ξ Δ),
      HEq (d.subst (M.comp σ θ)) ((d.subst σ).subst θ)
  | _, _, _, _, _, .nil, _, _ => HEq.rfl
  | _, _, _, _, _, .cons db B A hA d, σ, θ => by
      simp only [subst]
      congr 1
      · apply Chain.subst_comp
      · apply subst_comp db
      · apply HEq.trans _ (heq_of_eq (Boundary.subst_comp _ _ _))
        congr 1
        · rw [Chain.subst_comp]
        · apply Chain.lift_comp
      · apply M.substTy_comp
      · apply proof_irrel_heq
      · apply HEq.trans _ (heq_of_eq (Chain.subst_comp _ _ _))
        congr 1
        · rw [M.substTy_comp]
        · apply Structure.lift_comp
      · apply HEq.trans _ (subst_comp d _ _)
        congr 1
        · rw [M.substTy_comp]
        · apply Structure.lift_comp

/-- Reindexing a decoration along the identity leaves it unchanged. The two sides
decorate chains that are equal by `Chain.subst_identity`. -/
theorem Decoration.subst_identity :
    ∀ {Γ : M.Ob} {Ω : C.Arity} {c : Chain M Γ Ω} (d : Decoration M c),
      HEq (d.subst (M.identity Γ)) d
  | _, _, _, .nil => HEq.rfl
  | _, _, _, .cons db B A hA d => by
      rw [subst]
      congr 1
      · apply Chain.subst_identity
      · apply subst_identity db
      · apply HEq.trans _ (heq_of_eq (Boundary.subst_identity B))
        congr 1
        · rw [Chain.subst_identity]
        · apply Chain.lift_identity
      · apply M.substTy_identity
      · apply proof_irrel_heq
      · apply HEq.trans _ (heq_of_eq (Chain.subst_identity _))
        congr 1
        · rw [M.substTy_identity]
        · apply Structure.lift_identity
      · apply HEq.trans _ (subst_identity d)
        congr 1
        · rw [M.substTy_identity]
        · apply Structure.lift_identity

variable (M) in
/-- A semantic telescope over `Γ`: a chain of types together with a decoration of
it. -/
@[ext]
structure Telescope (Γ : M.Ob) (Ω : C.Arity) : Type u where
  /-- The chain of types. -/
  chain : Chain M Γ Ω
  /-- Its decoration. -/
  decoration : Decoration M chain

namespace Telescope

/-- A telescope reindexed along `σ`: its chain and its decoration reindexed. -/
def subst {Γ Δ : M.Ob} {Ω : C.Arity} (T : Telescope M Γ Ω) (σ : M.Sub Δ Γ) :
    Telescope M Δ Ω :=
  ⟨T.chain.subst σ, T.decoration.subst σ⟩

/-- Reindexing a telescope along a composite is reindexing it along each factor in
turn. -/
theorem subst_comp
    {Γ Δ Ξ : M.Ob} {Ω : C.Arity} (T : Telescope M Γ Ω) (σ : M.Sub Δ Γ) (θ : M.Sub Ξ Δ) :
  T.subst (M.comp σ θ) = (T.subst σ).subst θ
  := by
  apply Telescope.ext
  · apply Chain.subst_comp
  · apply Decoration.subst_comp

/-- Reindexing a telescope along the identity leaves it unchanged. -/
theorem subst_identity
    {Γ : M.Ob} {Ω : C.Arity} (T : Telescope M Γ Ω) :
  T.subst (M.identity Γ) = T
  := by
  apply Telescope.ext
  · apply Chain.subst_identity
  · apply Decoration.subst_identity

end Telescope

/-! ### Fillers, values and environments -/

variable (M) in
/-- A filler over `Γ`: a boundary together with a term of the type it declares. -/
@[ext]
structure Filler (Γ : M.Ob) : Type u where
  /-- The boundary. -/
  boundary : Boundary M Γ
  /-- A term of the type the boundary declares. -/
  tm : M.Tm Γ boundary.ty

/-- A filler reindexed along `σ`: its boundary and its term reindexed. -/
def Filler.subst {Γ Δ : M.Ob} (w : Filler M Γ) (σ : M.Sub Δ Γ) : Filler M Δ :=
  ⟨w.boundary.subst σ, w.boundary.subst_ty σ ▸ M.substTm w.tm σ⟩

/-- Reindexing a filler along a composite is reindexing it along each factor in
turn. -/
theorem Filler.subst_comp
    {Γ Δ Ξ : M.Ob} (w : Filler M Γ) (σ : M.Sub Δ Γ) (θ : M.Sub Ξ Δ) :
  w.subst (M.comp σ θ) = (w.subst σ).subst θ
  := by
  apply Filler.ext
  · apply Boundary.subst_comp
  · apply M.substTm_comp_heq

/-- Reindexing a filler along the identity leaves it unchanged. -/
theorem Filler.subst_identity
    {Γ : M.Ob} (w : Filler M Γ) :
  w.subst (M.identity Γ) = w
  := by
  apply Filler.ext
  · apply Boundary.subst_identity
  · apply M.substTm_identity_heq

variable (M) in
/-- The value of a slot of arity `α` over `Γ`: its binding telescope over `Γ` of
arity `α`, and a filler over the end of that telescope. -/
@[ext]
structure Value (Γ : M.Ob) (α : C.Arity) : Type u where
  /-- The telescope of entries the slot binds. -/
  binding : Telescope M Γ α
  /-- The filler, over the end of the binding telescope. -/
  filler : Filler M binding.chain.last

/-- A value reindexed along `σ`: its binding telescope reindexed along `σ`, and its
filler reindexed along the lift of `σ` through the binding chain. -/
def Value.subst {Γ Δ : M.Ob} {α : C.Arity} (v : Value M Γ α) (σ : M.Sub Δ Γ) :
    Value M Δ α :=
  ⟨v.binding.subst σ, v.filler.subst (v.binding.chain.lift σ)⟩

/-- Reindexing a value along a composite is reindexing it along each factor in
turn. -/
theorem Value.subst_comp
    {Γ Δ Ξ : M.Ob} {α : C.Arity} (v : Value M Γ α) (σ : M.Sub Δ Γ) (θ : M.Sub Ξ Δ) :
  v.subst (M.comp σ θ) = (v.subst σ).subst θ
  := by
  apply Value.ext
  · apply Telescope.subst_comp
  · apply HEq.trans _ (heq_of_eq (Filler.subst_comp _ _ _))
    simp only [subst]
    congr 1
    · rw [Telescope.subst_comp]
    · apply Chain.lift_comp

/-- Reindexing a value along the identity leaves it unchanged. -/
theorem Value.subst_identity
    {Γ : M.Ob} {α : C.Arity} (v : Value M Γ α) :
  v.subst (M.identity Γ) = v
  := by
  apply Value.ext
  · apply Telescope.subst_identity
  · apply HEq.trans _ (heq_of_eq (Filler.subst_identity _))
    simp only [subst]
    congr 1
    · rw [Telescope.subst_identity]
    · apply Chain.lift_identity

variable (M) in
/-- An environment over `Γ` for the arity `Δ`: a value over `Γ` for every slot of
`Δ`, of that slot's arity. -/
def Environment (Γ : M.Ob) (Δ : C.Arity) : Type u :=
  ∀ ⦃α : C.Arity⦄, Δ ∋ α → Value M Γ α

namespace Environment

/-- The environment over `Γ` for the unit arity, which has no slots. -/
def empty (Γ : M.Ob) : Environment M Γ 1 :=
  fun _ x => (C.unit_is_empty x).elim

/-- An environment reindexed along `σ`: every value reindexed along `σ`. -/
def subst {Γ Δ : M.Ob} {Φ : C.Arity} (E : Environment M Γ Φ) (σ : M.Sub Δ Γ) :
    Environment M Δ Φ :=
  fun _ x => (E x).subst σ

/-- Reindexing an environment along a composite is reindexing it along each factor in
turn. -/
theorem subst_comp
    {Γ Δ Ξ : M.Ob} {Φ : C.Arity} (E : Environment M Γ Φ)
    (σ : M.Sub Δ Γ) (θ : M.Sub Ξ Δ) :
  E.subst (M.comp σ θ) = (E.subst σ).subst θ
  := by
  funext _ x
  apply Value.subst_comp

end Environment

/-! ### Generic values and extension -/

/-- The generic value of the entry with binding decoration `db`, boundary `B` and type
`A = b.Bind B.ty`, over the extension by `A`: the binding telescope reindexed along the
projection, `B` reindexed along the lift of the projection through `b`, and the generic
term of `A` read over the end of the reindexed binding chain by `unlam`. -/
def Decoration.headValue {Γ : M.Ob} {α : C.Arity} {b : Chain M Γ α} (db : Decoration M b)
    (B : Boundary M b.last) (A : M.Ty Γ) (hA : A = b.Bind B.ty) :
    Value M (M.extend Γ A) α :=
  ⟨(Telescope.mk b db).subst (M.projection A),
    ⟨B.subst (b.lift (M.projection A)),
      (b.subst (M.projection A)).unlam
        (Chain.Bind_subst_entry hA (M.projection A) ▸ M.generic A)⟩⟩

/-- The generic value of an entry of type `A`, reindexed along the pair of `g` with a
term `t` of the type `A` reindexed along `g`, is the entry's binding telescope reindexed along
`g`, its boundary reindexed along the lift of `g` through the binding chain, and `t`
read over the end of the reindexed binding chain by `unlam`. -/
theorem Decoration.headValue_subst_pair
    {Γ Ξ : M.Ob} {α : C.Arity} {b : Chain M Γ α} (db : Decoration M b)
    (B : Boundary M b.last) (A : M.Ty Γ) (hA : A = b.Bind B.ty)
    (g : M.Sub Ξ Γ) (t : M.Tm Ξ (M.substTy A g)) :
  (headValue db B A hA).subst (M.pair g t)
    = ⟨(Telescope.mk b db).subst g,
        ⟨B.subst (b.lift g), (b.subst g).unlam (Chain.Bind_subst_entry hA g ▸ t)⟩⟩
  := by
  simp only [headValue, Value.subst]
  congr 1
  · rw [← Telescope.subst_comp, M.projection_pair]
  · simp only [Telescope.subst, Filler.subst]
    have hB : HEq ((B.subst (b.lift (M.projection A))).subst
        ((b.subst (M.projection A)).lift (M.pair g t))) (B.subst (b.lift g)) := by
      symm
      apply HEq.trans _ (heq_of_eq (Boundary.subst_comp _ _ _))
      congr 1
      · rw [← Chain.subst_comp, M.projection_pair]
      · apply HEq.trans _ (Chain.lift_comp _ _ _)
        rw [M.projection_pair]
    congr 1
    · rw [← Chain.subst_comp, M.projection_pair]
    · apply HEq.trans (eqRec_heq _ _)
      rw [Chain.unlam_subst]
      congr 1
      · rw [← Chain.subst_comp, M.projection_pair]
      · rw [Boundary.subst_ty]
        congr 1
        rw [← Chain.subst_comp, M.projection_pair]
      · apply HEq.trans (eqRec_heq _ _)
        symm
        apply HEq.trans (eqRec_heq _ _)
        symm
        apply HEq.trans _ (M.generic_pair g t)
        congr 1
        · symm
          apply Chain.Bind_subst_entry hA
        · apply eqRec_heq

/-- The generic value of an entry, reindexed along the lift of `σ` through the entry's
type, is the generic value of the entry reindexed along `σ`. -/
theorem Decoration.headValue_subst_lift
    {Γ Δ : M.Ob} {α : C.Arity} {b : Chain M Γ α} (db : Decoration M b)
    (B : Boundary M b.last) (A : M.Ty Γ) (hA : A = b.Bind B.ty) (σ : M.Sub Δ Γ) :
  (headValue db B A hA).subst (M.lift A σ)
    = headValue (db.subst σ) (B.subst (b.lift σ)) (M.substTy A σ)
        (Chain.Bind_subst_entry hA σ)
  := by
  rw [Structure.lift, headValue_subst_pair]
  simp only [headValue]
  congr 1
  · apply Telescope.subst_comp
  · simp only [Telescope.subst]
    have hB : HEq (B.subst (b.lift (M.comp σ (M.projection (M.substTy A σ)))))
        ((B.subst (b.lift σ)).subst ((b.subst σ).lift (M.projection (M.substTy A σ)))) := by
      apply HEq.trans _ (heq_of_eq (Boundary.subst_comp _ _ _))
      congr 1
      · rw [Chain.subst_comp]
      · apply Chain.lift_comp
    congr 1
    · rw [Chain.subst_comp]
    · congr 1
      · rw [Chain.subst_comp]
      · congr 1
        rw [Chain.subst_comp]
      · apply HEq.trans (eqRec_heq _ _)
        apply HEq.trans (eqRec_heq _ _)
        symm
        apply eqRec_heq

/-- The generic value of each slot of a decoration, over the end of its chain: the
generic value of the slot's entry, reindexed along the projections off the entries
after it. -/
def Decoration.slot : {Γ : M.Ob} → {Ω : C.Arity} → {c : Chain M Γ Ω} → Decoration M c →
    {β : C.Arity} → Ω ∋ β → Value M c.last β
  | _, _, _, .nil, _, x => (C.unit_is_empty x).elim
  | _, _, _, @Decoration.cons _ _ α Ω _ db B A hA c d, _, x =>
      match C.split (C.single α) Ω x with
      | .inl z => C.single_arity z ▸ (Decoration.headValue db B A hA).subst c.projection
      | .inr y => d.slot y

/-- An environment over `Γ` extended by a decoration of a chain over `Γ`: over the end
of the chain, the old slots keep their values reindexed along the chain's projection,
and the new slots get their generic values. -/
def Environment.extend {Γ : M.Ob} {Δ Ω : C.Arity} (E : Environment M Γ Δ)
    {c : Chain M Γ Ω} (d : Decoration M c) : Environment M c.last (Δ ⋈ Ω) :=
  fun _ x =>
    match C.split Δ Ω x with
    | .inl y => (E y).subst c.projection
    | .inr z => d.slot z

/-- The first slot of a decoration has the generic value of its first entry,
reindexed along the projection off the rest. -/
theorem Decoration.slot_head
    {Γ : M.Ob} {α Ω : C.Arity} {b : Chain M Γ α} (db : Decoration M b)
    (B : Boundary M b.last) (A : M.Ty Γ) (hA : A = b.Bind B.ty)
    {c : Chain M (M.extend Γ A) Ω} (d : Decoration M c) :
  (cons db B A hA d).slot (C.inl (C.singleSlot α))
    = (headValue db B A hA).subst c.projection
  := by
  simp only [slot, C.split_inl]

/-- The slot `inr y` of a decoration with a first entry has the generic value of `y`
in the rest of the decoration. -/
theorem Decoration.slot_tail
    {Γ : M.Ob} {α Ω β : C.Arity} {b : Chain M Γ α} (db : Decoration M b)
    (B : Boundary M b.last) (A : M.Ty Γ) (hA : A = b.Bind B.ty)
    {c : Chain M (M.extend Γ A) Ω} (d : Decoration M c) (y : Ω ∋ β) :
  (cons db B A hA d).slot (C.inr y) = d.slot y
  := by
  simp only [slot, C.split_inr]

/-- An old slot of an extended environment keeps its value, reindexed along the
chain's projection. -/
theorem Environment.extend_inl
    {Γ : M.Ob} {Δ Ω β : C.Arity} (E : Environment M Γ Δ) {c : Chain M Γ Ω}
    (d : Decoration M c) (y : Δ ∋ β) :
  E.extend d (C.inl y) = (E y).subst c.projection
  := by
  simp only [extend, C.split_inl]

/-- A new slot of an extended environment has its generic value in the decoration. -/
theorem Environment.extend_inr
    {Γ : M.Ob} {Δ Ω β : C.Arity} (E : Environment M Γ Δ) {c : Chain M Γ Ω}
    (d : Decoration M c) (z : Ω ∋ β) :
  E.extend d (C.inr z) = d.slot z
  := by
  simp only [extend, C.split_inr]

/-- Generic values commute with reindexing: reindexing the generic value of a slot
along the lift of `σ` through the chain gives the generic value of that slot in the
reindexed decoration. -/
theorem Decoration.slot_subst :
    ∀ {Γ Δ : M.Ob} {Ω : C.Arity} {c : Chain M Γ Ω} (d : Decoration M c) (σ : M.Sub Δ Γ)
      {β : C.Arity} (z : Ω ∋ β),
      (d.slot z).subst (c.lift σ) = (d.subst σ).slot z
  | _, _, _, _, .nil, _, _, z => (C.unit_is_empty z).elim
  | _, _, _, _, .cons db B A hA d, σ, _, z => by
      obtain ⟨x, rfl⟩ | ⟨y, rfl⟩ := C.cover _ _ z
      · obtain rfl := C.single_arity x
        obtain rfl := C.single_slot_unique x
        simp only [subst, slot_head, Chain.lift, Chain.last, Chain.subst]
        rw [← Value.subst_comp, Chain.projection_lift, Value.subst_comp, headValue_subst_lift]
      · simp only [subst, slot_tail, Chain.subst]
        apply slot_subst

/-- Extending an environment commutes with reindexing: extending the reindexed
environment by the reindexed decoration is reindexing the extended environment along
the lift of `σ` through the chain. -/
theorem Environment.extend_subst
    {Γ Δ : M.Ob} {Φ Ω : C.Arity} (E : Environment M Γ Φ) {c : Chain M Γ Ω}
    (d : Decoration M c) (σ : M.Sub Δ Γ) :
  (E.subst σ).extend (d.subst σ) = (E.extend d).subst (c.lift σ)
  := by
  funext _ x
  obtain ⟨y, rfl⟩ | ⟨z, rfl⟩ := C.cover _ _ x
  · simp only [subst, extend_inl]
    rw [← Value.subst_comp, ← Value.subst_comp, Chain.projection_lift]
  · simp only [subst, extend_inr]
    symm
    apply Decoration.slot_subst

end HrS
