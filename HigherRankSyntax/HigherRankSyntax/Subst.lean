import HigherRankSyntax.Expr

/-!
# Substitution

`Subst Δ Γ` maps each `Δ`-slot of arity `α` to an expression over `Γ ⋈ α`.

`Subst.act σ Φ` applies `σ : Subst Δ (Γ ⋈ Ξ)` to an expression in
`Expr (Γ ⋈ Δ ⋈ Φ)`, producing an expression in `Expr (Γ ⋈ Ξ ⋈ Φ)`.

`Subst.threeway` classifies a head slot of `Γ ⋈ Δ ⋈ Ξ` as coming from
`Γ`, `Δ`, or `Ξ`.
-/

/-- A substitution from `Δ` into `Γ`: an expression over `Γ ⋈ α` for each slot
of `Δ` of arity `α`. -/
abbrev Subst (Δ Γ : C.Arity) :=
  ∀ ⦃α : C.Arity⦄, Δ ∋ α → Expr (Γ ⋈ α)

/-- The identity substitution on `Γ`, sending each slot to its η-expansion. -/
def Subst.id (Γ : C.Arity) : Subst Γ Γ :=
  (fun ⦃_⦄ p => Expr.η p)

/-- The substitution sending each slot `x` to the η-expansion of `ρ x`. -/
def Subst.ofRenaming {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) : Subst Γ Δ :=
  fun ⦃_⦄ x => Expr.η (ρ x)

/-- The origin of a slot of `Γ ⋈ Δ ⋈ Ξ`: the prefix `Γ`, the substitution
domain `Δ`, or the current depth `Ξ`. -/
inductive LeftMiddleRight (Γ Δ Ξ α : C.Arity) : Type where
  /-- The slot belongs to the prefix `Γ`. -/
  | left (q : Γ ∋ α)
  /-- The slot belongs to the substitution domain `Δ`. -/
  | middle (q : Δ ∋ α)
  /-- The slot belongs to the current depth `Ξ`. -/
  | right (q : Ξ ∋ α)

/-- The origin of `p : Γ ⋈ Δ ⋈ Ξ ∋ α`: `.left x` for `p = C.inl (C.inl x)`,
`.middle y` for `p = C.inl (C.inr y)`, `.right z` for `p = C.inr z`. -/
def Subst.threeway {Γ Δ Ξ : C.Arity}
    {α : C.Arity} (p : Γ ⋈ Δ ⋈ Ξ ∋ α) :
    LeftMiddleRight Γ Δ Ξ α :=
  C.copair (Γ ⋈ Δ) Ξ _
    (fun q => C.copair Γ Δ _ (fun x => .left x) (fun y => .middle y) q)
    (fun q => .right q) p

/-- The slot of `Γ ⋈ Δ ⋈ Ξ` with a given origin: `C.inl (C.inl x)`,
`C.inl (C.inr x)` or `C.inr x`. -/
def Subst.reinject {Γ Δ Ξ : C.Arity} {α : C.Arity} :
  LeftMiddleRight Γ Δ Ξ α → Γ ⋈ Δ ⋈ Ξ ∋ α
  | .left x => C.inl (C.inl x)
  | .middle x => C.inl (C.inr x)
  | .right x => C.inr x

/-- Every slot of `Γ ⋈ Δ ⋈ Ξ` is `Subst.reinject` of some origin. -/
theorem Subst.isReinject {Γ Δ Ξ : C.Arity} {α : C.Arity}
    (x : Γ ⋈ Δ ⋈ Ξ ∋ α) :
  ∃ y : LeftMiddleRight Γ Δ Ξ α, x = reinject y
  := by
  rcases C.cover (Γ ⋈ Δ) Ξ x with ⟨y, rfl⟩ | ⟨x, rfl⟩
  · rcases C.cover Γ Δ y with ⟨w, rfl⟩ | ⟨z, rfl⟩
    · exists .left w
    · exists .middle z
  · exists .right x

/-- The origin of `C.inr x` with `x : Ξ ∋ α` is `.right x`. -/
@[simp] theorem Subst.threeway_right {Γ Δ Ξ : C.Arity}
    {α : C.Arity} (x : Ξ ∋ α) :
  threeway (Γ := Γ) (Δ := Δ) (C.inr x) = .right x
  := by
  rw [threeway, C.copair_apply_inr]

/-- The origin of `C.inl (C.inr x)` with `x : Δ ∋ α` is `.middle x`. -/
@[simp] theorem Subst.threeway_middle {Γ Δ Ξ : C.Arity}
    {α : C.Arity} (x : Δ ∋ α) :
  threeway (Γ := Γ) (Ξ := Ξ) (C.inl (C.inr x)) = .middle x
  := by
  rw [threeway, C.copair_apply_inl, C.copair_apply_inr]

/-- The origin of `C.inl (C.inl x)` with `x : Γ ∋ α` is `.left x`. -/
@[simp] theorem Subst.threeway_left {Γ Δ Ξ : C.Arity}
    {α : C.Arity} (x : Γ ∋ α) :
  threeway (Δ := Δ) (Ξ := Ξ) (C.inl (C.inl x)) = .left x
  := by
  rw [threeway, C.copair_apply_inl, C.copair_apply_inl]

/-- The substitution `Subst α (Δ ⋈ α)` sending each slot `i` to the
η-expansion of `C.inr i`. -/
def Subst.instId (Δ α : C.Arity) : Subst α (Δ ⋈ α) :=
  fun ⦃_⦄ i => Expr.η (C.inr i)

/-- The substitution out of `Γ ⋈ Δ` sending `C.inl y` to `σ y` and `C.inr z` to
`θ z`. -/
def Subst.copair {Γ Δ Ω : C.Arity} (σ : Subst Γ Ω) (θ : Subst Δ Ω) :
    Subst (Γ ⋈ Δ) Ω :=
  fun ⦃Λ⦄ x =>
    C.copair Γ Δ (Expr (Ω ⋈ Λ)) (fun y => σ y) (fun z => θ z) x

@[simp] theorem Subst.copair_inl {Γ Δ Ω : C.Arity}
    (σ : Subst Γ Ω) (θ : Subst Δ Ω) {Λ : C.Arity} (x : Γ ∋ Λ) :
  copair σ θ (C.inl x) = σ x
  := by
  apply C.copair_apply_inl

@[simp] theorem Subst.copair_inr {Γ Δ Ω : C.Arity}
    (σ : Subst Γ Ω) (θ : Subst Δ Ω) {Λ : C.Arity} (x : Δ ∋ Λ) :
  copair σ θ (C.inr x) = θ x
  := by
  apply C.copair_apply_inr

/-- `Subst.copair σ θ` restricted to the `Γ`-slots is `σ`. -/
theorem Subst.copair_left {Γ Δ Ω : C.Arity} (σ : Subst Γ Ω) (θ : Subst Δ Ω) :
  (fun ⦃α⦄ (y : Γ ∋ α) => copair σ θ (C.inl y)) = σ
  := by
  funext α y
  apply copair_inl

/-- `Subst.copair σ θ` restricted to the `Δ`-slots is `θ`. -/
theorem Subst.copair_right {Γ Δ Ω : C.Arity} (σ : Subst Γ Ω) (θ : Subst Δ Ω) :
  (fun ⦃α⦄ (z : Δ ∋ α) => copair σ θ (C.inr z)) = θ
  := by
  funext α z
  apply copair_inr

/-- A substitution out of `Γ ⋈ Δ` is the copair of its restrictions to `Γ` and
to `Δ`. -/
theorem Subst.copair_eta {Γ Δ Ω : C.Arity} (κ : Subst (Γ ⋈ Δ) Ω) :
  copair (fun ⦃α⦄ (y : Γ ∋ α) => κ (C.inl y))
      (fun ⦃α⦄ (z : Δ ∋ α) => κ (C.inr z))
    = κ
  := by
  funext α x
  rcases C.cover Γ Δ x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · apply copair_inl
  · apply copair_inr

/-- The substitution out of `C.single α ⋈ 1` sending its one slot to `t`. -/
def Subst.single {Δ α : C.Arity} (t : Expr (Δ ⋈ α)) : Subst (C.single α ⋈ 1) Δ :=
  fun ⦃β⦄ x =>
    C.copair (C.single α) 1 (Expr (Δ ⋈ β))
      (fun y => cast (congrArg (fun γ => Expr (Δ ⋈ γ)) (C.single_arity y).symm) t)
      (fun z => (C.unit_is_empty z).elim) x

@[simp] theorem Subst.single_head {Δ α : C.Arity} (t : Expr (Δ ⋈ α)) :
  single t (C.inl (C.singleSlot α)) = t
  := by
  rw [single, C.copair_apply_inl, cast_eq]

/-- A substitution out of `C.single α ⋈ 1` is `Subst.single` of its value on
the one slot. -/
theorem Subst.single_eta {Δ α : C.Arity} (τ : Subst (C.single α ⋈ 1) Δ) :
  single (τ (C.inl (C.singleSlot α))) = τ
  := by
  funext β x
  rcases C.cover (C.single α) 1 x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · obtain rfl := C.single_arity y
    rw [C.single_slot_unique y]
    apply single_head
  · exact (C.unit_is_empty z).elim

/-! ### The substitution action -/

/-- The action of `σ : Subst Δ (Γ ⋈ Ξ)` at depth `Φ`, from `Expr (Γ ⋈ Δ ⋈ Φ)` to
`Expr (Γ ⋈ Ξ ⋈ Φ)`: an application headed by `C.inl (C.inr z)` with `z : Δ ∋ α`
becomes `σ z` with its `α`-slots substituted by the acted arguments; an
application with any other head keeps the head and acts on the arguments. -/
def Subst.act {Γ Δ Ξ : C.Arity}
      (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity) :
    Expr (Γ ⋈ Δ ⋈ Φ) → Expr (Γ ⋈ Ξ ⋈ Φ)
  | .ap (α := α) x args =>
      match threeway x with
      | .right x =>
          .ap (C.inr x) (fun {_} i => σ.act (Φ ⋈ _) (args i))
      | .middle z =>
          act (Γ := Γ ⋈ Ξ)
            (fun {_} i => σ.act (Φ ⋈ _) (args i)) 1 (σ z)
      | .left z =>
          .ap (C.inl (C.inl z)) (fun {_} i => σ.act (Φ ⋈ _) (args i))
termination_by e => (Δ, (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ))
decreasing_by
  · exact Prod.Lex.right _ (Expr.Subterm.of_arg x args i)
  · exact Prod.Lex.right _ (Expr.Subterm.of_arg x args i)
  · exact Prod.Lex.left _ _ ⟨z⟩
  · exact Prod.Lex.right _ (Expr.Subterm.of_arg x args i)

/-- The composite of `σ` and `θ`, sending `x : Δ ∋ β` to `θ` acting at depth `β`
on `σ x`. -/
def Subst.comp {Γ Δ Θ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Θ))
    (θ : Subst Θ (Γ ⋈ Ξ)) :
  Subst Δ (Γ ⋈ Ξ) :=
  (fun ⦃β⦄ x => θ.act β (σ x))
