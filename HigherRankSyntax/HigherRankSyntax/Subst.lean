import HigherRankSyntax.Expr

/-!
# Substitution, instantiation, and the Kleisli extension

Slot classification, the walkers `inst.aux` and `lift.aux`, their per-case
unfolders, the public wrappers `Inst.act`, `Subst.lift`, and `Subst.act`, and
the categorical operations (`Renaming.toSubst`, `Renaming.preSubst`,
`Subst.postRen`, `Subst.comp`).

Each head slot is classified by `classify` into either a Γ-slot (`XPos.base`,
the weakening of some `p : Γ ∋ α` through τ) or a τ-binder (`XPos.ext`).  The
slot-correspondence witness lives in the inductive's index, so pattern matching
on `classify`'s result yields it definitionally — no `Eq.rec`.

`lift.aux` walks `Expr (Γ ⋈* τ)`; the Γ-slot case substitutes via σ and uses
`inst.aux` directly on σ's image, threading the target weakening as a renaming.
`inst.aux` walks `Expr ((Δ ⋈ α) ⋈* τ)`, carries a renaming `ρ : Δ →ʳ Ξ`, and
maps Δ-slots through `ρ` during traversal.

## Notations

  - `Γ →ˢ Δ` is the type of substitutions from `Γ` to `Δ`.
  - `𝟙ˢ` is the identity substitution.
  - `σ ∘ˢˢ θ` is Kleisli composition; `ρ ∘ʳˢ σ` and `σ ∘ˢʳ ρ` are pre- and
    post-composition with a renaming.
  - `Γ ↪ˢ α` and `Γ ↪ˢ* τ` are the canonical weakenings.
  - `σ ⇑ˢ α` and `σ ⇑ˢ* τ` extend a substitution through a fresh binder /
    list of binders.
  - `⟦σ⟧ˢ e` is the action of `σ` on an expression (parallels `⟦ρ⟧ʳ e`).
-/


/-! ## Substitutions and instantiations -/

/-- A substitution from `Γ` to `Δ`: an arity-preserving map from slots to expressions. -/
def Subst {C : Carrier} (Γ Δ : Shape C) : Type :=
  ∀ {α : C.Arity}, (Γ ∋ α) → Expr (Δ ⋈ α)

/-- Notation `Γ →ˢ Δ` for substitutions from `Γ` to `Δ`. -/
infixr:25 " →ˢ " => Subst

/-- An instantiation of an α-binder above `Γ`. -/
abbrev Inst {C : Carrier} (α : C.Arity) (Γ : Shape C) : Type :=
  (i : C.Binder α) → Expr (Γ ⋈ i.arity)

/-! ## Slot classification -/

/-- The slot at depth `|τ_above|` in `Γ ⋈* (τ_above ++ β :: τ_below)` corresponding to
binder `i` of `β`.  Iterates `.there` over `τ_above` from `.here i`. -/
def tauSlot {C : Carrier} (Γ : Shape C) :
    (τ_above : List C.Arity) → (β : C.Arity) → (τ_below : List C.Arity) →
    (i : C.Binder β) → (Γ ⋈* (τ_above ++ β :: τ_below)) ∋ i.arity
  | [],        _, _, i => .here i
  | _ :: rest, β, τ_below, i => .there (tauSlot Γ rest β τ_below i)

/-- Position of a slot in `Γ ⋈* τ` at arity `α`: a Γ-slot weakened through τ, or a
τ-binder. -/
inductive XPos {C : Carrier} (Γ : Shape C) :
    {τ : List C.Arity} → {α : C.Arity} → SlotAt (Γ ⋈* τ) α → Type where
  | base : {τ : List C.Arity} → {α : C.Arity} → (p : Γ ∋ α) →
           XPos Γ ((Γ ↪ʳ* τ) p)
  | ext  : {τ_above : List C.Arity} → {β : C.Arity} → {τ_below : List C.Arity} →
           (i : C.Binder β) →
           XPos Γ (τ := τ_above ++ β :: τ_below) (tauSlot Γ τ_above β τ_below i)

/-- Classify a slot in an iterated extension. -/
def classify {C : Carrier} {Γ : Shape C} :
    (τ : List C.Arity) → {α : C.Arity} → (p : (Γ ⋈* τ) ∋ α) → XPos Γ p
  | [],       _, p        => XPos.base p
  | _ :: _,   _, .here i  => XPos.ext (τ_above := []) i
  | β :: τ',  _, .there p =>
      match classify τ' p with
      | XPos.base q => XPos.base q
      | XPos.ext (τ_above := ta) (β := b) (τ_below := tb) j =>
          XPos.ext (τ_above := β :: ta) (β := b) (τ_below := tb) j

/-- Classifying a Γ-slot weakened through τ recovers the original Γ-slot. -/
@[simp] theorem classify_weakenList {C : Carrier} {Γ : Shape C}
    (τ : List C.Arity) {α : C.Arity} (p : Γ ∋ α) :
    classify τ ((Γ ↪ʳ* τ) p) = XPos.base p := by
  induction τ with
  | nil => rfl
  | cons β rest ih =>
    show classify (β :: rest) (.there ((Γ ↪ʳ* rest) p)) = XPos.base p
    simp [classify, ih]

/-- Classifying a `tauSlot` recovers the corresponding `XPos.ext`. -/
@[simp] theorem classify_tauSlot {C : Carrier} {Γ : Shape C}
    (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
    (i : C.Binder β) :
    classify (τ_above ++ β :: τ_below) (tauSlot Γ τ_above β τ_below i)
      = XPos.ext (τ_above := τ_above) (β := β) (τ_below := τ_below) i := by
  induction τ_above with
  | nil => rfl
  | cons a rest ih =>
    show classify (a :: (rest ++ β :: τ_below))
           (.there (tauSlot Γ rest β τ_below i))
         = XPos.ext (τ_above := a :: rest) (β := β) (τ_below := τ_below) i
    simp [classify, ih]

/-! ## Walkers -/

/-- α-instantiation walker.  Walks `e : Expr ((Δ ⋈ α) ⋈* τ)` by classifying each head:
τ-binder rebuilds the same `tauSlot` at the Ξ-side; Δ-slots are mapped through `ρ` and
then weakened through τ; α-binders plug `ι j` and recurse at smaller arity. -/
def inst.aux {C : Carrier} {Δ Ξ : Shape C} {α : C.Arity}
    (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
    (τ : List C.Arity) (e : Expr ((Δ ⋈ α) ⋈* τ)) : Expr (Ξ ⋈* τ) :=
  match e with
  | .apply p args =>
      match classify τ p with
      | XPos.ext (τ_above := ta) (β := b) (τ_below := tb) i =>
          Expr.apply (tauSlot Ξ ta b tb i)
            (fun k => inst.aux ρ ι (k.arity :: (ta ++ b :: tb)) (args k))
      | XPos.base q =>
          match q with
          | .there r =>
              Expr.apply ((Ξ ↪ʳ* τ) (ρ r))
                (fun k => inst.aux ρ ι (k.arity :: τ) (args k))
          | .here j =>
              inst.aux (Ξ ↪ʳ* τ)
                (fun k => inst.aux ρ ι (k.arity :: τ) (args k)) [] (ι j)
termination_by (⟨α, _, e⟩ : (_ : C.Arity) ×' Σ Γ : Shape C, Expr Γ)
decreasing_by
  -- ext args descent
  · exact PSigma.Lex.right _ (Expr.Subterm.of_arg _ _ _)
  -- .there args descent
  · exact PSigma.Lex.right _ (Expr.Subterm.of_arg _ _ _)
  -- .here args descent
  · exact PSigma.Lex.right _ (Expr.Subterm.of_arg _ _ _)
  -- α decreases (j.arity ≺ α)
  · exact PSigma.Lex.left _ _ ⟨j, rfl⟩

/-! ## η-fillers and per-case unfolders for `inst.aux` -/

/-- Canonical η-fillers for an α-binder over a shape with α at the top.  Each binder
position `i` becomes the η-expansion of the bound variable `.here i`. -/
def η_fillers {C : Carrier} (Δ : Shape C) (α : C.Arity) : Inst α (Δ ⋈ α) :=
  fun i => Expr.η (.here i)

@[simp] theorem inst_aux_ext_eq {C : Carrier} {Δ Ξ : Shape C} {α : C.Arity}
    (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
    (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
    (i : C.Binder β)
    (args : (j : C.Binder i.arity) →
      Expr ((Δ ⋈ α) ⋈* (τ_above ++ β :: τ_below) ⋈ j.arity)) :
    inst.aux ρ ι (τ_above ++ β :: τ_below)
      (Expr.apply (tauSlot (Δ ⋈ α) τ_above β τ_below i) args)
      =
    Expr.apply (tauSlot Ξ τ_above β τ_below i)
      (fun j => inst.aux ρ ι (j.arity :: (τ_above ++ β :: τ_below)) (args j)) := by
  delta inst.aux
  change inst.aux._unary (C := C)
      ⟨Δ, ⟨Ξ, ⟨α, ⟨ρ, ⟨ι, ⟨τ_above ++ β :: τ_below,
        Expr.apply (tauSlot (Δ ⋈ α) τ_above β τ_below i) args⟩⟩⟩⟩⟩⟩ = _
  rw [inst.aux._unary.eq_1]
  simp [classify_tauSlot]

@[simp] theorem inst_aux_base_there_eq {C : Carrier} {Δ Ξ : Shape C} {α : C.Arity}
    (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
    (τ : List C.Arity) {α_r : C.Arity} (r : Δ ∋ α_r)
    (args : (j : C.Binder α_r) → Expr ((Δ ⋈ α) ⋈* τ ⋈ j.arity)) :
    inst.aux ρ ι τ
      (Expr.apply (((Δ ⋈ α) ↪ʳ* τ) (.there r)) args)
      =
    Expr.apply ((Ξ ↪ʳ* τ) (ρ r))
      (fun j => inst.aux ρ ι (j.arity :: τ) (args j)) := by
  delta inst.aux
  change inst.aux._unary (C := C)
      ⟨Δ, ⟨Ξ, ⟨α, ⟨ρ, ⟨ι, ⟨τ,
        Expr.apply (((Δ ⋈ α) ↪ʳ* τ) (.there r)) args⟩⟩⟩⟩⟩⟩ = _
  rw [inst.aux._unary.eq_1]
  simp [classify_weakenList]

@[simp] theorem inst_aux_base_here_eq {C : Carrier} {Δ Ξ : Shape C} {α : C.Arity}
    (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
    (τ : List C.Arity) (j : C.Binder α)
    (args : (k : C.Binder j.arity) → Expr ((Δ ⋈ α) ⋈* τ ⋈ k.arity)) :
    inst.aux ρ ι τ
      (Expr.apply (((Δ ⋈ α) ↪ʳ* τ) (.here j)) args)
      =
    inst.aux (Ξ ↪ʳ* τ)
      (fun k => inst.aux ρ ι (k.arity :: τ) (args k)) [] (ι j) := by
  delta inst.aux
  change inst.aux._unary (C := C)
      ⟨Δ, ⟨Ξ, ⟨α, ⟨ρ, ⟨ι, ⟨τ,
        Expr.apply (((Δ ⋈ α) ↪ʳ* τ) (.here j)) args⟩⟩⟩⟩⟩⟩ = _
  rw [inst.aux._unary.eq_1]
  simp [classify_weakenList]

/-- Kleisli extension walker.  Walks `e : Expr (Γ ⋈* τ)` by classifying each head:
τ-binder rebuilds; Γ-slot substitutes via σ and threads the target weakening through
`inst.aux`. -/
def lift.aux {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
    (τ : List C.Arity) (e : Expr (Γ ⋈* τ)) : Expr (Δ ⋈* τ) :=
  match e with
  | .apply (α := α_h) p args =>
      match classify τ p with
      | XPos.ext (τ_above := ta) (β := b) (τ_below := tb) i =>
          Expr.apply (tauSlot Δ ta b tb i)
            (fun k => lift.aux σ (k.arity :: (ta ++ b :: tb)) (args k))
      | XPos.base q =>
          inst.aux (Δ ↪ʳ* τ)
            (fun k => lift.aux σ (k.arity :: τ) (args k)) [] (σ q)
termination_by (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by
  all_goals exact Expr.Subterm.of_arg _ _ _

@[simp] theorem lift_aux_ext_eq {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
    (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
    (i : C.Binder β)
    (args : (j : C.Binder i.arity) →
      Expr (Γ ⋈* (τ_above ++ β :: τ_below) ⋈ j.arity)) :
    lift.aux σ (τ_above ++ β :: τ_below)
      (Expr.apply (tauSlot Γ τ_above β τ_below i) args)
      =
    Expr.apply (tauSlot Δ τ_above β τ_below i)
      (fun j => lift.aux σ (j.arity :: (τ_above ++ β :: τ_below)) (args j)) := by
  delta lift.aux
  change lift.aux._unary (C := C) σ
      ⟨τ_above ++ β :: τ_below,
        Expr.apply (tauSlot Γ τ_above β τ_below i) args⟩ = _
  rw [lift.aux._unary.eq_1]
  simp [classify_tauSlot]

@[simp] theorem lift_aux_base_eq {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
    (τ : List C.Arity) {α : C.Arity} (q : Γ ∋ α)
    (args : (j : C.Binder α) → Expr (Γ ⋈* τ ⋈ j.arity)) :
    lift.aux σ τ
      (Expr.apply ((Γ ↪ʳ* τ) q) args)
      =
    inst.aux (Δ ↪ʳ* τ)
      (fun j => lift.aux σ (j.arity :: τ) (args j)) [] (σ q) := by
  delta lift.aux
  change lift.aux._unary (C := C) σ
      ⟨τ, Expr.apply ((Γ ↪ʳ* τ) q) args⟩ = _
  rw [lift.aux._unary.eq_1]
  simp [classify_weakenList]

/-! ## Public wrappers -/

/-- α-instantiation: replace the α-binder of `Δ ⋈ α` by `ι`. -/
def Inst.act {C : Carrier} {α : C.Arity} {Δ : Shape C}
    (ι : Inst α Δ) (e : Expr (Δ ⋈ α)) : Expr Δ :=
  inst.aux 𝟙ʳ ι [] e

/-- Kleisli extension at a single α-binder. -/
def Subst.lift {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
    {α : C.Arity} (e : Expr (Γ ⋈ α)) : Expr (Δ ⋈ α) :=
  lift.aux σ [α] e

/-- Action of a substitution on an expression without a top binder. -/
def Subst.act {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ) (e : Expr Γ) : Expr Δ :=
  lift.aux σ [] e

/-- Action of a substitution on an expression: `⟦ σ ⟧ˢ e`. -/
notation:60 "⟦" σ "⟧ˢ " e:61 => Subst.act σ e

/-! ## Categorical operations: substitution and renaming compositions -/

/-- Embed a renaming as a substitution: send each slot through `ρ` and η-expand. -/
def Renaming.toSubst {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ) : Subst Γ Δ :=
  fun p => Expr.η (ρ p)

/-- The identity substitution: η-expansion of every slot. -/
def Subst.id {C : Carrier} (Γ : Shape C) : Subst Γ Γ :=
  fun p => Expr.η p

/-- The identity substitution on a shape. -/
notation "𝟙ˢ" => Subst.id _

/-- Weakening as a substitution: insert a fresh α-binder. -/
def Subst.weaken {C : Carrier} (Γ : Shape C) (α : C.Arity) : Subst Γ (Γ ⋈ α) :=
  Renaming.toSubst (Renaming.weaken Γ α)

@[inherit_doc Subst.weaken]
notation:65 Γ " ↪ˢ " α => Subst.weaken Γ α

/-- Iterated weakening as a substitution. -/
def Subst.weakenList {C : Carrier} (Γ : Shape C) (τ : List C.Arity) :
    Subst Γ (Γ ⋈* τ) :=
  Renaming.toSubst (Γ ↪ʳ* τ)

@[inherit_doc Subst.weakenList]
notation:65 Γ " ↪ˢ* " τ => Subst.weakenList Γ τ

/-- Pre-compose a substitution by a renaming. -/
def Renaming.preSubst {C : Carrier} {Γ Γ' Δ : Shape C}
    (ρ : Γ →ʳ Γ') (σ : Subst Γ' Δ) : Subst Γ Δ :=
  fun p => σ (ρ p)

@[inherit_doc Renaming.preSubst]
infixl:90 " ∘ʳˢ " => Renaming.preSubst

/-- Post-compose a substitution by a renaming: apply `σ`, then rename the result. -/
def Subst.postRen {C : Carrier} {Γ Δ Δ' : Shape C}
    (σ : Subst Γ Δ) (ρ : Δ →ʳ Δ') : Subst Γ Δ' :=
  fun {α} p => ⟦ ρ ⇑ʳ α ⟧ʳ (σ p)

@[inherit_doc Subst.postRen]
infixl:90 " ∘ˢʳ " => Subst.postRen

/-- Kleisli composition of substitutions: `(σ ˢ∘ˢ θ) p = θ.lift (σ p)`. -/
def Subst.comp {C : Carrier} {Γ Δ Ε : Shape C}
    (σ : Subst Γ Δ) (θ : Subst Δ Ε) : Subst Γ Ε :=
  fun p => θ.lift (σ p)

@[inherit_doc Subst.comp]
infixl:90 " ∘ˢˢ " => Subst.comp

/-- Extend a substitution through a fresh α-binder: η at the new binder, σ then weaken
on the underlying slots. -/
def Subst.extend {C : Carrier} {Δ Ε : Shape C} (σ : Subst Δ Ε) (α : C.Arity) :
    Subst (Δ ⋈ α) (Ε ⋈ α) :=
  fun {α'} p =>
    match p with
    | .here i  => Expr.η (.here i)
    | .there q => ⟦ Renaming.weaken Ε α ⇑ʳ α' ⟧ʳ (σ q)

@[inherit_doc Subst.extend]
infixl:95 " ⇑ˢ " => Subst.extend

/-- Iterated extension of a substitution through a list of binders. -/
def Subst.extendList {C : Carrier} {Δ Ε : Shape C} (σ : Subst Δ Ε) :
    (τ : List C.Arity) → Subst (Δ ⋈* τ) (Ε ⋈* τ)
  | []        => σ
  | β :: rest => (Subst.extendList σ rest) ⇑ˢ β

@[inherit_doc Subst.extendList]
infixl:95 " ⇑ˢ* " => Subst.extendList

/-- Componentwise action of a substitution on an instantiation. -/
def Inst.map {C : Carrier} {α : C.Arity} {Δ Ε : Shape C}
    (ι : Inst α Δ) (σ : Subst Δ Ε) : Inst α Ε :=
  fun j => σ.lift (ι j)
