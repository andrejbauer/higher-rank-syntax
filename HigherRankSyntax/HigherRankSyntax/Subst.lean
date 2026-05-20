import HigherRankSyntax.Expr

/-!
# Substitution, instantiation, and the Kleisli extension

Slot classification, the walkers `inst.aux` and `lift.aux`, their per-case
unfolders, the public wrappers `Inst.act`, `Subst.lift`, and `Subst.act`, and
the categorical operations (`Renaming.toSubst`, `Renaming.preSubst`,
`Subst.postRen`, `Subst.comp`).

Each head slot is classified by `classify` into either a Γ-slot (`XPos.base`, the
weakening of some `p : Slot Γ` through τ) or a τ-binder (`XPos.ext`, identified by a
split of τ as `τ_above ++ β :: τ_below` with a binder `i` of `β`).  The
slot-correspondence witness lives in the inductive's index, so pattern matching on
`classify`'s result yields it definitionally — no `Eq.rec`.

`lift.aux` walks `Expr (Γ ⋈* τ)`; the Γ-slot case substitutes via σ and uses
`inst.aux` directly on σ's image, threading the target weakening as a renaming.
`inst.aux` walks `Expr ((Δ ⋈ α) ⋈* τ)`, carries a renaming `ρ : Δ →ʳ Ξ`, and
maps Δ-slots through `ρ` during traversal.
-/


/-! ## Substitutions and instantiations -/

/-- A substitution from `Γ` to `Δ`. -/
abbrev Subst {C : Carrier} (Γ Δ : Shape C) : Type :=
  (p : Slot Γ) → Expr (Δ ⋈ p.arity)

/-- An instantiation of an α-binder above `Γ`. -/
abbrev Inst {C : Carrier} (α : C.Arity) (Γ : Shape C) : Type :=
  (i : C.Binder α) → Expr (Γ ⋈ i.arity)

/-! ## Slot classification -/

/-- The slot at depth `|τ_above|` in `Γ ⋈* (τ_above ++ β :: τ_below)` corresponding to
binder `i` of `β`.  Iterates `.there` over `τ_above` from `.here i`. -/
def tauSlot {C : Carrier} (Γ : Shape C) :
    (τ_above : List C.Arity) → (β : C.Arity) → (τ_below : List C.Arity) →
    (i : C.Binder β) → Slot (Γ ⋈* (τ_above ++ β :: τ_below))
  | [],        _, _, i => .here i
  | _ :: rest, β, τ_below, i => .there (tauSlot Γ rest β τ_below i)

/-- A `tauSlot`'s arity is the binder's sub-arity. -/
theorem tauSlot_arity {C : Carrier} (Γ : Shape C)
    (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
    (i : C.Binder β) : (tauSlot Γ τ_above β τ_below i).arity = i.arity := by
  induction τ_above with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- Position of a slot in `Γ ⋈* τ`: a Γ-slot weakened through τ, or a τ-binder. -/
inductive XPos {C : Carrier} (Γ : Shape C) :
    (τ : List C.Arity) → Slot (Γ ⋈* τ) → Type where
  | base : ∀ {τ : List C.Arity}, (p : Slot Γ) →
           XPos Γ τ ((Γ ↪ʳ τ) p)
  | ext  : ∀ {τ_above : List C.Arity} {β : C.Arity} {τ_below : List C.Arity},
           (i : C.Binder β) →
           XPos Γ (τ_above ++ β :: τ_below) (tauSlot Γ τ_above β τ_below i)

/-- Classify a slot in an iterated extension. -/
def classify {C : Carrier} {Γ : Shape C} :
    (τ : List C.Arity) → (p : Slot (Γ ⋈* τ)) → XPos Γ τ p
  | [],       p        => XPos.base p
  | _ :: _,   .here i  => XPos.ext (τ_above := []) i
  | β :: τ',  .there p =>
      match classify τ' p with
      | XPos.base q => XPos.base q
      | XPos.ext (τ_above := ta) (β := b) (τ_below := tb) j =>
          XPos.ext (τ_above := β :: ta) (β := b) (τ_below := tb) j

/-- Classifying a Γ-slot weakened through τ recovers the original Γ-slot. -/
@[simp] theorem classify_weakenList {C : Carrier} {Γ : Shape C}
    (τ : List C.Arity) (p : Slot Γ) :
    classify τ ((Γ ↪ʳ τ) p) = XPos.base p := by
  induction τ with
  | nil => rfl
  | cons β rest ih =>
    show classify (β :: rest)
           (.there ((Γ ↪ʳ rest) p)) = XPos.base p
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
def inst.aux {C : Carrier} {Δ Ξ : Shape C} (α : C.Arity)
    (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
    (τ : List C.Arity) (e : Expr ((Δ ⋈ α) ⋈* τ)) : Expr (Ξ ⋈* τ) :=
  match e with
  | .apply' p α_h h_α_h args =>
      match classify τ p with
      | XPos.ext (τ_above := ta) (β := b) (τ_below := tb) i =>
          let new_args : (i : C.Binder α_h) →
              Expr ((Ξ ⋈* (ta ++ b :: tb)) ⋈ i.arity) :=
            fun i => inst.aux α ρ ι (i.arity :: (ta ++ b :: tb)) (args i)
          have new_h : (tauSlot Ξ ta b tb i).arity = α_h :=
            (tauSlot_arity Ξ ta b tb i).trans
              ((tauSlot_arity (Δ ⋈ α) ta b tb i).symm.trans h_α_h)
          Expr.apply' (tauSlot Ξ ta b tb i) α_h new_h new_args
      | XPos.base q =>
          match q with
          | .there r =>
              let new_args : (i : C.Binder α_h) →
                  Expr ((Ξ ⋈* τ) ⋈ i.arity) :=
                fun i => inst.aux α ρ ι (i.arity :: τ) (args i)
              have new_h : ((Ξ ↪ʳ τ) (ρ r)).arity = α_h :=
                ((Ξ ↪ʳ τ).arity (ρ r)).trans
                  ((ρ.arity r).trans
                    ((((Δ ⋈ α) ↪ʳ τ).arity (.there r)).symm.trans h_α_h))
              Expr.apply' ((Ξ ↪ʳ τ) (ρ r)) α_h new_h new_args
          | .here j =>
              have hs : j.arity = α_h :=
                (((Δ ⋈ α) ↪ʳ τ).arity (.here j)).symm.trans h_α_h
              match hs with
              | rfl =>
                  let new_args : (i : C.Binder j.arity) →
                      Expr ((Ξ ⋈* τ) ⋈ i.arity) :=
                    fun i => inst.aux α ρ ι (i.arity :: τ) (args i)
                  inst.aux j.arity (Ξ ↪ʳ τ) new_args [] (ι j)
termination_by (⟨α, _, e⟩ : (_ : C.Arity) ×' Σ Γ : Shape C, Expr Γ)
decreasing_by
  -- ext args descent
  · exact PSigma.Lex.right _ (Expr.Subterm.of_arg _ _ _ _ _)
  -- .there args descent
  · exact PSigma.Lex.right _ (Expr.Subterm.of_arg _ _ _ _ _)
  -- .here args descent
  · exact PSigma.Lex.right _ (Expr.Subterm.of_arg _ _ _ _ _)
  -- α decreases (j.arity ≺ α)
  · exact PSigma.Lex.left _ _ ⟨j, rfl⟩

/-! ## η-fillers and per-case unfolders for `inst.aux` -/

/-- Canonical η-fillers for an α-binder over a shape with α at the top.
At each binder position `i`, returns the η-expansion of the bound variable `.here i`. -/
def η_fillers {C : Carrier} (Δ : Shape C) (α : C.Arity) : Inst α (Δ ⋈ α) :=
  fun i => Expr.η ⟨.here i, rfl⟩

@[simp] theorem inst_aux_ext_eq {C : Carrier} {Δ Ξ : Shape C} (α : C.Arity)
    (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
    (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
    (i : C.Binder β) (α_h : C.Arity)
    (h : (tauSlot (Δ ⋈ α) τ_above β τ_below i).arity = α_h)
    (args : (j : C.Binder α_h) →
      Expr ((Δ ⋈ α) ⋈* (τ_above ++ β :: τ_below) ⋈ j.arity)) :
    inst.aux α ρ ι (τ_above ++ β :: τ_below)
      (Expr.apply' (tauSlot (Δ ⋈ α) τ_above β τ_below i)
        α_h h args)
      =
    Expr.apply' (tauSlot Ξ τ_above β τ_below i)
      α_h
      ((tauSlot_arity Ξ τ_above β τ_below i).trans
        ((tauSlot_arity (Δ ⋈ α) τ_above β τ_below i).symm.trans h))
      (fun j => inst.aux α ρ ι (j.arity :: (τ_above ++ β :: τ_below)) (args j)) := by
  delta inst.aux
  change inst.aux._unary (C := C)
      ⟨Δ, ⟨Ξ, ⟨α, ⟨ρ, ⟨ι, ⟨τ_above ++ β :: τ_below,
        Expr.apply' (tauSlot (Δ ⋈ α) τ_above β τ_below i)
          α_h h args⟩⟩⟩⟩⟩⟩ = _
  rw [inst.aux._unary.eq_1]
  simp [classify_tauSlot]

@[simp] theorem inst_aux_base_there_eq {C : Carrier} {Δ Ξ : Shape C} (α : C.Arity)
    (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
    (τ : List C.Arity) (r : Slot Δ) (α_h : C.Arity)
    (h : (((Δ ⋈ α) ↪ʳ τ) (.there r)).arity = α_h)
    (args : (j : C.Binder α_h) → Expr ((Δ ⋈ α) ⋈* τ ⋈ j.arity)) :
    inst.aux α ρ ι τ
      (Expr.apply' (((Δ ⋈ α) ↪ʳ τ) (.there r))
        α_h h args)
      =
    Expr.apply' ((Ξ ↪ʳ τ) (ρ r)) α_h
      (((Ξ ↪ʳ τ).arity (ρ r)).trans
        ((ρ.arity r).trans
          ((((Δ ⋈ α) ↪ʳ τ).arity (.there r)).symm.trans h)))
      (fun j => inst.aux α ρ ι (j.arity :: τ) (args j)) := by
  delta inst.aux
  change inst.aux._unary (C := C)
      ⟨Δ, ⟨Ξ, ⟨α, ⟨ρ, ⟨ι, ⟨τ,
        Expr.apply' (((Δ ⋈ α) ↪ʳ τ) (.there r))
          α_h h args⟩⟩⟩⟩⟩⟩ = _
  rw [inst.aux._unary.eq_1]
  simp [classify_weakenList]

@[simp] theorem inst_aux_base_here_eq {C : Carrier} {Δ Ξ : Shape C} (α : C.Arity)
    (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
    (τ : List C.Arity) (j : C.Binder α)
    (h : (((Δ ⋈ α) ↪ʳ τ) (.here j)).arity = j.arity)
    (args : (k : C.Binder j.arity) → Expr ((Δ ⋈ α) ⋈* τ ⋈ k.arity)) :
    inst.aux α ρ ι τ
      (Expr.apply' (((Δ ⋈ α) ↪ʳ τ) (.here j))
        j.arity h args)
      =
    inst.aux j.arity (Ξ ↪ʳ τ)
      (fun k => inst.aux α ρ ι (k.arity :: τ) (args k)) [] (ι j) := by
  delta inst.aux
  change inst.aux._unary (C := C)
      ⟨Δ, ⟨Ξ, ⟨α, ⟨ρ, ⟨ι, ⟨τ,
        Expr.apply' (((Δ ⋈ α) ↪ʳ τ) (.here j))
          j.arity h args⟩⟩⟩⟩⟩⟩ = _
  rw [inst.aux._unary.eq_1]
  simp [classify_weakenList]

/-- Kleisli extension walker.  Walks `e : Expr (Γ ⋈* τ)` by classifying each head:
τ-binder rebuilds; Γ-slot substitutes via σ and threads the target weakening through
`inst.aux`. -/
def lift.aux {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
    (τ : List C.Arity) (e : Expr (Γ ⋈* τ)) : Expr (Δ ⋈* τ) :=
  match e with
  | .apply' p α_h h_α_h args =>
      match classify τ p with
      | XPos.ext (τ_above := ta) (β := b) (τ_below := tb) i =>
          let new_args : (i : C.Binder α_h) →
              Expr ((Δ ⋈* (ta ++ b :: tb)) ⋈ i.arity) :=
            fun i => lift.aux σ (i.arity :: (ta ++ b :: tb)) (args i)
          have new_h : (tauSlot Δ ta b tb i).arity = α_h :=
            (tauSlot_arity Δ ta b tb i).trans
              ((tauSlot_arity Γ ta b tb i).symm.trans h_α_h)
          Expr.apply' (tauSlot Δ ta b tb i) α_h new_h new_args
      | XPos.base q =>
          have hs : q.arity = α_h :=
            ((Γ ↪ʳ τ).arity q).symm.trans h_α_h
          match hs with
          | rfl =>
              let new_args : (i : C.Binder q.arity) →
                  Expr ((Δ ⋈* τ) ⋈ i.arity) :=
                fun i => lift.aux σ (i.arity :: τ) (args i)
              inst.aux q.arity (Δ ↪ʳ τ) new_args [] (σ q)
termination_by (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by
  all_goals exact Expr.Subterm.of_arg _ _ _ _ _

@[simp] theorem lift_aux_ext_eq {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
    (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
    (i : C.Binder β) (α_h : C.Arity)
    (h : (tauSlot Γ τ_above β τ_below i).arity = α_h)
    (args : (j : C.Binder α_h) →
      Expr (Γ ⋈* (τ_above ++ β :: τ_below) ⋈ j.arity)) :
    lift.aux σ (τ_above ++ β :: τ_below)
      (Expr.apply' (tauSlot Γ τ_above β τ_below i) α_h h args)
      =
    Expr.apply' (tauSlot Δ τ_above β τ_below i) α_h
      ((tauSlot_arity Δ τ_above β τ_below i).trans
        ((tauSlot_arity Γ τ_above β τ_below i).symm.trans h))
      (fun j => lift.aux σ (j.arity :: (τ_above ++ β :: τ_below)) (args j)) := by
  delta lift.aux
  change lift.aux._unary (C := C) σ
      ⟨τ_above ++ β :: τ_below,
        Expr.apply' (tauSlot Γ τ_above β τ_below i) α_h h args⟩ = _
  rw [lift.aux._unary.eq_1]
  simp [classify_tauSlot]

@[simp] theorem lift_aux_base_eq {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
    (τ : List C.Arity) (q : Slot Γ)
    (h : ((Γ ↪ʳ τ) q).arity = q.arity)
    (args : (j : C.Binder q.arity) → Expr (Γ ⋈* τ ⋈ j.arity)) :
    lift.aux σ τ
      (Expr.apply' ((Γ ↪ʳ τ) q) q.arity h args)
      =
    inst.aux q.arity (Δ ↪ʳ τ)
      (fun j => lift.aux σ (j.arity :: τ) (args j)) [] (σ q) := by
  delta lift.aux
  change lift.aux._unary (C := C) σ
      ⟨τ, Expr.apply' ((Γ ↪ʳ τ) q) q.arity h args⟩ = _
  rw [lift.aux._unary.eq_1]
  simp [classify_weakenList]

/-! ## Public wrappers -/

/-- α-instantiation: replace the α-binder of `Δ ⋈ α` by `ι`. -/
def Inst.act {C : Carrier} {α : C.Arity} {Δ : Shape C}
    (ι : Inst α Δ) (e : Expr (Δ ⋈ α)) : Expr Δ :=
  inst.aux α 𝟙ʳ ι [] e

/-- Kleisli extension at a single α-binder. -/
def Subst.lift {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
    {α : C.Arity} (e : Expr (Γ ⋈ α)) : Expr (Δ ⋈ α) :=
  lift.aux σ [α] e

/-- Action of a substitution on an expression without a top binder. -/
def Subst.act {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ) (e : Expr Γ) : Expr Δ :=
  lift.aux σ [] e

/-! ## Categorical operations: substitution and renaming compositions -/

/-- Embed a renaming as a substitution: send each slot through `ρ` and η-expand. -/
def Renaming.toSubst {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ) : Subst Γ Δ :=
  fun p => Expr.η ⟨ρ p, ρ.arity p⟩

/-- Pre-compose a substitution by a renaming: `(ρ ʳ∘ˢ σ) p = σ (ρ p)` up to the
arity-preservation transport carried by `ρ`. -/
def Renaming.preSubst {C : Carrier} {Γ Γ' Δ : Shape C}
    (ρ : Γ →ʳ Γ') (σ : Subst Γ' Δ) : Subst Γ Δ :=
  fun p => (ρ.arity p) ▸ σ (ρ p)

@[inherit_doc Renaming.preSubst]
infixl:90 " ʳ∘ˢ " => Renaming.preSubst

/-- Post-compose a substitution by a renaming: apply `σ`, then rename the result. -/
def Subst.postRen {C : Carrier} {Γ Δ Δ' : Shape C}
    (σ : Subst Γ Δ) (ρ : Δ →ʳ Δ') : Subst Γ Δ' :=
  fun p => ⟦ ρ ⇑ʳ p.arity ⟧ʳ (σ p)

@[inherit_doc Subst.postRen]
infixl:90 " ˢ∘ʳ " => Subst.postRen

/-- Kleisli composition of substitutions: `(σ ˢ∘ˢ θ) p = θ.lift (σ p)`. -/
def Subst.comp {C : Carrier} {Γ Δ Ε : Shape C}
    (σ : Subst Γ Δ) (θ : Subst Δ Ε) : Subst Γ Ε :=
  fun p => θ.lift (σ p)

@[inherit_doc Subst.comp]
infixl:90 " ˢ∘ˢ " => Subst.comp

/-- Extend a substitution through a fresh α-binder: η at the new binder, σ then weaken
on the underlying slots. -/
def Subst.under {C : Carrier} {Δ Ε : Shape C} (σ : Subst Δ Ε) (α : C.Arity) :
    Subst (Δ ⋈ α) (Ε ⋈ α) := fun
  | .here i  => Expr.η ⟨.here i, rfl⟩
  | .there p => ⟦ Renaming.weaken Ε α ⇑ʳ p.arity ⟧ʳ (σ p)

/-- Iterated extension of a substitution through a list of binders. -/
def Subst.extendList {C : Carrier} {Δ Ε : Shape C} (σ : Subst Δ Ε) :
    (τ : List C.Arity) → Subst (Δ ⋈* τ) (Ε ⋈* τ)
  | []        => σ
  | β :: rest => (σ.extendList rest).under β

/-- Componentwise action of a substitution on an instantiation. -/
def Inst.map {C : Carrier} {α : C.Arity} {Δ Ε : Shape C}
    (ι : Inst α Δ) (σ : Subst Δ Ε) : Inst α Ε :=
  fun j => σ.lift (ι j)

