import HigherRankSyntax.Subst

/-!
# Equations of the substitution action

Auxiliary equations for the three relative-monad laws, built from
**computation lemmas**: each takes `Subst.act` on an `Expr.ap` with a
specific head (τ-side, dom-side, pre-side) and reduces the classify
dispatch to a clean right-hand side.  The reflection lemmas
`Proper.classify_inr` / `classify_inl` are the rewriting handles.

The file has two conceptual halves.

1. The first half proves the unit laws.  These are mostly structural
   inductions on expressions, plus a mutual arity induction for the
   interaction between η-expansion and one-binder instantiation.

2. The second half proves composition.  The hard point is not the
   mathematical idea, but keeping Lean's `Proper` witnesses aligned.  A
   shape such as `(τ ⋈ dst) ⋈ Tele.ofList υ` can be equipped with different
   computational witnesses, and those witnesses determine how `Proper.inl`,
   `Proper.inr`, and `Proper.cover` reduce.  The private `Proper.AppendCoherence`
   package below records the exact witnesses and coherence equations used by
   the composition proof.

The central private theorem in the second half is `diamondAt`: acting by `σ`
commutes with instantiating an arbitrary source substitution `κ`.  It is
mutual with `liftAt`, because the `dom` branch of `diamondAt` creates a fresh
one-binder instantiation, whose β-head case calls back into the diamond.

## The three monad laws

* `Subst.act_id` — `(Subst.id Γ).act τ e = e` (unit_right).
* `Subst.act_η` — `(Subst.mk f).act ⌊α⌋ (Expr.η p) = f p` (unit_left).
* `Subst.act_kcomp` — Kleisli composition factors (comp_lift).
-/


/-! ## Computation lemmas — `Subst.act` on a specific apply head -/

/-- Computing `σ.act` on an apply whose head is right-injected into the
τ-side: collapses to the S-side reconstruction. -/
theorem Subst.act_ap_right
    {C : Carrier} {pre dom cod : Shape C}
    [Proper dom] [Proper cod]
    (σ : Subst C dom (pre ⋈ cod)) (τ : Shape C) [Proper τ]
    {α} (x : τ ∋ α)
    (args : (i : C.Binder α) → Expr (((pre ⋈ dom) ⋈ τ) ∷ i.arity)) :
  σ.act τ (.ap (ι₂ x) args)
    = .ap (ι₂ x) (fun j => σ.act (τ ∷ j.arity) (args j))
  := by
  conv => lhs; unfold Subst.act
  rw [Subst.threeway_inr]

/-- Computing `σ.act` on an apply whose head is left-injected below τ and
classified to the dom side: fires the dom-branch instantiation. -/
theorem Subst.act_ap_middle
    {C : Carrier} {pre dom cod : Shape C}
    [Proper dom] [Proper cod]
    (σ : Subst C dom (pre ⋈ cod)) (τ : Shape C) [Proper τ]
    {α} (y : dom ∋ α)
    (args : (i : C.Binder α) → Expr (((pre ⋈ dom) ⋈ τ) ∷ i.arity)) :
  σ.act τ (.ap ((Proper.inl (pre ⋈ dom)) ((Proper.inr pre) y)) args)
    = ⟦ ((fun | .here (i : C.Binder α) => σ.act (τ ∷ i.arity) (args i)) : Subst C ⌊α⌋ ((pre ⋈ cod) ⋈ τ)) ⟧ˢ (σ y)
  := by
  conv => lhs; unfold Subst.act
  rw [Subst.threeway_inl_dom]
  rfl

/-- Computing `σ.act` on an apply whose head is left-injected below τ and
classified to the pre side: rebuilds the head in the pre branch. -/
theorem Subst.act_ap_left
    {C : Carrier} {pre dom cod : Shape C}
    [Proper dom] [Proper cod]
    (σ : Subst C dom (pre ⋈ cod)) (τ : Shape C) [Proper τ]
    {α} (z : pre ∋ α)
    (args : (i : C.Binder α) → Expr (((pre ⋈ dom) ⋈ τ) ∷ i.arity)) :
  σ.act τ (.ap ((Proper.inl (pre ⋈ dom)) ((Proper.inl pre) z)) args)
    = .ap ((Proper.inl (pre ⋈ cod)) ((Proper.inl pre) z)) (fun i => σ.act (τ ∷ i.arity) (args i))
  := by
  conv => lhs; unfold Subst.act
  rw [Subst.threeway_inl_pre]

/-! ## Auxiliary: η-action on a right-injected slot -/

/-- Acting on the η-expansion of a right-injected (S-side) slot reproduces
the η in the target shape.  By WF recursion on the slot's arity `α`; uses
`act_apply_inr` as a black-box computation lemma. -/
theorem Subst.act_η_right
    {C : Carrier} {pre dom cod : Shape C}
    [Proper dom] [Proper cod]
    (σ : Subst C dom (pre ⋈ cod)) (τ : Shape C) [Proper τ]
    {α} (x : τ ∋ α) :
  σ.act (τ ∷ α) (.η (Proper.inr _ x))
    = .η (Proper.inr _ x)
  := by
  rw [Expr.η.eq_1]
  -- `.there ((inr τ) x) = (inr (τ ∷ α)) (.there x)` holds
  -- definitionally (instCons.inr); `change` exposes the rewrite shape.
  change σ.act (τ ∷ α)
      (.ap (Proper.inr _ (.there x))
                  (fun i => .η (.here i))) = _
  rw [Subst.act_ap_right σ (τ ∷ α) (.there x)]
  rw [Expr.η.eq_1]
  congr 1
  funext i
  exact Subst.act_η_right σ (τ ∷ α)
          (x := @ListSlotAt.here C α τ.toList i)
termination_by α
decreasing_by exact ⟨i, rfl⟩

/-! ## Instantiation laws: identity action and β-for-η -/

/-- Identity instantiation acts as the identity, given the β-for-η
property at the immediate sub-arities of the head arity.  The proof
recurses over the expression. -/
private theorem idOf
    {C : Carrier} (α : C.Arity) (Δ : Shape C)
    (hη : ∀ (i : C.Binder α), ∀ {pre cod : Shape C} [Proper cod]
      (ι : Subst C ⌊i.arity⌋ (pre ⋈ cod))
      (p : pre ∋ i.arity),
      ⟦ ι ⟧ˢ (.η p)
        = .ap ((Proper.inl pre) p) (fun j => ι (.here j))) :
  ∀ (τ : Shape C) [Proper τ] (e : Expr ((Δ ∷ α) ⋈ τ)),
    Subst.act (Subst.instId Δ α) (Γ := Δ) τ e = e
  | τ, _, .ap (α := β) head argFam => by
      have ih_all : ∀ (k : C.Binder β),
          Subst.act (Subst.instId Δ α) (Γ := Δ) (τ ∷ k.arity) (argFam k) = argFam k :=
        fun k => idOf α Δ hη (τ ∷ k.arity) (argFam k)
      rcases Proper.cover (Δ ∷ α) head with ⟨y, h_y⟩ | ⟨y, h_y⟩
      · subst h_y
        refine (Subst.act_ap_right (Subst.instId Δ α) τ y argFam).trans ?_
        congr
        funext k
        exact ih_all k
      · subst h_y
        rcases Proper.cover Δ y with ⟨z, h_z⟩ | ⟨z, h_z⟩
        · subst h_z
          cases z with
          | here i =>
              refine (Subst.act_ap_middle
                (Subst.instId Δ α) τ (.here i) argFam).trans ?_
              refine (hη i (pre := Δ ∷ α) (cod := τ)
                (ι := _) (p := .here i)).trans ?_
              congr 1
              funext k
              exact ih_all k
          | there z' => nomatch z'
        · subst h_z
          refine (Subst.act_ap_left (Subst.instId Δ α) τ z argFam).trans ?_
          congr 1
          funext k
          exact ih_all k
termination_by τ _ e => (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg head argFam _

-- β-for-η and identity-act, proved together by well-founded recursion on
-- arities: β-for-η at α invokes identity-act at i.arity ≺ α, and identity-act
-- at α invokes β-for-η at i.arity ≺ α (via `idOf`'s hypothesis).
mutual

/-- β-for-η for a one-binder instantiation: instantiating the η-expansion
of a pre-slot exposes the kit. -/
theorem Subst.act_inst.η
    {C : Carrier} {pre cod : Shape C} [Proper cod]
    {α} (ι : Subst C ⌊α⌋ (pre ⋈ cod))
    (p : pre ∋ α) :
  ⟦ ι ⟧ˢ (.η p)
    = .ap ((Proper.inl pre) p) (fun i => ι (.here i))
  := by
  rw [Expr.η.eq_1]
  change ⟦ ι ⟧ˢ
      (.ap ((Proper.inl (pre ⋈ ⌊α⌋))
        ((Proper.inl pre) p)) (fun i => .η (.here i))) = _
  rw [Subst.act_ap_left]
  change
    Expr.ap ((Proper.inl pre) p)
      (fun i => ι.act (⌊i.arity⌋) (.η (.here i)))
    =
    Expr.ap ((Proper.inl pre) p) (fun i => ι (.here i))
  congr
  funext i
  rw [Expr.η.eq_1]
  change ι.act (⌊i.arity⌋)
      (.ap ((Proper.inl _) ((Proper.inr pre) (.here i)))
        (fun k =>
          @Expr.η C
            ((pre ⋈ ⌊α⌋) ⋈ (⌊i.arity⌋))
            k.arity (.here k))) = _
  rw [Subst.act_ap_middle]
  have hfill : ∀ (k : C.Binder i.arity),
      ι.act
        (⌊i.arity⌋ ∷ k.arity)
          (@Expr.η C
            ((pre ⋈ ⌊α⌋) ⋈ ⌊i.arity⌋)
            k.arity (.here k))
      =
        @Expr.η C
          ((pre ⋈ cod) ⋈ (⌊i.arity⌋))
          k.arity (.here k)
          := by
    intro k
    exact Subst.act_η_right ι (⌊i.arity⌋) (x := .here k)
  simp only [hfill]
  exact Subst.act_inst.id i.arity (pre ⋈ cod) Shape.nil (ι (.here i))
termination_by α
decreasing_by exact ⟨i, rfl⟩

/-- Identity instantiation acts as the identity. -/
theorem Subst.act_inst.id
    {C : Carrier} (α : C.Arity) (Δ : Shape C) :
  ∀ (τ : Shape C) [Proper τ] (e : Expr ((Δ ∷ α) ⋈ τ)),
    act (instId Δ α) (Γ := Δ) τ e = e
  :=
  fun τ _ e =>
    idOf α Δ (fun i => act_inst.η) τ e
termination_by α
decreasing_by exact ⟨i, rfl⟩

end

/-! ## Monad laws -/

/-- **`act_id`** — the identity substitution acts as the identity.
Translates to `lift η = 𝟙` (unit_right).  Generalised over τ so the
recursive call on each arg fits the same statement. -/
theorem Subst.act_id
    {C : Carrier} (Γ : Shape C) [Proper Γ]
    (τ : Shape C) [Proper τ]
    (e : Expr (Γ ⋈ τ)) :
  act (id Γ) (Γ := Shape.nil) τ e = e
  := by
  match e with
  | .ap (α := β) x args =>
    rcases Proper.cover Γ x with
      ⟨y, h_y⟩ | ⟨y, h_y⟩
    · -- head = inr x; the τ-side branch fires.
      subst h_y
      refine (Subst.act_ap_right (pre := Shape.nil)
        (Subst.id Γ) τ y args).trans ?_
      congr ; funext k ; apply Subst.act_id
    · -- head = inl y; y : Γ ∋ β.  Cover y at base Shape.nil:
      -- inl-from-nil is empty, so y is necessarily in the right image.
      subst h_y
      rcases Proper.cover Shape.nil y with ⟨y, h_q⟩ | ⟨z, _⟩
      · subst h_q
        refine (Subst.act_ap_middle (pre := Shape.nil)
          (Subst.id Γ) τ y args).trans ?_
        -- IH on each argument:
        have h_args : ∀ (k : C.Binder β),
          act (id Γ) (Γ := Shape.nil) (τ ∷ k.arity) _ = args k :=
          fun k => Subst.act_id Γ _ _
        rw [Proper.inr_nil_id y]
        refine (Subst.act_inst.η (ι := _) (p := y)).trans ?_
        congr 1
        funext k
        exact h_args k
      · exact nomatch z
termination_by (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args _

/-- **`act_η`** — acting on an η-expansion reduces to applying `f`.
Translates to `lift f ∘ η = f` (unit_left). -/
theorem Subst.act_η
    {C : Carrier} {Γ Δ : Shape C} [Proper Γ] [Proper Δ]
      (f : Subst C Γ Δ)
    (α : C.Arity) (p : Γ ∋ α) :
    f.act (Γ := Shape.nil) ⌊α⌋ (.η p) = f p
  := by
  rw [Expr.η.eq_1]
  -- `.there p = (weaken_{⌊α⌋} _) p` by instCons.weaken (rfl).
  -- Cover p at base Shape.nil: p must be in the right image (inl-from-nil empty).
  rcases Proper.cover Shape.nil p with ⟨y, h_q⟩ | ⟨z, _⟩
  · subst h_q
    show f.act (Γ := Shape.nil) ⌊α⌋
        (.ap ((Proper.inl (Shape.nil ⋈ Γ))
                      ((Proper.inr Shape.nil) y))
                    (fun i => .η (.here i))) = _
    rw [Subst.act_ap_middle (pre := Shape.nil)
      f ⌊α⌋ y]
    have hfill : ∀ (i : C.Binder α),
        f.act (⌊α⌋ ∷ i.arity)
          (@Expr.η C
            ((Shape.nil ⋈ Γ) ⋈ ⌊α⌋)
            i.arity (.here i))
        =
        @Expr.η C
          ((Shape.nil ⋈ Δ) ⋈ ⌊α⌋)
          i.arity (.here i)
          := by
      intro i
      exact Subst.act_η_right (pre := Shape.nil) f ⌊α⌋ (x := .here i)
    simp only [hfill]
    rw [Proper.inr_nil_id y]
    exact Subst.act_inst.id α Δ Shape.nil (f y)
  · exact nomatch z

/-- `Expr.Subterm.of_arg` repackaged for the descent shape
`Γ ⋈ Tele.ofList (j.arity :: ρ)`. -/
private theorem Expr.Subterm.of_arg_ofList_cons
    {C : Carrier} {Γ : Shape C}
    (ρ : List C.Arity) {α}
    (head : Γ ⋈ Tele.ofList ρ ∋ α)
    (args : (i : C.Binder α) → Expr ((Γ ⋈ Tele.ofList ρ) ∷ i.arity))
    (j : C.Binder α) :
  Expr.Subterm
    ⟨Γ ⋈ Tele.ofList (j.arity :: ρ), args j⟩
    ⟨Γ ⋈ Tele.ofList ρ, .ap head args⟩
  := by
  simpa [Shape.extList, Shape.ext, Tele.comp, Tele.ofList] using
    (Expr.Subterm.of_arg head args j)

/-! ## General substitution diamond for composition -/

/-!
The composition proof is expressed as a substitution diamond.  The informal
picture is:

```
  act by σ, then instantiate κ pushed forward pointwise
      =
  instantiate κ first, then act by σ
```

The expression being transformed lives over
`(((pre ⋈ dom) ⋈ τ) ⋈ src) ⋈ Tele.ofList υ`.

* `pre` is the prefix untouched by `σ`.
* `dom` is the substitution domain of `σ`.
* `τ` is a passive target depth under which `σ` is acting.
* `src` is the domain of the second substitution `κ`.
* `υ` is a concrete under-list used only for recursive descent into
  application arguments.

Most of the length below is bookkeeping that says exactly which of these
regions an application head came from.
-/

/- A singleton-instantiation substitution.  This is the local "substitute the
arguments of one application head" operation used in the `src`, `dom`, and
β branches. -/
private abbrev instOne
    {C : Carrier} {pre : Shape C} (α : C.Arity) (cod : Shape C)
    (f : (i : C.Binder α) → Expr ((pre ⋈ cod) ∷ i.arity)) :
    Subst C ⌊α⌋ (pre ⋈ cod) :=
  (fun | .here i => f i)

/- Extensionality for substitutions built from an explicit filler family. -/
-- private theorem Subst.mk_congr
--     {C : Carrier} {dom cod : Shape C}
--     {f g : Subst C dom cod}
--     (h : ∀ {α : C.Arity} (q : dom ∋ α), f q = g q) :
--   @f = @g
-- := by
--   congr
--   funext α q
--   exact h q

/- Apply `σ` at a target depth using an explicitly chosen `Proper` witness.
This tiny wrapper prevents typeclass search from silently choosing the wrong
composite witness. -/
private abbrev actAt
    {C : Carrier} {pre dom cod τ : Shape C}
    [Proper dom] [Proper cod]
    (σ : Subst C dom (pre ⋈ cod))
    (hτ : Proper τ)
    (e : Expr ((pre ⋈ dom) ⋈ τ)) :
    Expr ((pre ⋈ cod) ⋈ τ) :=
  @Subst.act C pre dom cod inferInstance inferInstance σ τ hτ e

namespace Diamond

/- Push a substitution `κ` forward along `σ`, by acting with `σ` on every
filler of `κ`.  Mathematically, this is
`(σ_* κ) x = σ (κ x)` at the passive depth determined by the filler. -/
private abbrev pushforward
    {C : Carrier} {Γ Δ Ξ Ω Θ : Shape C}
    [Proper Δ] [Proper Ξ] [Proper Ω] [Proper Θ]
    (σ : Subst C Δ (Γ ⋈ Ξ))
    (κ : Subst C Θ (Γ ⋈ Δ ⋈ Ω)) :
    Subst C Θ ((Γ ⋈ Ξ ⋈ Ω)) := by
  exact fun {β} x => σ.act (Ω ∷ β) (κ x)

end Diamond

namespace Lift

/- `Lift.sequential` is the companion situation created by a dom-head of
`diamondAt`: first instantiate a freshly opened β-binder (`lam`), then apply
`κ` under the additional list `υ`. -/
private abbrev sequential
    {C : Carrier} {pre τ src dst : Shape C}
    [Proper τ] [Proper src] [Proper dst]
    {υ : List C.Arity}
    (hτSrc : Proper (τ ⋈ src))
    (κ : Subst C src ((pre ⋈ τ) ⋈ dst))
    {β : C.Arity} (χ : List C.Arity)
    (η : (j : C.Binder β) →
      Expr (((pre ⋈ τ) ⋈ src) ⋈ Tele.ofList υ ∷ j.arity))
    (e : Expr ((pre ∷ β) ⋈ Tele.ofList χ)) :=
  κ.act ((Tele.ofList υ) ⋈ Tele.ofList χ)
    (Subst.act (instOne β ((τ ⋈ src) ⋈ Tele.ofList υ) η) (Tele.ofList χ) e)

/- `Lift.fused` is the same operation with the `κ` action pushed into each
β-filler.  `liftAt` proves `sequential = fused`. -/
private abbrev fused
    {C : Carrier} {pre τ src dst : Shape C}
    [Proper τ] [Proper src] [Proper dst]
    {υ : List C.Arity}
    (hτDst : Proper (τ ⋈ dst))
    (κ : Subst C src ((pre ⋈ τ) ⋈ dst))
    {β : C.Arity} (χ : List C.Arity)
    (η : (j : C.Binder β) →
      Expr (((pre ⋈ τ) ⋈ src) ⋈ Tele.ofList υ ∷ j.arity))
    (e : Expr ((pre ∷ β) ⋈ Tele.ofList χ)) :=
  Subst.act (instOne β ((τ ⋈ dst) ⋈ Tele.ofList υ)
      (fun j => κ.act (Tele.ofList υ ∷ j.arity) (η j))) (Tele.ofList χ) e

end Lift

/- Five possible origins for a head in the diamond expression:

* `under`: one of the concrete recursive argument binders `υ`;
* `src`: a head that belongs to the domain of `κ`;
* `tau`: a passive head from the ambient depth `τ`;
* `dom`: a head substituted by `σ`;
* `pre`: an untouched prefix head.

Keeping these cases explicit is the main readability device in `diamondAt`. -/
private inductive DiamondSite {C : Carrier}
    (pre dom τ src : Shape C) (υ : List C.Arity) : C.Arity → Type where
  | under {β} (xυ : Tele.ofList υ ∋ β) : DiamondSite pre dom τ src υ β
  | src {β} (xsrc : src ∋ β) : DiamondSite pre dom τ src υ β
  | tau {β} (xτ : τ ∋ β) : DiamondSite pre dom τ src υ β
  | dom {β} (z : dom ∋ β) : DiamondSite pre dom τ src υ β
  | pre {β} (z : pre ∋ β) : DiamondSite pre dom τ src υ β

/- Embed a classified head back into the flattened expression context, using
the exact source-side append witness. -/
private def DiamondSite.embed {C : Carrier}
    {pre dom τ src : Shape C} [Proper dom] [Proper τ] [Proper src]
    {β : C.Arity} {υ : List C.Arity}
    (hτSrc : Proper (τ ⋈ src)) :
    DiamondSite pre dom τ src υ β →
      ((((pre ⋈ dom) ⋈ τ) ⋈ src) ⋈ Tele.ofList υ) ∋ β :=
  letI : Proper ((τ ⋈ src) ⋈ Tele.ofList υ) := Proper.underList hτSrc υ
  fun
  | .under xυ =>
      ((Proper.inr (pre ⋈ dom)) :
        ((τ ⋈ src) ⋈ Tele.ofList υ) →ʳ
          (pre ⋈ dom) ⋈ ((τ ⋈ src) ⋈ Tele.ofList υ))
        ((Proper.inr (τ ⋈ src)) xυ)
  | .src xsrc =>
      ((Proper.inr (pre ⋈ dom)) :
        ((τ ⋈ src) ⋈ Tele.ofList υ) →ʳ
          (pre ⋈ dom) ⋈ ((τ ⋈ src) ⋈ Tele.ofList υ))
        ((Proper.inl (τ ⋈ src)) ((Proper.inr τ) xsrc))
  | .tau xτ =>
      ((Proper.inr (pre ⋈ dom)) :
        ((τ ⋈ src) ⋈ Tele.ofList υ) →ʳ
          (pre ⋈ dom) ⋈ ((τ ⋈ src) ⋈ Tele.ofList υ))
        ((Proper.inl (τ ⋈ src)) ((Proper.inl τ) xτ))
  | .dom z =>
      ((Proper.inl (pre ⋈ dom)) :
        (pre ⋈ dom) →ʳ
          (pre ⋈ dom) ⋈ ((τ ⋈ src) ⋈ Tele.ofList υ))
        ((Proper.inr pre) z)
  | .pre z =>
      ((Proper.inl (pre ⋈ dom)) :
        (pre ⋈ dom) →ʳ
          (pre ⋈ dom) ⋈ ((τ ⋈ src) ⋈ Tele.ofList υ))
        ((Proper.inl pre) z)

/- Covering lemma for diamond heads.  The proof is just the nested
`Proper.cover` split packaged once, so `diamondAt` can read as a five-case
proof instead of a maze of cover/subst blocks. -/
private theorem DiamondSite.cover {C : Carrier}
    {pre dom τ src : Shape C} [Proper dom] [Proper τ] [Proper src]
    {β : C.Arity} {υ : List C.Arity}
    (hτSrc : Proper (τ ⋈ src))
    (head : ((((pre ⋈ dom) ⋈ τ) ⋈ src) ⋈ Tele.ofList υ) ∋ β) :
    ∃ site : DiamondSite pre dom τ src υ β,
      head = DiamondSite.embed hτSrc site := by
  obtain ⟨site, h_site⟩ :=
    Subst.isReinject
      (Ξ := (τ ⋈ src) ⋈ Tele.ofList υ) head
  subst h_site
  cases site with
  | right top =>
      rcases Proper.cover (Γ := Tele.ofList υ) (τ ⋈ src) top with
        ⟨xυ, h_xυ⟩ | ⟨base, h_base⟩
      · subst h_xυ
        refine ⟨.under xυ, ?_⟩
        unfold DiamondSite.embed Subst.reinject
        rfl
      · subst h_base
        rcases Proper.cover (Γ := src) τ base with
          ⟨xsrc, h_xsrc⟩ | ⟨xτ, h_xτ⟩
        · subst h_xsrc
          refine ⟨.src xsrc, ?_⟩
          unfold DiamondSite.embed Subst.reinject
          rfl
        · subst h_xτ
          refine ⟨.tau xτ, ?_⟩
          unfold DiamondSite.embed Subst.reinject
          rfl
  | middle z =>
      refine ⟨.dom z, ?_⟩
      unfold DiamondSite.embed Subst.reinject
      rfl
  | left z =>
      refine ⟨.pre z, ?_⟩
      unfold DiamondSite.embed Subst.reinject
      rfl

/- One-step computation for the first action in `diamondAt`: acting by `σ` on a
head classified by `DiamondSite`.  This packages the otherwise repeated
`Subst.act_ap_*` and append-coherence rewrites for the five head origins. -/
private theorem DiamondSite.actBySubst {C : Carrier}
    {pre dom cod τ src : Shape C}
    [Proper dom] [Proper cod] [Proper τ] [Proper src]
    (σ : Subst C dom (pre ⋈ cod))
    {υ : List C.Arity}
    (hτSrc : Proper (τ ⋈ src))
    (srcTarget : Proper.AppendCoherence hτSrc)
    {β : C.Arity}
    (site : DiamondSite pre dom τ src υ β)
    (args : (i : C.Binder β) →
      Expr (((((pre ⋈ dom) ⋈ τ) ⋈ src) ⋈ Tele.ofList υ) ∷ i.arity)) :
    actAt (pre := pre) σ (Proper.underList hτSrc υ)
      (.ap (DiamondSite.embed hτSrc site) args)
    =
    match site with
    | .under xυ =>
        .ap ((Proper.inr (((pre ⋈ cod) ⋈ τ) ⋈ src)) xυ)
          (fun j => σ.act (((τ ⋈ src) ⋈ Tele.ofList υ) ∷ j.arity) (args j))
    | .src xsrc =>
        .ap
          ((Proper.inl (((pre ⋈ cod) ⋈ τ) ⋈ src))
            ((Proper.inr ((pre ⋈ cod) ⋈ τ)) xsrc))
          (fun j => σ.act (((τ ⋈ src) ⋈ Tele.ofList υ) ∷ j.arity) (args j))
    | .tau xτ =>
        .ap
          ((Proper.inl (((pre ⋈ cod) ⋈ τ) ⋈ src))
            ((Proper.inl ((pre ⋈ cod) ⋈ τ))
              ((Proper.inr (pre ⋈ cod)) xτ)))
          (fun j => σ.act (((τ ⋈ src) ⋈ Tele.ofList υ) ∷ j.arity) (args j))
    | .dom z =>
        ⟦ instOne β ((τ ⋈ src) ⋈ Tele.ofList υ)
            (fun j => σ.act (((τ ⋈ src) ⋈ Tele.ofList υ) ∷ j.arity) (args j)) ⟧ˢ
          (σ z)
    | .pre z =>
        .ap
          ((Proper.inl (((pre ⋈ cod) ⋈ τ) ⋈ src))
            ((Proper.inl ((pre ⋈ cod) ⋈ τ))
              ((Proper.inl (pre ⋈ cod)) ((Proper.inl pre) z))))
          (fun j => σ.act (((τ ⋈ src) ⋈ Tele.ofList υ) ∷ j.arity) (args j)) := by
  cases site with
  | under xυ =>
      unfold actAt DiamondSite.embed
      rw [Subst.act_ap_right σ ((τ ⋈ src) ⋈ Tele.ofList υ)
        ((Proper.inr (τ ⋈ src)) xυ) args]
      rw [Proper.extendList_inr_inr (τ ⋈ src) υ (pre ⋈ cod) xυ]
      rfl
  | src xsrc =>
      unfold actAt DiamondSite.embed
      rw [Subst.act_ap_right σ ((τ ⋈ src) ⋈ Tele.ofList υ)
        ((Proper.inl (τ ⋈ src)) ((Proper.inr τ) xsrc)) args]
      rw [Proper.extendList_inr_inl (τ ⋈ src) υ (pre ⋈ cod)
        ((Proper.inr τ) xsrc)]
      rw [srcTarget.inr_right (pre ⋈ cod) xsrc]
      rfl
  | tau xτ =>
      unfold actAt DiamondSite.embed
      rw [Subst.act_ap_right σ ((τ ⋈ src) ⋈ Tele.ofList υ)
        ((Proper.inl (τ ⋈ src)) ((Proper.inl τ) xτ)) args]
      rw [Proper.extendList_inr_inl (τ ⋈ src) υ (pre ⋈ cod)
        ((Proper.inl τ) xτ)]
      rw [srcTarget.inr_left (pre ⋈ cod) xτ]
      rfl
  | dom z =>
      unfold actAt DiamondSite.embed instOne
      rw [Subst.act_ap_middle σ ((τ ⋈ src) ⋈ Tele.ofList υ) z args]
  | pre z =>
      unfold actAt DiamondSite.embed
      rw [Subst.act_ap_left σ ((τ ⋈ src) ⋈ Tele.ofList υ) z args]
      rw [Proper.extendList_inl (τ ⋈ src) υ (pre ⋈ cod)
        ((Proper.inl pre) z)]
      rw [srcTarget.inl (pre ⋈ cod) ((Proper.inl pre) z)]
      rfl

/- Three possible origins for a head in the lifted one-binder companion:

* `under`: a concrete binder from `χ`;
* `beta`: the freshly opened β-binder;
* `pre`: an untouched prefix head.
-/
private inductive LiftSite {C : Carrier}
    (pre : Shape C) (β : C.Arity) (χ : List C.Arity) : C.Arity → Type where
  | under {γ} (xχ : Tele.ofList χ ∋ γ) : LiftSite pre β χ γ
  | beta (j : C.Binder β) : LiftSite pre β χ j.arity
  | pre {γ} (z : pre ∋ γ) : LiftSite pre β χ γ

/- Embed a `LiftSite` into the flattened context `(pre ∷ β) ⋈ Tele.ofList χ`. -/
private def LiftSite.embed {C : Carrier}
    {pre : Shape C} {β γ : C.Arity} {χ : List C.Arity} :
    LiftSite pre β χ γ → ((pre ∷ β) ⋈ Tele.ofList χ) ∋ γ
  | .under xχ => (Proper.inr (pre ∷ β)) xχ
  | .beta j => (Proper.inl (pre ∷ β)) ((Proper.inr pre) (.here j))
  | .pre z => (Proper.inl (pre ∷ β)) ((Proper.inl pre) z)

/- Pack the nested cover split for `liftAt`. -/
private theorem LiftSite.cover {C : Carrier}
    {pre : Shape C} {β γ : C.Arity} {χ : List C.Arity}
    (head : ((pre ∷ β) ⋈ Tele.ofList χ) ∋ γ) :
    ∃ site : LiftSite pre β χ γ, head = LiftSite.embed site := by
  rcases Proper.cover (Γ := Tele.ofList χ) (pre ∷ β) head with
    ⟨xχ, h_xχ⟩ | ⟨below, h_below⟩
  · subst h_xχ
    exact ⟨.under xχ, rfl⟩
  · subst h_below
    rcases Proper.cover pre below with ⟨xβ, h_xβ⟩ | ⟨z, h_z⟩
    · subst h_xβ
      cases xβ with
      | here j => exact ⟨.beta j, rfl⟩
      | there z => nomatch z
    · subst h_z
      exact ⟨.pre z, rfl⟩

/-- Two active substitution-domain fuels, considered up to swapping.  The mutual
diamond/lift proof either descends in one fuel component or keeps the fuel fixed
and descends into an expression argument. -/
private structure InterchangeFuel (C : Carrier) where
  fst : DomMeasure C
  snd : DomMeasure C

/-- Strict-decrease relation on `InterchangeFuel`, allowing component swap. -/
private inductive InterchangeFuel.Lt {C : Carrier} :
    InterchangeFuel C → InterchangeFuel C → Prop where
  | left {a b a' : DomMeasure C}
      (h : WellFoundedRelation.rel a' a) :
      InterchangeFuel.Lt ⟨a', b⟩ ⟨a, b⟩
  | right {a b b' : DomMeasure C}
      (h : WellFoundedRelation.rel b' b) :
      InterchangeFuel.Lt ⟨a, b'⟩ ⟨a, b⟩
  | left_swap {a b a' : DomMeasure C}
      (h : WellFoundedRelation.rel a' a) :
      InterchangeFuel.Lt ⟨b, a'⟩ ⟨a, b⟩
  | right_swap {a b b' : DomMeasure C}
      (h : WellFoundedRelation.rel b' b) :
      InterchangeFuel.Lt ⟨b', a⟩ ⟨a, b⟩

/-- Both components of an `InterchangeFuel` pair are simultaneously accessible. -/
private theorem InterchangeFuel.Lt.accPair
    {C : Carrier} (a b : DomMeasure C) :
  Acc (InterchangeFuel.Lt (C := C)) ⟨a, b⟩ ∧ Acc (InterchangeFuel.Lt (C := C)) ⟨b, a⟩
  := by
  let wf : WellFounded
      (WellFoundedRelation.rel : DomMeasure C → DomMeasure C → Prop) :=
    WellFoundedRelation.wf
  exact WellFounded.induction wf a (C := fun a =>
      ∀ b : DomMeasure C,
        Acc (InterchangeFuel.Lt (C := C)) ⟨a, b⟩ ∧
          Acc (InterchangeFuel.Lt (C := C)) ⟨b, a⟩)
    (fun a IHa b =>
      WellFounded.induction wf b (C := fun b =>
          Acc (InterchangeFuel.Lt (C := C)) ⟨a, b⟩ ∧
            Acc (InterchangeFuel.Lt (C := C)) ⟨b, a⟩)
        (fun b IHb => by
          constructor
          · refine Acc.intro _ ?_
            intro y hy
            cases y with
            | mk y₀ y₁ =>
                cases hy with
                | left h =>
                    exact (IHa y₀ h b).1
                | right h =>
                    exact (IHb y₁ h).1
                | left_swap h =>
                    exact (IHa y₁ h b).2
                | right_swap h =>
                    exact (IHb y₀ h).2
          · refine Acc.intro _ ?_
            intro y hy
            cases y with
            | mk y₀ y₁ =>
                cases hy with
                | left h =>
                    exact (IHb y₀ h).2
                | right h =>
                    exact (IHa y₁ h b).2
                | left_swap h =>
                    exact (IHb y₁ h).1
                | right_swap h =>
                    exact (IHa y₀ h b).1))
    b

/-- `InterchangeFuel.Lt` is well-founded. -/
private theorem InterchangeFuel.Lt.wf
    {C : Carrier} :
  WellFounded (InterchangeFuel.Lt (C := C))
  := by
  refine ⟨fun f => ?_⟩
  cases f with
  | mk a b =>
      exact (InterchangeFuel.Lt.accPair a b).1

private instance {C : Carrier} : WellFoundedRelation (InterchangeFuel C) where
  rel := InterchangeFuel.Lt
  wf := InterchangeFuel.Lt.wf

/-! ### The recursive diamond and its lifted companion

The next mutual block is the heart of the composition proof.

`diamondAt` proves the square

```
act σ after instantiate κ  =  instantiate (act σ on κ) after act σ
```

for expressions whose context has been flattened as
`(((pre ⋈ dom) ⋈ τ) ⋈ src) ⋈ Tele.ofList υ`.

The five `DiamondSite` cases are not five different mathematical ideas.  They
are the five possible origins of an application head after flattening:

* `under`, `tau`, and `pre` are stable-head cases.  The head is preserved and
  only the recursive argument family matters.
* `src` is where `κ` fires.  The proof descends into the selected filler
  `κ.sub xsrc`, so the source component of the fuel decreases.
* `dom` is where `σ` fires.  That creates a one-binder instantiation, so the
  proof switches to `liftAt`.

`liftAt` is the companion theorem for that fresh one-binder instantiation.
Its only active branch is `beta`; there it calls back into `diamondAt`.
-/

mutual

/- `diamondAt` is deliberately stated with `Proper.AppendCoherence` rather than asking
typeclass search for the composite `Proper` witnesses.  The proof needs
`Proper.extendList` witnesses for the concrete under-list `υ`; a merely
extensionally equal witness built by `Proper.compose` would not reduce the same
way in the head computations below. -/
private theorem diamondAt
    {C : Carrier} {pre dom cod τ src dst : Shape C}
    [Proper dom] [Proper cod] [Proper τ] [Proper src] [Proper dst]
    (σ : Subst C dom (pre ⋈ cod))
    {υ : List C.Arity}
    (hτSrc : Proper (τ ⋈ src)) (hτDst : Proper (τ ⋈ dst))
    (srcTarget : Proper.AppendCoherence hτSrc)
    (dstTarget : Proper.AppendCoherence hτDst)
    (κ : Subst C src (((pre ⋈ dom) ⋈ τ) ⋈ dst))
    (e : Expr ((((pre ⋈ dom) ⋈ τ) ⋈ src) ⋈ Tele.ofList υ)) :
    Subst.act
      (Γ := (pre ⋈ cod) ⋈ τ) (Δ := src) (Ξ := dst)
      (Diamond.pushforward (Ω := τ ⋈ dst) σ κ :
        Subst C src (((pre ⋈ cod) ⋈ τ) ⋈ dst))
      (Tele.ofList υ)
      (σ.act ((τ ⋈ src) ⋈ Tele.ofList υ) e)
      =
       σ.act ((τ ⋈ dst) ⋈ Tele.ofList υ) (κ.act (Tele.ofList υ) e) := by
  let κσ : Subst C src (((pre ⋈ cod) ⋈ τ) ⋈ dst) :=
    Diamond.pushforward (Ω := τ ⋈ dst) σ κ
  match e with
  | .ap (α := β) head args =>
      -- Ordinary structural recursion on every application argument.  Every
      -- branch below eventually reduces to these equalities, except the two
      -- fuel-changing branches (`src` and `dom`).
      have hargs :=
        fun (j : C.Binder β) => diamondAt (υ := j.arity :: υ)
          σ hτSrc hτDst srcTarget dstTarget κ (args j)
      obtain ⟨site, h_site⟩ := DiamondSite.cover hτSrc head
      subst h_site
      cases site with
      | under xυ =>
          -- Stable local-binder head.  Both routes keep the same head `xυ`;
          -- after normalising the embeddings, the result is pointwise `hargs`.
          refine (congrArg (Subst.act κσ (Tele.ofList υ))
            (DiamondSite.actBySubst σ hτSrc srcTarget (.under xυ) args)).trans ?_
          dsimp only [actAt, DiamondSite.embed]
          refine (Subst.act_ap_right κσ (Tele.ofList υ) xυ
            (fun j => σ.act (((τ ⋈ src) ⋈ Tele.ofList υ) ∷ j.arity) (args j))).trans ?_
          rw [show Proper.inr (pre ⋈ dom) (Proper.inr (τ ⋈ src) xυ)
              = Proper.inr (((pre ⋈ dom) ⋈ τ) ⋈ src) xυ by
            simpa only [Shape.extList_assoc] using
              Proper.extendList_inr_inr (τ ⋈ src) υ (pre ⋈ dom) xυ]
          rw [Subst.act_ap_right κ (Tele.ofList υ) xυ args]
          rw [← show Proper.inr (pre ⋈ dom) (Proper.inr (τ ⋈ dst) xυ)
              = Proper.inr (((pre ⋈ dom) ⋈ τ) ⋈ dst) xυ by
            simpa only [Shape.extList_assoc] using
              Proper.extendList_inr_inr (τ ⋈ dst) υ (pre ⋈ dom) xυ]
          refine Eq.trans ?_ (Subst.act_ap_right σ ((τ ⋈ dst) ⋈ Tele.ofList υ)
            ((Proper.inr (τ ⋈ dst)) xυ)
            (fun j => Subst.act κ (Tele.ofList υ ∷ j.arity) (args j))).symm
          rw [Proper.extendList_inr_inr (τ ⋈ dst) υ (pre ⋈ cod) xυ]
          congr 1
          funext j
          exact hargs j
      | src xsrc =>
          -- Source head for `κ`.  The right-hand route fires `κ` at `xsrc`.
          -- The left-hand route first acts on the head and then fires the
          -- pushforward substitution.  Both reduce to the smaller diamond on the
          -- single selected filler `κ.sub xsrc`.
          refine (congrArg (Subst.act κσ (Tele.ofList υ))
            (DiamondSite.actBySubst σ hτSrc srcTarget (.src xsrc) args)).trans ?_
          dsimp only [actAt, DiamondSite.embed]
          refine (Subst.act_ap_middle κσ (Tele.ofList υ) xsrc
            (fun j => σ.act (((τ ⋈ src) ⋈ Tele.ofList υ) ∷ j.arity) (args j))).trans ?_
          rw [Proper.extendList_inr_inl (τ ⋈ src) υ (pre ⋈ dom)
            ((Proper.inr τ) xsrc)]
          rw [srcTarget.inr_right (pre ⋈ dom) xsrc]
          change ⟦(
                (fun {δ} q => match q with
                | .here j =>
                    Subst.act κσ (Tele.ofList υ ∷ j.arity)
                      (σ.act (((τ ⋈ src) ⋈ Tele.ofList υ) ∷ j.arity) (args j)))
                : Subst C ⌊β⌋ (((pre ⋈ cod) ⋈ (τ ⋈ dst)) ⋈ Tele.ofList υ))⟧ˢ
              (σ.act ((τ ⋈ dst) ∷ β) (κ xsrc))
            =
            σ.act ((τ ⋈ dst) ⋈ Tele.ofList υ)
              (κ.act (Tele.ofList υ)
                (.ap
                  ((Proper.inl (((pre ⋈ dom) ⋈ τ) ⋈ src))
                    ((Proper.inr ((pre ⋈ dom) ⋈ τ)) xsrc))
                  args))
          rw [Subst.act_ap_middle κ (Tele.ofList υ) xsrc args]
          let κβ : Subst C ⌊β⌋ (pre ⋈ dom ⋈ τ ⋈ dst ⋈ Tele.ofList υ) :=
            instOne β (Tele.ofList υ)
              (pre := ((pre ⋈ dom) ⋈ τ) ⋈ dst)
              (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))
          letI : Proper (τ ⋈ dst) := hτDst
          have hrec := diamondAt (τ := τ ⋈ dst) (src := ⌊β⌋)
            (dst := Tele.ofList υ) σ
            (υ := [])
            (Proper.underBinder hτDst β) (Proper.underList hτDst υ)
            (Proper.AppendCoherence.singleton (τ ⋈ dst) β)
            (Proper.AppendCoherence.extendList (τ ⋈ dst) υ)
            κβ (e := κ xsrc)
          unfold Diamond.pushforward at hrec
          have hSubst :
              ((fun {δ : C.Arity} (q : ⌊β⌋ ∋ δ) =>
                  match q with
                  | .here j =>
                      Subst.act κσ (Tele.ofList υ ∷ j.arity)
                        (σ.act (((τ ⋈ src) ⋈ Tele.ofList υ) ∷ j.arity) (args j)))
                : Subst C ⌊β⌋ (((pre ⋈ cod) ⋈ (τ ⋈ dst)) ⋈ Tele.ofList υ))
              =
              ((fun {δ : C.Arity} (q : ⌊β⌋ ∋ δ) =>
                  σ.act (((τ ⋈ dst) ⋈ Tele.ofList υ) ∷ δ) (κβ q))
                : Subst C ⌊β⌋ (((pre ⋈ cod) ⋈ (τ ⋈ dst)) ⋈ Tele.ofList υ)) := by
            funext δ q
            cases q with
            | here j => exact hargs j
            | there q => nomatch q
          rw [hSubst]
          simpa only [κβ, instOne] using hrec
      | tau xτ =>
          -- Stable ambient-depth head.  It is not in the domain of either
          -- substitution; the proof is bookkeeping that shows both sides
          -- rebuild the same τ-head and recurse on the arguments.
          refine (congrArg (Subst.act κσ (Tele.ofList υ))
            (DiamondSite.actBySubst σ hτSrc srcTarget (.tau xτ) args)).trans ?_
          dsimp only [actAt, DiamondSite.embed]
          refine (Subst.act_ap_left κσ (Tele.ofList υ)
            ((Proper.inr (pre ⋈ cod)) xτ)
            (fun j => σ.act (((τ ⋈ src) ⋈ Tele.ofList υ) ∷ j.arity) (args j))).trans ?_
          rw [Proper.extendList_inr_inl (τ ⋈ src) υ (pre ⋈ dom)
            ((Proper.inl τ) xτ)]
          rw [srcTarget.inr_left (pre ⋈ dom) xτ]
          change .ap
              ((Proper.inl (((pre ⋈ cod) ⋈ τ) ⋈ dst))
                ((Proper.inl ((pre ⋈ cod) ⋈ τ))
                  ((Proper.inr (pre ⋈ cod)) xτ)))
              (fun i => Subst.act κσ (Tele.ofList υ ∷ i.arity)
                (σ.act (((τ ⋈ src) ⋈ Tele.ofList υ) ∷ i.arity) (args i)))
            =
            σ.act ((τ ⋈ dst) ⋈ Tele.ofList υ)
              (κ.act (Tele.ofList υ)
                (.ap
                  ((Proper.inl (((pre ⋈ dom) ⋈ τ) ⋈ src))
                    ((Proper.inl ((pre ⋈ dom) ⋈ τ))
                      ((Proper.inr (pre ⋈ dom)) xτ)))
                  args))
          rw [Subst.act_ap_left κ (Tele.ofList υ)
            ((Proper.inr (pre ⋈ dom)) xτ) args]
          have hτdom :
              ((Proper.inl ((pre ⋈ dom) ⋈ τ)) ((Proper.inr (pre ⋈ dom)) xτ)) =
              ((Proper.inr (pre ⋈ dom)) ((Proper.inl τ) xτ))
              := (dstTarget.inr_left (pre ⋈ dom) xτ).symm
          rw [hτdom]
          change .ap
              ((Proper.inl (((pre ⋈ cod) ⋈ τ) ⋈ dst))
                ((Proper.inl ((pre ⋈ cod) ⋈ τ))
                  ((Proper.inr (pre ⋈ cod)) xτ)))
              (fun i => Subst.act κσ (Tele.ofList υ ∷ i.arity)
                (σ.act (((τ ⋈ src) ⋈ Tele.ofList υ) ∷ i.arity) (args i)))
            =
            σ.act ((τ ⋈ dst) ⋈ Tele.ofList υ)
              (.ap
                ((Proper.inl ((pre ⋈ dom) ⋈ (τ ⋈ dst)))
                  ((Proper.inr (pre ⋈ dom)) ((Proper.inl τ) xτ)))
                (fun i => κ.act (Tele.ofList υ ∷ i.arity) (args i)))
          rw [← Proper.extendList_inr_inl (τ ⋈ dst) υ (pre ⋈ dom)
            ((Proper.inl τ) xτ)]
          rw [Subst.act_ap_right σ ((τ ⋈ dst) ⋈ Tele.ofList υ)
            ((Proper.inl (τ ⋈ dst)) ((Proper.inl τ) xτ))
            (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))]
          rw [Proper.extendList_inr_inl (τ ⋈ dst) υ (pre ⋈ cod)
            ((Proper.inl τ) xτ)]
          rw [dstTarget.inr_left (pre ⋈ cod) xτ]
          congr 1
          funext j
          exact hargs j
      | dom z =>
          -- Domain head for `σ`.  Here `σ` fires, producing a term whose
          -- immediate subterms are the pushed-forward arguments.  The needed statement
          -- is exactly the lifted one-binder theorem `liftAt`; afterwards
          -- `hargs` aligns the singleton filler family.
          refine (congrArg (Subst.act κσ (Tele.ofList υ))
            (DiamondSite.actBySubst σ hτSrc srcTarget (.dom z) args)).trans ?_
          dsimp only [actAt, DiamondSite.embed]
          let η : (j : C.Binder β) →
              Expr ((((pre ⋈ cod) ⋈ τ) ⋈ src) ⋈ Tele.ofList υ ∷ j.arity) :=
            fun j => σ.act (((τ ⋈ src) ⋈ Tele.ofList υ) ∷ j.arity) (args j)
          refine (liftAt hτSrc hτDst srcTarget dstTarget
            κσ [] η (σ z)).trans ?_
          let ζ₀ : Subst C ⌊β⌋ ((pre ⋈ cod) ⋈ ((τ ⋈ dst) ⋈ Tele.ofList υ)) :=
            fun q => match q with
            | .here j =>
                Subst.act κσ (Tele.ofList υ ∷ j.arity)
                  (σ.act (((τ ⋈ src) ⋈ Tele.ofList υ) ∷ j.arity)
                    (args j))
          let ζ₁ : Subst C ⌊β⌋ ((pre ⋈ cod) ⋈ ((τ ⋈ dst) ⋈ Tele.ofList υ)) :=
            fun | .here j =>
                σ.act (((τ ⋈ dst) ⋈ Tele.ofList υ) ∷ j.arity)
                  (κ.act (Tele.ofList υ ∷ j.arity) (args j))
          have hζ :
              (fun {δ : C.Arity} (q : ⌊β⌋ ∋ δ) => ζ₀ q)
                =
              (fun {δ : C.Arity} (q : ⌊β⌋ ∋ δ) => ζ₁ q) := by
            funext δ q
            cases q with
            | here j => exact hargs j
            | there q => nomatch q
          change ⟦ ζ₀ ⟧ˢ (σ z)
              =
              σ.act ((τ ⋈ dst) ⋈ Tele.ofList υ)
                (κ.act (Tele.ofList υ)
                  (.ap (Proper.inl (Γ := (τ ⋈ src) ⋈ Tele.ofList υ)
                    (pre ⋈ dom) ((Proper.inr pre) z)) args))
          rw [hζ]
          have hκ :
              κ.act (Tele.ofList υ)
                (.ap
                  (Proper.inl (Γ := (τ ⋈ src) ⋈ Tele.ofList υ)
                    (pre ⋈ dom) ((Proper.inr pre) z))
                  args)
              =
              .ap
                ((Proper.inl (((pre ⋈ dom) ⋈ τ) ⋈ dst))
                  ((Proper.inl ((pre ⋈ dom) ⋈ τ))
                    ((Proper.inl (pre ⋈ dom))
                      ((Proper.inr pre) z))))
                (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j)) := by
            rw [Proper.extendList_inl
              (τ ⋈ src) υ (pre ⋈ dom) ((Proper.inr pre) z)]
            rw [srcTarget.inl (pre ⋈ dom) ((Proper.inr pre) z)]
            exact Subst.act_ap_left κ (Tele.ofList υ)
              ((Proper.inl (pre ⋈ dom))
                ((Proper.inr pre) z)) args
          refine Eq.trans ?_
            (congrArg (σ.act ((τ ⋈ dst) ⋈ Tele.ofList υ)) hκ).symm
          rw [← dstTarget.inl (pre ⋈ dom) ((Proper.inr pre) z)]
          change ⟦ ζ₁ ⟧ˢ (σ z)
              =
              σ.act ((τ ⋈ dst) ⋈ Tele.ofList υ)
                (.ap
                  ((Proper.inl
                      ((pre ⋈ dom) ⋈ (τ ⋈ dst)))
                    (((Proper.inl (pre ⋈ dom)) :
                        (pre ⋈ dom) →ʳ
                          (pre ⋈ dom) ⋈ (τ ⋈ dst))
                      ((Proper.inr pre) z)))
                  (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j)))
          rw [← Proper.extendList_inl
            (τ ⋈ dst) υ (pre ⋈ dom)
            ((Proper.inr pre) z)]
          exact (Subst.act_ap_middle σ
            ((τ ⋈ dst) ⋈ Tele.ofList υ) z
            (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))).symm
      | pre z =>
          -- Stable prefix head.  The prefix is preserved by both substitutions.
          -- The long-looking proof is only reassociation of the same preserved
          -- head through the two composite target contexts.
          refine (congrArg (Subst.act κσ (Tele.ofList υ))
            (DiamondSite.actBySubst σ hτSrc srcTarget (.pre z) args)).trans ?_
          dsimp only [actAt, DiamondSite.embed]
          refine (Subst.act_ap_left κσ (Tele.ofList υ)
            ((Proper.inl (pre ⋈ cod)) ((Proper.inl pre) z))
            (fun j => σ.act (((τ ⋈ src) ⋈ Tele.ofList υ) ∷ j.arity) (args j))).trans ?_
          rw [Proper.extendList_inl (τ ⋈ src) υ (pre ⋈ dom)
            ((Proper.inl pre) z)]
          rw [srcTarget.inl (pre ⋈ dom) ((Proper.inl pre) z)]
          change .ap
              ((Proper.inl (((pre ⋈ cod) ⋈ τ) ⋈ dst))
                ((Proper.inl ((pre ⋈ cod) ⋈ τ))
                  ((Proper.inl (pre ⋈ cod)) ((Proper.inl pre) z))))
              (fun i => Subst.act κσ (Tele.ofList υ ∷ i.arity)
                (σ.act (((τ ⋈ src) ⋈ Tele.ofList υ) ∷ i.arity) (args i)))
            =
            σ.act ((τ ⋈ dst) ⋈ Tele.ofList υ)
              (κ.act (Tele.ofList υ)
                (.ap
                  ((Proper.inl (((pre ⋈ dom) ⋈ τ) ⋈ src))
                    ((Proper.inl ((pre ⋈ dom) ⋈ τ))
                      ((Proper.inl (pre ⋈ dom)) ((Proper.inl pre) z))))
                  args))
          rw [Subst.act_ap_left κ (Tele.ofList υ)
            ((Proper.inl (pre ⋈ dom)) ((Proper.inl pre) z)) args]
          rw [← dstTarget.inl (pre ⋈ dom) ((Proper.inl pre) z)]
          change .ap
              ((Proper.inl (((pre ⋈ cod) ⋈ τ) ⋈ dst))
                ((Proper.inl ((pre ⋈ cod) ⋈ τ))
                  ((Proper.inl (pre ⋈ cod)) ((Proper.inl pre) z))))
              (fun i => Subst.act κσ (Tele.ofList υ ∷ i.arity)
                (σ.act (((τ ⋈ src) ⋈ Tele.ofList υ) ∷ i.arity) (args i)))
            =
            σ.act ((τ ⋈ dst) ⋈ Tele.ofList υ)
              (.ap
                ((Proper.inl ((pre ⋈ dom) ⋈ (τ ⋈ dst)))
                  ((Proper.inl (pre ⋈ dom)) ((Proper.inl pre) z)))
                (fun i => κ.act (Tele.ofList υ ∷ i.arity) (args i)))
          rw [← Proper.extendList_inl (τ ⋈ dst) υ (pre ⋈ dom)
            ((Proper.inl pre) z)]
          rw [Subst.act_ap_left σ ((τ ⋈ dst) ⋈ Tele.ofList υ) z
            (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))]
          rw [Proper.extendList_inl (τ ⋈ dst) υ (pre ⋈ cod)
            ((Proper.inl pre) z)]
          rw [dstTarget.inl (pre ⋈ cod) ((Proper.inl pre) z)]
          congr 1
          funext j
          exact hargs j
termination_by
  ((⟨⟨dom.toList⟩, ⟨src.toList⟩⟩ : InterchangeFuel C),
    (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ))
decreasing_by
  -- The measure is lexicographic: first the pair of active substitution
  -- domains, then expression subterm recursion.  Argument recursion goes right
  -- in the lexicographic product; `src` decreases the second domain; `dom`
  -- decreases the first domain by switching to `liftAt`.
  all_goals
    subst_vars
    first
      | refine Prod.Lex.left _ _ (InterchangeFuel.Lt.right ?_)
        obtain ⟨γ, hmem, hsub⟩ := SlotAt.subWitness xsrc
        exact DomLt.step γ hmem _ hsub
      | refine Prod.Lex.left _ _ (InterchangeFuel.Lt.left ?_)
        obtain ⟨γ, hmem, hsub⟩ := SlotAt.subWitness z
        exact DomLt.step γ hmem _ hsub
      | refine Prod.Lex.right _ ?_
        exact Expr.Subterm.of_arg_ofList_cons υ _ _ _

/- `liftAt` is the proof obligation produced when a `dom` head of `diamondAt`
fires `σ`.  It compares doing `κ` after opening that one binder with first
pushing `κ` into each β-filler.  The β-head branch is the only branch that
changes fuel; the stable branches simply recurse through arguments. -/
private theorem liftAt
    {C : Carrier} {pre τ src dst : Shape C}
    [Proper τ] [Proper src] [Proper dst]
    {υ : List C.Arity}
    (hτSrc : Proper (τ ⋈ src)) (hτDst : Proper (τ ⋈ dst))
    (srcTarget : Proper.AppendCoherence hτSrc)
    (dstTarget : Proper.AppendCoherence hτDst)
    (κ : Subst C src ((pre ⋈ τ) ⋈ dst))
    {β : C.Arity} (χ : List C.Arity)
    (η : (j : C.Binder β) →
      Expr (((pre ⋈ τ) ⋈ src) ⋈ Tele.ofList υ ∷ j.arity))
    (e : Expr ((pre ∷ β) ⋈ Tele.ofList χ)) :
    Lift.sequential hτSrc κ χ η e = Lift.fused hτDst κ χ η e := by
  let lam :  Subst C ⌊β⌋ (pre ⋈ (τ ⋈ src ⋈ Tele.ofList υ)) :=
    instOne β ((τ ⋈ src) ⋈ Tele.ofList υ) (pre := pre) η
  let lam' : Subst C ⌊β⌋ (pre ⋈ (τ ⋈ dst ⋈ Tele.ofList υ)) :=
    instOne β ((τ ⋈ dst) ⋈ Tele.ofList υ)
      (pre := pre) (fun j => κ.act (Tele.ofList υ ∷ j.arity) (η j))
  change κ.act ((Tele.ofList υ) ⋈ Tele.ofList χ)
      (lam.act (Tele.ofList χ) e)
    =
    lam'.act (Tele.ofList χ) e
  match e with
  | .ap (α := γ) head args =>
      -- Structural recursion through the arguments under the current concrete
      -- list of binders `χ`.
      have ih_args : ∀ (j : C.Binder γ),
          Lift.sequential hτSrc κ (j.arity :: χ) η (args j)
            =
          Lift.fused hτDst κ (j.arity :: χ) η (args j) :=
        fun j => liftAt hτSrc hτDst srcTarget dstTarget
          κ (j.arity :: χ) η (args j)
      obtain ⟨site, h_site⟩ :=
        LiftSite.cover head
      subst h_site
      cases site with
      | under xχ =>
          -- Stable local head from `χ`; both substitutions preserve the head
          -- and the proof closes by the argument induction hypotheses.
          refine (congrArg
            (κ.act ((Tele.ofList υ) ⋈ Tele.ofList χ))
            (Subst.act_ap_right lam (Tele.ofList χ) xχ args)).trans ?_
          change κ.act ((Tele.ofList υ) ⋈ Tele.ofList χ)
              (.ap
                ((Proper.inr (((pre ⋈ τ) ⋈ src) ⋈ Tele.ofList υ)) xχ)
                (fun j => lam.act (Tele.ofList χ ∷ j.arity) (args j)))
            =
            lam'.act (Tele.ofList χ)
              (.ap ((Proper.inr (pre ∷ β)) xχ) args)
          rw [← Proper.extendList_inr_inr
            (Tele.ofList υ) χ ((pre ⋈ τ) ⋈ src) xχ]
          refine (Subst.act_ap_right κ
            ((Tele.ofList υ) ⋈ Tele.ofList χ)
            ((Proper.inr (Tele.ofList υ)) xχ)
            (fun j => lam.act (Tele.ofList χ ∷ j.arity) (args j))).trans ?_
          change .ap
              ((Proper.inr ((pre ⋈ τ) ⋈ dst))
                ((Proper.inr (Tele.ofList υ)) xχ))
              (fun j =>
                κ.act (((Tele.ofList υ) ⋈ Tele.ofList χ) ∷ j.arity)
                  (lam.act (Tele.ofList χ ∷ j.arity) (args j)))
            =
            lam'.act (Tele.ofList χ)
              (.ap ((Proper.inr (pre ∷ β)) xχ) args)
          rw [Proper.extendList_inr_inr
            (Tele.ofList υ) χ ((pre ⋈ τ) ⋈ dst) xχ]
          refine Eq.trans ?_
            (Subst.act_ap_right lam' (Tele.ofList χ) xχ args).symm
          congr 1
          funext j
          exact ih_args j
      | beta j =>
          -- The fresh β-head fires the one-binder substitution `lam`.  This
          -- exposes the chosen filler `η j`; the remaining interaction is the
          -- diamond theorem for the singleton argument substitution built from
          -- the application arguments.
          refine (congrArg
            (κ.act ((Tele.ofList υ) ⋈ Tele.ofList χ))
            (Subst.act_ap_middle lam (Tele.ofList χ)
              (.here j) args)).trans ?_
          let θ : ∀ {δ : C.Arity}, (⌊j.arity⌋) ∋ δ →
              Expr (((pre ⋈ τ) ⋈ src) ⋈
                ((Tele.ofList υ) ⋈ Tele.ofList χ) ∷ δ) :=
            fun q => match q with
            | .here k => lam.act (Tele.ofList χ ∷ k.arity) (args k)
          let θ' : ∀ {δ : C.Arity}, (⌊j.arity⌋) ∋ δ →
              Expr (((pre ⋈ τ) ⋈ dst) ⋈
                ((Tele.ofList υ) ⋈ Tele.ofList χ) ∷ δ) :=
            fun q => match q with
            | .here k => lam'.act (Tele.ofList χ ∷ k.arity) (args k)
          have hfill : ∀ (k : C.Binder j.arity),
              κ.act (((Tele.ofList υ) ⋈ Tele.ofList χ) ∷ k.arity)
                  (θ (.here k))
                =
              θ' (.here k) := by
            intro k
            exact ih_args k
          let θSubst : Subst C ⌊j.arity⌋ (pre ⋈ τ ⋈ src ⋈ Tele.ofList υ ⋈ Tele.ofList χ) :=
            instOne j.arity (Tele.ofList χ)
              (pre := ((pre ⋈ τ) ⋈ src) ⋈ Tele.ofList υ)
              (fun k => lam.act (Tele.ofList χ ∷ k.arity) (args k))
          have hrec := diamondAt (pre := pre ⋈ τ) (dom := src)
            (cod := dst) (τ := Tele.ofList υ) (src := ⌊j.arity⌋)
            (dst := Tele.ofList χ) κ
            (υ := [])
            (Proper.extendList (Tele.ofList υ) [j.arity])
            (Proper.extendList (Tele.ofList υ) χ)
            (Proper.AppendCoherence.extendList (Tele.ofList υ) [j.arity])
            (Proper.AppendCoherence.extendList (Tele.ofList υ) χ)
            θSubst (e := η j)
          unfold Diamond.pushforward at hrec
          refine Eq.trans hrec.symm ?_
          have hSubst :
              ((fun {δ : C.Arity} (q : ⌊j.arity⌋ ∋ δ) =>
                  κ.act (((Tele.ofList υ) ⋈ Tele.ofList χ) ∷ δ)
                    (θSubst q))
                : Subst C ⌊j.arity⌋
                    ((((pre ⋈ τ) ⋈ dst) ⋈ Tele.ofList υ) ⋈ Tele.ofList χ))
              =
              ((fun {δ : C.Arity} (q : ⌊j.arity⌋ ∋ δ) =>
                  θ' q)
                : Subst C ⌊j.arity⌋
                    ((((pre ⋈ τ) ⋈ dst) ⋈ Tele.ofList υ) ⋈ Tele.ofList χ)) := by
            funext δ q
            cases q with
            | here k => exact hfill k
            | there q => nomatch q
          rw [hSubst]
          change ⟦((fun {α : C.Arity} (q : ⌊j.arity⌋ ∋ α) =>
                  match q with
                  | .here i => lam'.act (Tele.ofList χ ∷ i.arity) (args i))
                : Subst C ⌊j.arity⌋
                    (((pre ⋈ (τ ⋈ dst)) ⋈ Tele.ofList υ) ⋈ Tele.ofList χ))⟧ˢ
                (lam' (.here j))
              =
              lam'.act (Tele.ofList χ)
                (.ap
                  ((Proper.inl (pre ⋈ ⌊β⌋))
                    ((Proper.inr pre) (.here j)))
                  args)
          symm
          conv => lhs; unfold Subst.act
          rw [Subst.threeway_inl_dom]
          simp only
          congr
          funext α q
          cases q with
          | here i => rfl
          | there q => nomatch q
      | pre z =>
          -- Stable prefix head.  As in the `pre` branch of `diamondAt`, this
          -- is mostly witness reassociation plus the argument recursion.
          refine (congrArg
            (κ.act ((Tele.ofList υ) ⋈ Tele.ofList χ))
            (Subst.act_ap_left lam (Tele.ofList χ) z args)).trans ?_
          rw [Proper.extendList_inl (τ ⋈ src) υ pre z]
          rw [srcTarget.inl pre z]
          change κ.act ((Tele.ofList υ) ⋈ Tele.ofList χ)
              (.ap
                ((Proper.inl (((pre ⋈ τ) ⋈ src) ⋈ Tele.ofList υ))
                  ((Proper.inl ((pre ⋈ τ) ⋈ src))
                    ((Proper.inl (pre ⋈ τ))
                      ((Proper.inl pre) z))))
                (fun i => lam.act (Tele.ofList χ ∷ i.arity) (args i)))
            =
            lam'.act (Tele.ofList χ)
              (.ap
                ((Proper.inl (pre ∷ β)) ((Proper.inl pre) z))
                args)
          rw [← Proper.extendList_inl
            (Tele.ofList υ) χ ((pre ⋈ τ) ⋈ src)
            ((Proper.inl (pre ⋈ τ)) ((Proper.inl pre) z))]
          change κ.act ((Tele.ofList υ) ⋈ Tele.ofList χ)
              (.ap
                ((Proper.inl ((pre ⋈ τ) ⋈ src))
                  ((Proper.inl (pre ⋈ τ))
                    ((Proper.inl pre) z)))
                (fun i => lam.act (Tele.ofList χ ∷ i.arity) (args i)))
            =
            lam'.act (Tele.ofList χ)
              (.ap
                ((Proper.inl (pre ∷ β)) ((Proper.inl pre) z))
                args)
          rw [Subst.act_ap_left κ
            ((Tele.ofList υ) ⋈ Tele.ofList χ)
            ((Proper.inl pre) z)]
          refine Eq.trans ?_
            (Subst.act_ap_left lam' (Tele.ofList χ) z args).symm
          congr 1
          · rw [← dstTarget.inl pre z]
            rw [Proper.extendList_inl
              (τ ⋈ dst) υ pre z]
            change
              Proper.inl (Γ := (Tele.ofList υ) ⋈ Tele.ofList χ)
                (pre ⋈ (τ ⋈ dst)) ((Proper.inl pre) z)
              =
              Proper.inl (Γ := Tele.ofList χ)
                ((pre ⋈ (τ ⋈ dst)) ⋈ Tele.ofList υ)
                ((Proper.inl (pre ⋈ (τ ⋈ dst))) ((Proper.inl pre) z))
            rw [← Proper.extendList_inl
              (Tele.ofList υ) χ
              (pre ⋈ (τ ⋈ dst))
              ((Proper.inl pre) z)]
          funext k
          exact ih_args k
termination_by
  ((⟨⟨[β]⟩, ⟨src.toList⟩⟩ : InterchangeFuel C),
    (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ))
decreasing_by
  -- In the β branch we call back to `diamondAt` with the selected binder arity
  -- as a strictly smaller first fuel component.  The other recursive calls are
  -- ordinary expression-subterm calls under the extended `χ` list.
  all_goals
    subst_vars
    first
      | refine Prod.Lex.left _ _ (InterchangeFuel.Lt.left_swap ?_)
        exact DomLt.step β (List.Mem.head _) j.arity ⟨j, rfl⟩
      | refine Prod.Lex.right _ ?_
        exact Expr.Subterm.of_arg_ofList_cons χ _ _ _

end

/-- **`act_comp`** — action by a composite substitution factors into two actions.

This is the public composition theorem for `Subst.act`.  The proof is now a
small expression recursion with three semantic head cases:

* τ-heads are preserved by both substitutions, so we recurse on arguments;
* pre-heads are also preserved, again with argument recursion;
* dom-heads are the real case.  There `σ` fires first, and `diamondAt` says
  that subsequently acting by `θ` commutes with the one-binder instantiation
  generated by that firing.
-/
theorem Subst.act_comp
    {C : Carrier} {pre dom mid cod : Shape C}
    [Proper dom] [Proper mid] [Proper cod]
    (σ : Subst C dom (pre ⋈ mid)) (θ : Subst C mid (pre ⋈ cod))
    (τ : Shape C) [Proper τ] (e : Expr ((pre ⋈ dom) ⋈ τ)) :
  act (comp σ θ) τ e = θ.act τ (σ.act τ e)
  := by
  match e with
  | .ap (α := β) head args =>
    obtain ⟨site, h_site⟩ := Subst.isReinject head
    subst h_site
    cases site with
    | right x =>
      -- Current-depth variable: both sides rebuild the same head and compare
      -- the recursively transformed argument family.
      refine (Subst.act_ap_right (comp σ θ) τ x args).trans ?_
      change
        .ap ((Proper.inr (pre ⋈ cod)) x)
          (fun j => act (comp σ θ) (τ ∷ j.arity) (args j))
        =
        θ.act τ
          (σ.act τ
            (.ap ((Proper.inr (pre ⋈ dom)) x) args))
      rw [Subst.act_ap_right σ τ x args]
      rw [Subst.act_ap_right θ τ x (fun i => σ.act (τ ∷ i.arity) (args i))]
      congr 1
      funext i
      exact Subst.act_comp σ θ (τ ∷ i.arity) (args i)
    | middle y =>
      -- Substituted variable: the composite filler is definitionally
      -- `θ.act ⌊β⌋ (σ y)`.  The remaining question is whether `θ` commutes
      -- with the instantiation created by firing `σ`; this is exactly the
      -- nil-τ singleton-source specialization of `diamondAt`.
      refine (Subst.act_ap_middle (Subst.comp σ θ) τ y args).trans ?_
      have ih_args :=
        fun (i : C.Binder β) => Subst.act_comp σ θ (τ ∷ i.arity) (args i)
      simp only [ih_args]
      change
        ⟦((fun
          | .here i =>
              θ.act (τ ∷ i.arity)
                (σ.act (τ ∷ i.arity) (args i)))
          : Subst C ⌊β⌋ ((pre ⋈ cod) ⋈ τ))⟧ˢ
          (θ.act ⌊β⌋ (σ y))
        =
        θ.act τ
          (σ.act τ
            (.ap ((Proper.inl _) (Proper.inr _ y)) args))
      rw [Subst.act_ap_middle σ τ y args]
      let κβ : Subst C ⌊β⌋ (pre ⋈ mid ⋈ τ) := instOne β τ (fun i => σ.act (τ ∷ i.arity) (args i))
      have h := diamondAt
        (τ := Shape.nil)
        θ
        (υ := [])
        (inferInstanceAs (Proper ⌊β⌋)) (inferInstanceAs (Proper τ))
        (Proper.AppendCoherence.nil ⌊β⌋) (Proper.AppendCoherence.nil τ)
        κβ (e := σ y)
      unfold Diamond.pushforward at h
      unfold κβ at h
      unfold instOne at h
      dsimp only at h
      change
        Subst.act (((fun {δ : C.Arity} (q : ⌊β⌋ ∋ δ) =>
            θ.act (τ ∷ δ)
              (match q with
              | .here i => σ.act (τ ∷ i.arity) (args i)))
          ))
          (Tele.ofList []) (θ.act ⌊β⌋ (σ y))
        =
        θ.act τ
          (Subst.act (((fun {δ : C.Arity} (q : ⌊β⌋ ∋ δ) =>
              match q with
              | .here i => σ.act (τ ∷ i.arity) (args i))
            ))
            (Tele.ofList []) (σ y)) at h
      have hFiller :
          ((fun {δ : C.Arity} (q : ⌊β⌋ ∋ δ) =>
              θ.act (τ ∷ δ)
                (match q with
                | .here i => σ.act (τ ∷ i.arity) (args i))))
          =
          ((fun {δ : C.Arity} (q : ⌊β⌋ ∋ δ) =>
              match q with
              | .here i =>
                  θ.act (τ ∷ i.arity)
                    (σ.act (τ ∷ i.arity) (args i))))
:= by
        funext δ q
        cases q with
        | here i => rfl
        | there q => nomatch q
      rw [hFiller] at h
      exact h
    | left z =>
      -- Prefix variable: neither substitution replaces the head.  Only the
      -- argument family is transformed recursively.
      refine (Subst.act_ap_left (comp σ θ) τ z args).trans ?_
      change
        .ap ((Proper.inl (pre ⋈ cod)) ((Proper.inl pre) z))
          (fun i => Subst.act (comp σ θ) (τ ∷ i.arity) (args i))
        =
        θ.act τ
          (σ.act τ
            (.ap
              ((Proper.inl (pre ⋈ dom)) ((Proper.inl pre) z))
              args))
      rw [Subst.act_ap_left σ τ z args]
      rw [Subst.act_ap_left θ τ z (fun i => σ.act (τ ∷ i.arity) (args i))]
      congr 1
      funext i
      exact Subst.act_comp σ θ (τ ∷ i.arity) (args i)
termination_by (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg head args _
