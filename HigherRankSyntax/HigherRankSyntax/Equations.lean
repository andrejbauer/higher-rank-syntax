import HigherRankSyntax.Subst

/-!
# Equations of the substitution action

Auxiliary equations for the three relative-monad laws, built from
**computation lemmas**: each takes `Subst.act` on an `Expr.ap` with a
specific head (τ-side, dom-side, pre-side) and reduces the classify
dispatch to a clean right-hand side.  The reflection lemmas
`Proper.classify_inr` / `classify_inl` are the rewriting handles.

## The three monad laws

* `Subst.act_id` — `(Subst.id Γ).act τ e = e` (unit_right).
* `Subst.act_η` — `(toSubst f).act ⌊α⌋ (Expr.η p) = f p` (unit_left).
* `Subst.act_kcomp` — Kleisli composition factors (comp_lift).
-/


/-! ## Computation lemmas — `Subst.act` on a specific apply head

One lemma per `SubstSite` case.  Each unfolds `Subst.act` and rewrites
with the matching `Subst.classifySlot_*` reflection lemma.  The LHS uses
`Subst.embed`/`Subst.embedInner` so rewriting matches goals whose head is
already in embedded form. -/

/-- `σ.act` on an apply whose head sits in the `inner` accumulator. -/
theorem Subst.act_ap_inner
    {C : Carrier} {pre dom cod : Shape C} [Proper dom] [Proper cod]
    (σ : Subst C pre dom cod) (outer : Shape C) [Proper outer]
    (inner : List C.Arity)
    {α} (y : ListSlotAt inner α)
    (args : (i : C.Binder α) → Expr (pre ⧺ dom ⧺ outer ⧺ Tele.ofList inner ∷ i.arity)) :
  σ.act outer inner
      (.ap (Subst.embedInner (pre := pre) (cod := dom) (outer := outer) y) args)
    = .ap (Subst.embedInner (pre := pre) (cod := cod) (outer := outer) y)
        (fun j => σ.act outer (j.arity :: inner) (args j))
  := by
  conv => lhs; unfold Subst.act
  rw [Subst.classifySlot_embedInner]

/-- `σ.act` on an apply whose head sits in `outer`. -/
theorem Subst.act_ap_outer
    {C : Carrier} {pre dom cod : Shape C} [Proper dom] [Proper cod]
    (σ : Subst C pre dom cod) (outer : Shape C) [Proper outer]
    (inner : List C.Arity)
    {α} (x : outer ∋ α)
    (args : (i : C.Binder α) → Expr (pre ⧺ dom ⧺ outer ⧺ Tele.ofList inner ∷ i.arity)) :
  σ.act outer inner
      (.ap (Subst.embed (pre := pre) (dom := dom) (outer := outer) (.outer x)) args)
    = .ap ((Proper.inl (pre ⧺ cod ⧺ outer))
            ((Proper.inr (pre ⧺ cod)) x))
        (fun j => σ.act outer (j.arity :: inner) (args j))
  := by
  show σ.act outer inner
      (.ap ((Proper.inl (pre ⧺ dom ⧺ outer)) ((Proper.inr (pre ⧺ dom)) x)) args)
    = _
  conv => lhs; unfold Subst.act
  rw [Subst.classifySlot_outer]

/-- `σ.act` on an apply whose head sits in `dom`: fires the substitution
and inserts the recursively-acted args as the kit. -/
theorem Subst.act_ap_dom
    {C : Carrier} {pre dom cod : Shape C} [Proper dom] [Proper cod]
    (σ : Subst C pre dom cod) (outer : Shape C) [Proper outer]
    (inner : List C.Arity)
    {α} (z : dom ∋ α)
    (args : (i : C.Binder α) → Expr (pre ⧺ dom ⧺ outer ⧺ Tele.ofList inner ∷ i.arity)) :
  σ.act outer inner
      (.ap (Subst.embed (pre := pre) (dom := dom) (outer := outer) (.dom z)) args)
    = (Subst.inst (pre := pre ⧺ cod) (cod := outer ⧺ Tele.ofList inner)
        ⌊α⌋ (fun q => match q with
          | .here i => σ.act outer (i.arity :: inner) (args i))).act
        Shape.nil [] (σ z)
  := by
  show σ.act outer inner
      (.ap ((Proper.inl (pre ⧺ dom ⧺ outer))
            ((Proper.inl (pre ⧺ dom)) ((Proper.inr pre) z))) args)
    = _
  conv => lhs; unfold Subst.act
  rw [Subst.classifySlot_dom]
  rfl

/-- `σ.act` on an apply whose head sits in `pre`: rebuilds with the
pre-side weakened all the way back. -/
theorem Subst.act_ap_pre
    {C : Carrier} {pre dom cod : Shape C} [Proper dom] [Proper cod]
    (σ : Subst C pre dom cod) (outer : Shape C) [Proper outer]
    (inner : List C.Arity)
    {α} (w : pre ∋ α)
    (args : (i : C.Binder α) → Expr (pre ⧺ dom ⧺ outer ⧺ Tele.ofList inner ∷ i.arity)) :
  σ.act outer inner
      (.ap (Subst.embed (pre := pre) (dom := dom) (outer := outer) (.pre w)) args)
    = .ap ((Proper.inl (pre ⧺ cod ⧺ outer))
            ((Proper.inl (pre ⧺ cod)) ((Proper.inl pre) w)))
        (fun j => σ.act outer (j.arity :: inner) (args j))
  := by
  show σ.act outer inner
      (.ap ((Proper.inl (pre ⧺ dom ⧺ outer))
            ((Proper.inl (pre ⧺ dom)) ((Proper.inl pre) w))) args)
    = _
  conv => lhs; unfold Subst.act
  rw [Subst.classifySlot_pre]

/-! ## Auxiliary: η-action on an inner-side slot -/

/-- Acting on the η-expansion of an inner-side slot reproduces the η in
the target shape.  By WF recursion on the slot's arity `α`. -/
theorem Subst.act_η_inner
    {C : Carrier} {pre dom cod : Shape C}
    [Proper dom] [Proper cod]
    (σ : Subst C pre dom cod) (outer : Shape C) [Proper outer]
    (inner : List C.Arity)
    {α} (y : ListSlotAt inner α) :
  σ.act outer (α :: inner)
      (.η (Subst.embedInner (pre := pre) (cod := dom) (outer := outer) y))
    = .η (Subst.embedInner (pre := pre) (cod := cod) (outer := outer) y)
  := by
  rw [Expr.η.eq_1]
  -- `.there (embedInner y) = embedInner (.there y)` definitionally.
  change σ.act outer (α :: inner)
      (.ap (Subst.embedInner (pre := pre) (cod := dom) (outer := outer)
              (.there y : ListSlotAt (α :: inner) α))
           (fun i => .η (.here i))) = _
  rw [Subst.act_ap_inner σ outer (α :: inner)
        (.there y : ListSlotAt (α :: inner) α)
        (fun i => .η (.here i))]
  rw [Expr.η.eq_1]
  congr 1
  funext i
  exact Subst.act_η_inner σ outer (α :: inner)
          (y := @ListSlotAt.here C α inner i)
termination_by α
decreasing_by exact ⟨i, rfl⟩

/-! ## Instantiation laws: identity action and β-for-η -/

/-- Identity instantiation acts as the identity, given the β-for-η
property at the immediate sub-arities of the head arity.  The proof
recurses over the expression. -/
private theorem idOf
    {C : Carrier} (α : C.Arity) (Δ : Shape C)
    (hη : ∀ (i : C.Binder α), ∀ {pre cod : Shape C} [Proper cod]
      (ι : ∀ {β : C.Arity}, (⌊i.arity⌋) ∋ β → Expr (pre ⧺ cod ∷ β))
      (p : pre ∋ i.arity),
      ⟦Subst.inst (⌊i.arity⌋) ι⟧ˢ (.η p)
        = .ap ((Proper.inl pre) p) (fun j => ι (.here j))) :
  ∀ (τ : List C.Arity) (e : Expr ((Δ ∷ α) ⧺ Tele.ofList τ)),
    (Subst.instId Δ α).act Shape.nil τ e = e
  | τ, .ap (α := β) head argFam => by
      have ih_all : ∀ (k : C.Binder β),
          (Subst.instId Δ α).act Shape.nil (k.arity :: τ) (argFam k) = argFam k :=
        fun k => idOf α Δ hη (k.arity :: τ) (argFam k)
      obtain ⟨s, h⟩ := Subst.coverSlot
        (pre := Δ) (dom := ⌊α⌋) (outer := Shape.nil) τ head
      subst h
      cases s with
      | outer x => nomatch x
      | inner y =>
          refine (Subst.act_ap_inner (Subst.instId Δ α) Shape.nil τ y argFam).trans ?_
          congr
          funext k
          exact ih_all k
      | dom z =>
          cases z with
          | here i =>
              refine (Subst.act_ap_dom
                (Subst.instId Δ α) Shape.nil τ (.here i) argFam).trans ?_
              rw [show (Subst.instId Δ α).sub (.here i)
                    = @Expr.η C (Δ ∷ α) i.arity (.here i) from rfl]
              refine (hη i (pre := Δ ∷ α) (cod := Tele.ofList τ)
                (ι := _) (p := .here i)).trans ?_
              change
                Expr.ap ((Proper.inl (Δ ∷ α))
                    (.here i))
                  (fun k => (Subst.instId Δ α).act Shape.nil (k.arity :: τ) (argFam k))
                =
                Expr.ap ((Proper.inl (Δ ∷ α))
                    (.here i)) argFam
              congr 1
              funext k
              exact ih_all k
          | there z' => nomatch z'
      | pre w =>
          refine (Subst.act_ap_pre (Subst.instId Δ α) Shape.nil τ w argFam).trans ?_
          change
            Expr.ap ((Proper.inl (Δ ∷ α))
                ((Proper.inl Δ) w))
              (fun k => (Subst.instId Δ α).act Shape.nil (k.arity :: τ) (argFam k))
            =
            Expr.ap ((Proper.inl (Δ ∷ α))
                ((Proper.inl Δ) w)) argFam
          congr 1
          funext k
          exact ih_all k
termination_by τ e => (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg head argFam _

-- β-for-η and identity-act, proved together by well-founded recursion on
-- arities: β-for-η at α invokes identity-act at i.arity ≺ α, and identity-act
-- at α invokes β-for-η at i.arity ≺ α (via `idOf`'s hypothesis).
mutual

/-- β-for-η for a one-binder instantiation: instantiating the η-expansion
of a pre-slot exposes the kit. -/
theorem Subst.act_inst.η
    {C : Carrier} {pre cod : Shape C} [Proper cod]
    {α} (ι : ∀ {β : C.Arity}, ⌊α⌋ ∋ β → Expr (pre ⧺ cod ∷ β))
    (p : pre ∋ α) :
  ⟦Subst.inst ⌊α⌋ ι⟧ˢ (.η p)
    = .ap ((Proper.inl pre) p) (fun i => ι (.here i))
  := by
  rw [Expr.η.eq_1]
  -- `.there p = embed (.pre p)` (rfl through instId Proper.inl chain).
  change (Subst.inst ⌊α⌋ ι).act Shape.nil []
      (.ap (Subst.embed (pre := pre) (dom := ⌊α⌋) (outer := Shape.nil) (.pre p))
           (fun i => .η (.here i))) = _
  rw [Subst.act_ap_pre]
  -- target head `(Proper.inl _) ((Proper.inl _) ((Proper.inl _) p)) = (Proper.inl pre) p` rfl.
  congr 1
  funext i
  -- Goal: σ.act Shape.nil [i.arity] (.η (.here i)) = ι (.here i).
  rw [Expr.η.eq_1]
  -- `.there .here i = embed (.dom (.here i))` rfl.
  change (Subst.inst ⌊α⌋ ι).act Shape.nil [i.arity]
      (.ap (Subst.embed (pre := pre) (dom := ⌊α⌋) (outer := Shape.nil)
              (.dom (.here i)))
           (fun k => .η (.here k))) = _
  rw [Subst.act_ap_dom]
  -- σ.sub (.here i) = ι (.here i) rfl.
  rw [show (Subst.inst ⌊α⌋ ι).sub (.here i) = ι (.here i) from rfl]
  sorry  -- TODO: rewrite kit body via act_η_inner, then apply act_inst.id
termination_by α
decreasing_by exact ⟨i, rfl⟩

/-- Identity instantiation acts as the identity. -/
theorem Subst.act_inst.id
    {C : Carrier} (α : C.Arity) (Δ : Shape C) :
  ∀ (τ : List C.Arity) (e : Expr ((Δ ∷ α) ⧺ Tele.ofList τ)),
    (Subst.instId Δ α).act Shape.nil τ e = e
  :=
  fun τ e =>
    idOf α Δ (fun i => Subst.act_inst.η) τ e
termination_by α
decreasing_by exact ⟨i, rfl⟩

end

/-! ## Monad laws -/

/-- **`act_id`** — the identity substitution acts as the identity.
Translates to `lift η = 𝟙` (unit_right).  Generalised over τ so the
recursive call on each arg fits the same statement. -/
theorem Subst.act_id
    {C : Carrier} (Γ : Shape C) [Proper Γ]
    (τ : List C.Arity)
    (e : Expr (Γ ⧺ Tele.ofList τ)) :
  (Subst.id Γ).act Shape.nil τ e = e
  := by
  match e with
  | .ap (α := β) head args =>
    obtain ⟨s, h⟩ := Subst.coverSlot
      (pre := Shape.nil) (dom := Γ) (outer := Shape.nil) τ head
    subst h
    cases s with
    | pre w => nomatch w
    | outer x => nomatch x
    | inner y =>
        refine (Subst.act_ap_inner (Subst.id Γ) Shape.nil τ y args).trans ?_
        congr 1
        funext k
        exact Subst.act_id Γ (k.arity :: τ) (args k)
    | dom z => sorry  -- TODO: bridge embed(.dom z) ≡ (Proper.inl Γ) z via inr_nil_id
termination_by (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg head args _

/-- **`act_η`** — acting on an η-expansion reduces to applying `f`.
Translates to `lift f ∘ η = f` (unit_left). -/
theorem Subst.act_η
    {C : Carrier} {Γ Δ : Shape C} [Proper Γ] [Proper Δ]
    (f : ∀ {β : C.Arity}, Γ ∋ β → Expr (Δ ∷ β))
    (α : C.Arity) (p : Γ ∋ α) :
  (toSubst f).act Shape.nil [α] (.η p) = f p
  := by
  sorry  -- TODO: rewrite using coverSlot + act_ap_dom + act_inst.η

/-- `Expr.Subterm.of_arg` repackaged for the descent shape
`Γ ⧺ Tele.ofList (j.arity :: ρ)`. -/
private theorem Expr.Subterm.of_arg_ofList_cons
    {C : Carrier} {Γ : Shape C}
    (ρ : List C.Arity) {α}
    (head : Γ ⧺ Tele.ofList ρ ∋ α)
    (args : (i : C.Binder α) → Expr (Γ ⧺ Tele.ofList ρ ∷ i.arity))
    (j : C.Binder α) :
  Expr.Subterm
    ⟨Γ ⧺ Tele.ofList (j.arity :: ρ), args j⟩
    ⟨Γ ⧺ Tele.ofList ρ, .ap head args⟩
  := by
  simpa [Shape.extList, Shape.ext, Tele.comp, Tele.ofList] using
    (Expr.Subterm.of_arg head args j)

/-- A slot of the singleton list `[α]` has sub-arity α. -/
private theorem ListSlotAt.sub_single
    {C : Carrier} {α β : C.Arity} (x : (⌊α⌋ : Shape C) ∋ β) :
  Carrier.Sub β α
  := by
  cases x with
  | here i => exact ⟨i, rfl⟩
  | there z => nomatch z

/-! ## Statement facades for the interchange lemmas -/

/-- One-binder instantiation, written in binder-indexed form rather than
singleton-slot form. -/
private abbrev instOne
    {C : Carrier} {pre : Shape C} (α : C.Arity) (cod : Shape C)
    (f : (i : C.Binder α) → Expr (pre ⧺ cod ∷ i.arity)) :
  Subst C pre ⌊α⌋ cod
  :=
  Subst.inst ⌊α⌋ (fun q => match q with | .here i => f i)

/-- LHS of `underListAt`: σ acts on `e`, then `κ' = σ-acted ι` instantiates the
α-slot.  Reads as "act σ first, then instantiate". -/
private abbrev UnderList.actThenInst
    {C : Carrier} {pre dom cod : Shape C} [Proper dom] [Proper cod]
    (σ : Subst C pre dom cod) {α} {τ : List C.Arity} (ρ υ : List C.Arity)
    (ι : ∀ {β : C.Arity}, ⌊α⌋ ∋ β → Expr (pre ⧺ dom ⧺ᴸ τ ⧺ᴸ ρ ∷ β))
    (e : Expr ((pre ⧺ dom ⧺ᴸ τ ∷ α) ⧺ᴸ υ))
  :=
  (instOne (pre := pre ⧺ cod ⧺ᴸ τ) α (Tele.ofList ρ)
      (fun i =>
        σ.act (i.arity :: ρ ++ τ) (ι (.here i)))).act
    υ (σ.act (υ ++ (α :: τ)) e)

/-- RHS of `underListAt`: `κ = raw ι` instantiates the α-slot, then σ acts at the
combined depth `(τ ⧺ ρ) ⧺ υ`.  Reads as "instantiate first, then act σ". -/
private abbrev UnderList.instThenAct
    {C : Carrier} {pre dom cod : Shape C} [Proper dom] [Proper cod]
    (σ : Subst C pre dom cod) {α} {τ : List C.Arity} (ρ υ : List C.Arity)
    (ι : ∀ {β : C.Arity}, ⌊α⌋ ∋ β → Expr (pre ⧺ dom ⧺ᴸ τ ⧺ᴸ ρ ∷ β))
    (e : Expr ((pre ⧺ dom ⧺ᴸ τ ∷ α) ⧺ᴸ υ))
  :=
  σ.act (υ ++ ρ ++ τ)
    ((instOne α (Tele.ofList ρ)
        (fun i => ι (.here i))).act υ e)

/-- LHS of `preNaturalityLiftAt`: apply `lam` (β-instantiator from η), then apply
`κ` (α-instantiator from ι) at the outer depth. -/
private abbrev PreLift.sequential
    {C : Carrier} {pre τ : Shape C} [Proper τ]
    {α β : C.Arity} (ρ υ χ : List C.Arity)
    (ι : ∀ {δ : C.Arity}, ⌊α⌋ ∋ δ → Expr (pre ⧺ τ ⧺ Tele.ofList ρ ∷ δ))
    (η : (j : C.Binder β) → Expr ((pre ⧺ τ ∷ α) ⧺ Tele.ofList υ ∷ j.arity))
    (e : Expr ((pre ∷ β) ⧺ Tele.ofList χ))
  :=
  (instOne α (Tele.ofList ρ)
      (fun i => ι (.here i))).act ((Tele.ofList υ) ⧺ Tele.ofList χ)
    ((instOne β ((τ ∷ α) ⧺ Tele.ofList υ) η).act
      (Tele.ofList χ) e)

/-- RHS of `preNaturalityLiftAt`: apply a single `lam' = κ-acted η` (β-instantiator
that already factors κ into each filler). -/
private abbrev PreLift.fused
    {C : Carrier} {pre τ : Shape C} [Proper τ]
    {α β : C.Arity} (ρ υ χ : List C.Arity)
    (ι : ∀ {δ : C.Arity}, ⌊α⌋ ∋ δ → Expr (pre ⧺ τ ⧺ Tele.ofList ρ ∷ δ))
    (η : (j : C.Binder β) → Expr ((pre ⧺ τ ∷ α) ⧺ Tele.ofList υ ∷ j.arity))
    (e : Expr ((pre ∷ β) ⧺ Tele.ofList χ))
  :=
  (instOne β ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ)
      (fun j =>
        (instOne α (Tele.ofList ρ)
            (fun i => ι (.here i))).act (Tele.ofList υ ∷ j.arity) (η j))).act
    (Tele.ofList χ) e

/-- LHS of `preNaturalityAt`: `κ` (α-instantiator from raw ι at the
`dom`-stack) is applied, then σ acts. -/
private abbrev PreNaturality.sequential
    {C : Carrier} {pre dom cod : Shape C} [Proper dom] [Proper cod]
    (σ : Subst C pre dom cod) {α} (ρ υ : List C.Arity)
    (ι : ∀ {β : C.Arity}, ⌊α⌋ ∋ β → Expr (pre ⧺ dom ⧺ Tele.ofList ρ ∷ β))
    (e : Expr ((pre ∷ α) ⧺ Tele.ofList υ))
  :=
  σ.act ((Tele.ofList ρ) ⧺ Tele.ofList υ)
    ((instOne α (dom ⧺ Tele.ofList ρ)
        (fun i => ι (.here i))).act (Tele.ofList υ) e)

/-- RHS of `preNaturalityAt`: `κ' = σ-acted ι` (α-instantiator at the
`cod`-stack) is applied directly. -/
private abbrev PreNaturality.fused
    {C : Carrier} {pre dom cod : Shape C} [Proper dom] [Proper cod]
    (σ : Subst C pre dom cod) {α} (ρ υ : List C.Arity)
    (ι : ∀ {β : C.Arity}, ⌊α⌋ ∋ β → Expr (pre ⧺ dom ⧺ Tele.ofList ρ ∷ β))
    (e : Expr ((pre ∷ α) ⧺ Tele.ofList υ))
  :=
  (instOne α (cod ⧺ Tele.ofList ρ)
      (fun i => σ.act (Tele.ofList ρ ∷ i.arity) (ι (.here i)))).act
    (Tele.ofList υ) e

/-- LHS of `interchange`: σ acts at depth `⌊α⌋ ⧺ ρ`, then `κ' = σ-acted ι`
(τ-shaped instantiator) is applied. -/
private abbrev Interchange.actThenInst
    {C : Carrier} {pre dom cod τ : Shape C} [Proper dom] [Proper cod] [Proper τ]
    (σ : Subst C pre dom cod) {α}
    (ι : ∀ {β : C.Arity}, ⌊α⌋ ∋ β → Expr (pre ⧺ dom ⧺ τ ∷ β))
    (ρ : List C.Arity) (e : Expr (pre ⧺ dom ⧺ ⌊α⌋ ⧺ Tele.ofList ρ))
  :=
  (instOne α τ
      (fun i => σ.act (τ ∷ i.arity) (ι (.here i)))).act
    (Tele.ofList ρ)
    (σ.act (⌊α⌋ ⧺ Tele.ofList ρ) e)

/-- RHS of `interchange`: `κ = raw ι` (τ-shaped instantiator) is applied, then σ
acts at depth `τ ⧺ ρ`. -/
private abbrev Interchange.instThenAct
    {C : Carrier} {pre dom cod τ : Shape C} [Proper dom] [Proper cod] [Proper τ]
    (σ : Subst C pre dom cod) {α}
    (ι : ∀ {β : C.Arity}, ⌊α⌋ ∋ β → Expr (pre ⧺ dom ⧺ τ ∷ β))
    (ρ : List C.Arity) (e : Expr (pre ⧺ dom ⧺ ⌊α⌋ ⧺ Tele.ofList ρ))
  :=
  σ.act (τ ⧺ Tele.ofList ρ)
    ((instOne α τ
        (fun i => ι (.here i))).act (Tele.ofList ρ) e)

/-- Two active substitution-domain fuels, considered up to swapping.  The mutual
interchange proof either descends in one fuel component or keeps the fuel fixed
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

mutual

/-- The `UnderList.{actThenInst,instThenAct}` reductions agree at every depth υ.
Mutually recursive with `preNaturalityLiftAt`. -/
private theorem underListAt
    {C : Carrier} {pre dom cod τ : Shape C} [Proper dom] [Proper cod] [Proper τ]
    (σ : Subst C pre dom cod) {α} (ρ υ : List C.Arity)
    (ι : ∀ {β : C.Arity}, ⌊α⌋ ∋ β → Expr (pre ⧺ dom ⧺ τ ⧺ Tele.ofList ρ ∷ β))
    (e : Expr ((pre ⧺ dom ⧺ τ ∷ α) ⧺ Tele.ofList υ)) :
  UnderList.actThenInst σ ρ υ ι e = UnderList.instThenAct σ ρ υ ι e
  := by
  let κ : Subst C (pre ⧺ dom ⧺ τ) ⌊α⌋ (Tele.ofList ρ) :=
    instOne α (Tele.ofList ρ) (fun i => ι (.here i))
  let κ' : Subst C (pre ⧺ cod ⧺ τ) ⌊α⌋ (Tele.ofList ρ) :=
    instOne α (Tele.ofList ρ)
      (fun i => σ.act ((τ ⧺ Tele.ofList ρ) ∷ i.arity) (ι (.here i)))
  match e with
  | .ap (α := β) head args =>
    rcases Proper.cover (Γ :=(τ ∷ α) ⧺ Tele.ofList υ) (pre ⧺ dom) head with
      ⟨top, h_top⟩ | ⟨below, h_below⟩
    · subst h_top
      rcases Proper.cover (Γ :=Tele.ofList υ) (τ ∷ α) top with
        ⟨xυ, h_xυ⟩ | ⟨xt, h_xt⟩
      · subst h_xυ
        refine (congrArg (κ'.act (Tele.ofList υ))
          (Subst.act_ap_inr σ
            ((τ ∷ α) ⧺ Tele.ofList υ)
            ((Proper.inr (τ ∷ α)) xυ) args)).trans ?_
        rw [Proper.extendList_inr_inr (τ ∷ α) υ (pre ⧺ cod) xυ]
        refine (Subst.act_ap_inr κ' (Tele.ofList υ) xυ
          (fun j => σ.act (((τ ∷ α) ⧺ Tele.ofList υ) ∷ j.arity)
            (args j))).trans ?_
        have hκ :
            κ.act (Tele.ofList υ)
              (.ap
                ((Proper.inr ((pre ⧺ dom) ⧺ (τ ∷ α))) xυ)
                args)
            =
            .ap
              ((Proper.inr ((pre ⧺ dom ⧺ τ) ⧺ Tele.ofList ρ)) xυ)
              (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))
              := by
          exact Subst.act_ap_inr κ (Tele.ofList υ) xυ args
        have hκ_nested :
            κ.act (Tele.ofList υ)
              (.ap
                ((Proper.inr (pre ⧺ dom))
                  ((Proper.inr (τ ∷ α)) xυ))
                args)
            =
            .ap
              ((Proper.inr ((pre ⧺ dom ⧺ τ) ⧺ Tele.ofList ρ)) xυ)
              (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))
              := by
          rw [Proper.extendList_inr_inr (τ ∷ α) υ (pre ⧺ dom) xυ]
          exact hκ
        refine Eq.trans ?_ (congrArg
          (σ.act ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ))
          hκ_nested).symm
        change .ap
            ((Proper.inr ((pre ⧺ cod) ⧺ (τ ⧺ Tele.ofList ρ))) xυ)
            (fun j => κ'.act (Tele.ofList υ ∷ j.arity)
              (σ.act (((τ ∷ α) ⧺ Tele.ofList υ) ∷ j.arity) (args j)))
          =
          σ.act ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ)
            (.ap
              ((Proper.inr ((pre ⧺ dom) ⧺ (τ ⧺ Tele.ofList ρ))) xυ)
              (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j)))
        have hσ :
            σ.act ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ)
              (.ap
                ((Proper.inr ((pre ⧺ dom) ⧺ (τ ⧺ Tele.ofList ρ))) xυ)
                (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j)))
            =
            .ap
              ((Proper.inr ((pre ⧺ cod) ⧺ (τ ⧺ Tele.ofList ρ))) xυ)
              (fun j =>
                σ.act (((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ) ∷ j.arity)
                  (κ.act (Tele.ofList υ ∷ j.arity) (args j)))
                  := by
          rw [← Proper.extendList_inr_inr
            (τ ⧺ Tele.ofList ρ) υ (pre ⧺ dom) xυ]
          rw [Subst.act_ap_inr σ
            ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ)
            ((Proper.inr (τ ⧺ Tele.ofList ρ)) xυ)
            (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))]
          rw [Proper.extendList_inr_inr
            (τ ⧺ Tele.ofList ρ) υ (pre ⧺ cod) xυ]
        refine Eq.trans ?_ hσ.symm
        congr 1
        funext j
        exact underListAt σ ρ (j.arity :: υ) ι (args j)
      · subst h_xt
        rcases Proper.cover (Γ :=⌊α⌋) τ xt with
          ⟨xα, h_xα⟩ | ⟨xτ, h_xτ⟩
        · subst h_xα
          have hfillTop : ∀ (j : C.Binder β),
              κ'.act (Tele.ofList υ ∷ j.arity)
                  (σ.act ((((τ ∷ α) ⧺ Tele.ofList υ) ∷ j.arity))
                    (args j))
                =
              σ.act ((((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ) ∷ j.arity))
                  (κ.act (Tele.ofList υ ∷ j.arity) (args j))
                  := by
            intro j
            exact underListAt σ ρ (j.arity :: υ) ι (args j)
          refine (congrArg (κ'.act (Tele.ofList υ))
            (Subst.act_ap_inr σ
              ((τ ∷ α) ⧺ Tele.ofList υ)
              ((Proper.inl (τ ∷ α))
                ((Proper.inr τ) xα))
              args)).trans ?_
          have hheadCod :
              ((Proper.inr (pre ⧺ cod))
                (((Proper.inl (τ ∷ α)) :
                    (τ ∷ α) →ʳ (τ ∷ α) ⧺ Tele.ofList υ)
                  ((Proper.inr τ) xα)))
              =
              ((Proper.inl ((pre ⧺ cod) ⧺ (τ ∷ α)))
                ((Proper.inr (pre ⧺ cod))
                  ((Proper.inr τ) xα))) :=
            Proper.extendList_inr_inl
              (τ ∷ α) υ (pre ⧺ cod)
              ((Proper.inr τ) xα)
          refine (congrArg
            (fun head => κ'.act (Tele.ofList υ)
              (.ap head
                (fun j => σ.act (((τ ∷ α) ⧺ Tele.ofList υ) ∷ j.arity)
                  (args j))))
            hheadCod).trans ?_
          have hheadCod' :
              (((Proper.inl ((pre ⧺ cod) ⧺ (τ ∷ α))) :
                  ((pre ⧺ cod) ⧺ (τ ∷ α)) →ʳ
                    ((pre ⧺ cod) ⧺ (τ ∷ α)) ⧺ Tele.ofList υ)
                ((Proper.inr (pre ⧺ cod))
                  ((Proper.inr τ) xα)))
              =
              (((Proper.inl ((pre ⧺ cod ⧺ τ) ⧺ ⌊α⌋)) :
                  ((pre ⧺ cod ⧺ τ) ⧺ ⌊α⌋) →ʳ
                    ((pre ⧺ cod ⧺ τ) ⧺ ⌊α⌋) ⧺ Tele.ofList υ)
                ((Proper.inr (pre ⧺ cod ⧺ τ)) xα))
                := by
            change
              (((Proper.inl ((pre ⧺ cod) ⧺ (τ ∷ α))) :
                  ((pre ⧺ cod) ⧺ (τ ∷ α)) →ʳ
                    ((pre ⧺ cod) ⧺ (τ ∷ α)) ⧺ Tele.ofList υ)
                ((Proper.inr (pre ⧺ cod))
                  ((Proper.inr τ) xα)))
              =
              (((Proper.inl ((pre ⧺ cod ⧺ τ) ⧺ ⌊α⌋)) :
                  ((pre ⧺ cod ⧺ τ) ⧺ ⌊α⌋) →ʳ
                    ((pre ⧺ cod ⧺ τ) ⧺ ⌊α⌋) ⧺ Tele.ofList υ)
                ((Proper.inr (pre ⧺ cod ⧺ τ)) xα))
            cases xα with
            | here i => rfl
            | there z => nomatch z
          refine (congrArg
            (fun head => κ'.act (Tele.ofList υ)
              (.ap head
                (fun j => σ.act (((τ ∷ α) ⧺ Tele.ofList υ) ∷ j.arity)
                  (args j))))
            hheadCod').trans ?_
          refine (Subst.act_ap_inl_dom κ' (Tele.ofList υ)
            xα
            (fun j => σ.act (((τ ∷ α) ⧺ Tele.ofList υ) ∷ j.arity)
              (args j))).trans ?_
          have hκ'sub :
              κ'.sub xα = σ.act ((τ ⧺ Tele.ofList ρ) ∷ β) (ι xα)
              := by
            cases xα with
            | here i => rfl
            | there z => nomatch z
          rw [hκ'sub]
          have hheadDom :
              ((Proper.inr (pre ⧺ dom))
                (((Proper.inl (τ ∷ α)) :
                    (τ ∷ α) →ʳ (τ ∷ α) ⧺ Tele.ofList υ)
                  ((Proper.inr τ) xα)))
              =
              ((Proper.inl ((pre ⧺ dom) ⧺ (τ ∷ α)))
                ((Proper.inr (pre ⧺ dom))
                  ((Proper.inr τ) xα))) :=
            Proper.extendList_inr_inl
              (τ ∷ α) υ (pre ⧺ dom)
              ((Proper.inr τ) xα)
          have hheadDom' :
              (((Proper.inl ((pre ⧺ dom) ⧺ (τ ∷ α))) :
                  ((pre ⧺ dom) ⧺ (τ ∷ α)) →ʳ
                    ((pre ⧺ dom) ⧺ (τ ∷ α)) ⧺ Tele.ofList υ)
                ((Proper.inr (pre ⧺ dom))
                  ((Proper.inr τ) xα)))
              =
              (((Proper.inl ((pre ⧺ dom ⧺ τ) ⧺ ⌊α⌋)) :
                  ((pre ⧺ dom ⧺ τ) ⧺ ⌊α⌋) →ʳ
                    ((pre ⧺ dom ⧺ τ) ⧺ ⌊α⌋) ⧺ Tele.ofList υ)
                ((Proper.inr (pre ⧺ dom ⧺ τ)) xα))
                := by
            change
              (((Proper.inl ((pre ⧺ dom) ⧺ (τ ∷ α))) :
                  ((pre ⧺ dom) ⧺ (τ ∷ α)) →ʳ
                    ((pre ⧺ dom) ⧺ (τ ∷ α)) ⧺ Tele.ofList υ)
                ((Proper.inr (pre ⧺ dom))
                  ((Proper.inr τ) xα)))
              =
              (((Proper.inl ((pre ⧺ dom ⧺ τ) ⧺ ⌊α⌋)) :
                  ((pre ⧺ dom ⧺ τ) ⧺ ⌊α⌋) →ʳ
                    ((pre ⧺ dom ⧺ τ) ⧺ ⌊α⌋) ⧺ Tele.ofList υ)
                ((Proper.inr (pre ⧺ dom ⧺ τ)) xα))
            cases xα with
            | here i => rfl
            | there z => nomatch z
          have hκ :=
            (congrArg
              (fun head => κ.act (Tele.ofList υ) (.ap head args))
              hheadDom).trans
            ((congrArg
              (fun head => κ.act (Tele.ofList υ) (.ap head args))
              hheadDom').trans
            (Subst.act_ap_inl_dom κ (Tele.ofList υ) xα args))
          refine Eq.trans ?_
            (congrArg (σ.act ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ))
              hκ).symm
          have hκsub : κ.sub xα = ι xα
          := by
            cases xα with
            | here i => rfl
            | there z => nomatch z
          rw [hκsub]
          let ιβ : ∀ {δ : C.Arity}, ⌊β⌋ ∋ δ →
              Expr (pre ⧺ dom ⧺ (τ ⧺ Tele.ofList ρ) ⧺
                Tele.ofList υ ∷ δ) :=
            fun q => match q with
            | .here j => κ.act (Tele.ofList υ ∷ j.arity) (args j)
          simp only [hfillTop]
          simpa only [ιβ] using
            (underListAt
              (τ := τ ⧺ Tele.ofList ρ) σ υ [] (ι := ιβ)
              (e := ι xα))
        · subst h_xτ
          refine (congrArg (κ'.act (Tele.ofList υ))
            (Subst.act_ap_inr σ
              ((τ ∷ α) ⧺ Tele.ofList υ)
              ((Proper.inl (τ ∷ α))
                ((Proper.inl τ) xτ))
              args)).trans ?_
          change κ'.act (Tele.ofList υ)
              (.ap
                ((Proper.inr (pre ⧺ cod))
                  ((Proper.inl (τ ∷ α))
                    ((Proper.inl τ) xτ)))
                (fun j => σ.act (((τ ∷ α) ⧺ Tele.ofList υ) ∷ j.arity)
                  (args j)))
            =
            σ.act ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ)
              (κ.act (Tele.ofList υ)
                (.ap
                  ((Proper.inr (pre ⧺ dom))
                    ((Proper.inl (τ ∷ α))
                      ((Proper.inl τ) xτ)))
                  args))
          rw [Proper.extendList_inr_inl
            (τ ∷ α) υ (pre ⧺ cod) ((Proper.inl τ) xτ)]
          refine (Subst.act_ap_inl_pre κ' (Tele.ofList υ)
            ((Proper.inr (pre ⧺ cod)) xτ)
            (fun j => σ.act (((τ ∷ α) ⧺ Tele.ofList υ) ∷ j.arity)
              (args j))).trans ?_
          have hκ :
              κ.act (Tele.ofList υ)
                (.ap
                  ((Proper.inr (pre ⧺ dom))
                    ((Proper.inl (τ ∷ α))
                      ((Proper.inl τ) xτ)))
                  args)
              =
              .ap
                ((Proper.inl ((pre ⧺ dom ⧺ τ) ⧺ Tele.ofList ρ))
                  ((Proper.inl (pre ⧺ dom ⧺ τ))
                    ((Proper.inr (pre ⧺ dom)) xτ)))
                (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))
                := by
            rw [Proper.extendList_inr_inl
              (τ ∷ α) υ (pre ⧺ dom) ((Proper.inl τ) xτ)]
            exact Subst.act_ap_inl_pre κ (Tele.ofList υ)
              ((Proper.inr (pre ⧺ dom)) xτ) args
          refine Eq.trans ?_
            (congrArg (σ.act ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ)) hκ).symm
          unfold Subst.weakenCod
          rw [← Proper.extendList_inr_inl τ ρ (pre ⧺ dom) xτ]
          change .ap
              ((Proper.inl (pre ⧺ cod ⧺ τ ⧺ Tele.ofList ρ))
                ((Proper.inl (pre ⧺ cod ⧺ τ))
                  ((Proper.inr (pre ⧺ cod)) xτ)))
              (fun j => κ'.act (Tele.ofList υ ∷ j.arity)
                (σ.act (((τ ∷ α) ⧺ Tele.ofList υ) ∷ j.arity) (args j)))
            =
            σ.act ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ)
              (.ap
                ((Proper.inl ((pre ⧺ dom) ⧺ (τ ⧺ Tele.ofList ρ)))
                  ((Proper.inr (pre ⧺ dom))
                    ((Proper.inl τ) xτ)))
                (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j)))
          rw [← Proper.extendList_inr_inl
            (τ ⧺ Tele.ofList ρ) υ (pre ⧺ dom)
            ((Proper.inl τ) xτ)]
          refine Eq.trans ?_ (Subst.act_ap_inr σ
            ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ)
            ((Proper.inl (τ ⧺ Tele.ofList ρ))
              ((Proper.inl τ) xτ))
            (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))).symm
          rw [← Proper.extendList_inr_inl τ ρ (pre ⧺ cod) xτ]
          change Expr.ap
              ((Proper.inl (pre ⧺ cod ⧺ (τ ⧺ Tele.ofList ρ)))
                ((Proper.inr (pre ⧺ cod))
                  ((Proper.inl τ) xτ)))
              (fun j => κ'.act (Tele.ofList υ ∷ j.arity)
                (σ.act (((τ ∷ α) ⧺ Tele.ofList υ) ∷ j.arity) (args j)))
            =
            Expr.ap
              ((Proper.inr (pre ⧺ cod))
                ((Proper.inl (τ ⧺ Tele.ofList ρ))
                  ((Proper.inl τ) xτ)))
              (fun j =>
                σ.act (((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ) ∷ j.arity)
                  (κ.act (Tele.ofList υ ∷ j.arity) (args j)))
          rw [← Proper.extendList_inr_inl
            (τ ⧺ Tele.ofList ρ) υ (pre ⧺ cod)
            ((Proper.inl τ) xτ)]
          congr 1
          funext j
          exact underListAt σ ρ (j.arity :: υ) ι (args j)
    · subst h_below
      rcases Proper.cover pre below with ⟨z, h_z⟩ | ⟨z, h_z⟩
      · subst h_z
        refine (congrArg (κ'.act (Tele.ofList υ))
          (Subst.act_ap_inl_dom σ
            ((τ ∷ α) ⧺ Tele.ofList υ) z args)).trans ?_
        let η : (j : C.Binder β) →
            Expr (((pre ⧺ cod) ⧺ τ ∷ α) ⧺ Tele.ofList υ ∷ j.arity) :=
          fun j => σ.act (((τ ∷ α) ⧺ Tele.ofList υ) ∷ j.arity) (args j)
        let ιcod : ∀ {δ : C.Arity}, ⌊α⌋ ∋ δ →
            Expr ((pre ⧺ cod) ⧺ τ ⧺ Tele.ofList ρ ∷ δ) :=
          fun q => match q with
          | .here i => σ.act ((τ ⧺ Tele.ofList ρ) ∷ i.arity)
              (ι (.here i))
        refine (preNaturalityLiftAt
          (pre := pre ⧺ cod) (τ := τ) ρ υ []
          (ι := ιcod) (η := η) (e := σ z)).trans ?_
        have hfill : ∀ (j : C.Binder β),
            κ'.act (Tele.ofList υ ∷ j.arity)
                (σ.act (((τ ∷ α) ⧺ Tele.ofList υ) ∷ j.arity)
                  (args j))
              =
            σ.act (((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ) ∷ j.arity)
                (κ.act (Tele.ofList υ ∷ j.arity) (args j))
                := by
          intro j
          exact underListAt σ ρ (j.arity :: υ) ι (args j)
        simp only [η, ιcod]
        let ζ₀ : ∀ {δ : C.Arity}, ⌊β⌋ ∋ δ →
            Expr ((pre ⧺ cod) ⧺
              ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ) ∷ δ) :=
          fun q => match q with
          | .here j =>
              κ'.act (Tele.ofList υ ∷ j.arity)
                (σ.act (((τ ∷ α) ⧺ Tele.ofList υ) ∷ j.arity)
                  (args j))
        let ζ₁ : ∀ {δ : C.Arity}, ⌊β⌋ ∋ δ →
            Expr ((pre ⧺ cod) ⧺
              ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ) ∷ δ) :=
          fun q => match q with
          | .here j =>
              σ.act (((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ) ∷ j.arity)
                (κ.act (Tele.ofList υ ∷ j.arity) (args j))
        have hζ :
            (fun {δ : C.Arity} (q : ⌊β⌋ ∋ δ) => ζ₀ q)
              =
            (fun {δ : C.Arity} (q : ⌊β⌋ ∋ δ) => ζ₁ q)
            := by
          funext δ q
          cases q with
          | here j =>
              exact hfill j
          | there q => nomatch q
        change ⟦Subst.inst (C := C) (pre := pre ⧺ cod)
              (dom := ⌊β⌋)
              (cod := (τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ)
              ζ₀⟧ˢ (σ z)
            =
            σ.act ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ)
              (κ.act (Tele.ofList υ)
                (.ap
                  (((Proper.inl (pre ⧺ dom)) :
                      (pre ⧺ dom) →ʳ
                        (pre ⧺ dom) ⧺ ((τ ∷ α) ⧺ Tele.ofList υ))
                    ((Proper.inr pre) z))
                  args))
        rw [hζ]
        have hκ :
            κ.act (Tele.ofList υ)
              (.ap
                (((Proper.inl (pre ⧺ dom)) :
                    (pre ⧺ dom) →ʳ
                      (pre ⧺ dom) ⧺ ((τ ∷ α) ⧺ Tele.ofList υ))
                  ((Proper.inr pre) z))
                args)
            =
            .ap
              ((Proper.inl ((pre ⧺ dom ⧺ τ) ⧺ Tele.ofList ρ))
                ((Proper.inl (pre ⧺ dom ⧺ τ))
                  ((Proper.inl (pre ⧺ dom))
                    ((Proper.inr pre) z))))
              (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))
              := by
          rw [Proper.extendList_inl
            (τ ∷ α) υ (pre ⧺ dom) ((Proper.inr pre) z)]
          exact Subst.act_ap_inl_pre κ (Tele.ofList υ)
            ((Proper.inl (pre ⧺ dom))
              ((Proper.inr pre) z)) args
        refine Eq.trans ?_
          (congrArg (σ.act ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ)) hκ).symm
        rw [← Proper.extendList_inl τ ρ (pre ⧺ dom)
          ((Proper.inr pre) z)]
        change ⟦Subst.inst (C := C) (pre := pre ⧺ cod)
              (dom := ⌊β⌋)
              (cod := (τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ)
              (fun {δ} q => ζ₁ (δ := δ) q)⟧ˢ (σ z)
            =
            σ.act ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ)
              (.ap
                ((Proper.inl
                    (pre ⧺ dom ⧺ (τ ⧺ Tele.ofList ρ)))
                  (((Proper.inl (pre ⧺ dom)) :
                      (pre ⧺ dom) →ʳ
                        pre ⧺ dom ⧺ (τ ⧺ Tele.ofList ρ))
                    ((Proper.inr pre) z)))
                (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j)))
        rw [← Proper.extendList_inl
          (τ ⧺ Tele.ofList ρ) υ (pre ⧺ dom)
          ((Proper.inr pre) z)]
        exact (Subst.act_ap_inl_dom σ
          ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ) z
          (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))).symm
      · subst h_z
        refine (congrArg (κ'.act (Tele.ofList υ))
          (Subst.act_ap_inl_pre σ
            ((τ ∷ α) ⧺ Tele.ofList υ) z args)).trans ?_
        rw [Proper.extendList_inl
          (τ ∷ α) υ (pre ⧺ cod) ((Subst.weakenCod σ) z)]
        refine (Subst.act_ap_inl_pre κ' (Tele.ofList υ)
          ((Proper.inl (pre ⧺ cod))
            ((Subst.weakenCod σ) z))
          (fun j => σ.act (((τ ∷ α) ⧺ Tele.ofList υ) ∷ j.arity)
            (args j))).trans ?_
        have hκ :
            κ.act (Tele.ofList υ)
              (.ap
                (((Proper.inl (pre ⧺ dom)) :
                    (pre ⧺ dom) →ʳ
                      (pre ⧺ dom) ⧺ ((τ ∷ α) ⧺ Tele.ofList υ))
                  ((Proper.inl pre) z))
                args)
            =
            .ap
              ((Proper.inl ((pre ⧺ dom ⧺ τ) ⧺ Tele.ofList ρ))
                ((Proper.inl (pre ⧺ dom ⧺ τ))
                  ((Proper.inl (pre ⧺ dom))
                    ((Proper.inl pre) z))))
              (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))
              := by
          rw [Proper.extendList_inl
            (τ ∷ α) υ (pre ⧺ dom) ((Proper.inl pre) z)]
          exact Subst.act_ap_inl_pre κ (Tele.ofList υ)
            ((Proper.inl (pre ⧺ dom))
              ((Proper.inl pre) z)) args
        refine Eq.trans ?_
          (congrArg (σ.act ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ)) hκ).symm
        unfold Subst.weakenCod
        rw [← Proper.extendList_inl τ ρ (pre ⧺ cod)
          ((Proper.inl pre) z)]
        change (.ap
            ((Proper.inl
                (pre ⧺ cod ⧺ (τ ⧺ Tele.ofList ρ)))
              (((Proper.inl (pre ⧺ cod)) :
                  (pre ⧺ cod) →ʳ
                    pre ⧺ cod ⧺ (τ ⧺ Tele.ofList ρ))
                ((Proper.inl pre) z)))
            (fun i => κ'.act (Tele.ofList υ ∷ i.arity)
              (σ.act (((τ ∷ α) ⧺ Tele.ofList υ) ∷ i.arity)
                (args i)))
          =
          σ.act ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ)
            (.ap
              ((Proper.inl (pre ⧺ dom ⧺ τ ⧺ Tele.ofList ρ))
                ((Proper.inl (pre ⧺ dom ⧺ τ))
                  ((Proper.inl (pre ⧺ dom))
                    ((Proper.inl pre) z))))
              (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))))
        rw [← Proper.extendList_inl
          (τ ⧺ Tele.ofList ρ) υ (pre ⧺ cod)
          ((Proper.inl pre) z)]
        rw [← Proper.extendList_inl τ ρ (pre ⧺ dom)
          ((Proper.inl pre) z)]
        change .ap
            (((Proper.inl (pre ⧺ cod)) :
                (pre ⧺ cod) →ʳ
                  (pre ⧺ cod) ⧺
                    ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ))
              ((Proper.inl pre) z))
            (fun i => κ'.act (Tele.ofList υ ∷ i.arity)
              (σ.act (((τ ∷ α) ⧺ Tele.ofList υ) ∷ i.arity)
                (args i)))
          =
          σ.act ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ)
            (.ap
              ((Proper.inl
                  (pre ⧺ dom ⧺ (τ ⧺ Tele.ofList ρ)))
                (((Proper.inl (pre ⧺ dom)) :
                    (pre ⧺ dom) →ʳ
                      pre ⧺ dom ⧺ (τ ⧺ Tele.ofList ρ))
                  ((Proper.inl pre) z)))
              (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j)))
        rw [← Proper.extendList_inl
          (τ ⧺ Tele.ofList ρ) υ (pre ⧺ dom)
          ((Proper.inl pre) z)]
        refine Eq.trans ?_
          (Subst.act_ap_inl_pre σ
            ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ) z
            (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))).symm
        congr 1
        funext j
        exact underListAt σ ρ (j.arity :: υ) ι (args j)
termination_by
  ((⟨⟨dom.toList⟩, ⟨[α]⟩⟩ : InterchangeFuel C),
    (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ))
decreasing_by
  all_goals
    subst_vars
    first
      | refine Prod.Lex.left _ _ (InterchangeFuel.Lt.right ?_)
        exact DomLt.step α (List.Mem.head _) β (ListSlotAt.sub_single xα)
      | refine Prod.Lex.left _ _ (InterchangeFuel.Lt.left ?_)
        obtain ⟨βdom, hmem, hsub⟩ := SlotAt.subWitness z
        exact DomLt.step βdom hmem _ hsub
      | refine Prod.Lex.right _ ?_
        exact Expr.Subterm.of_arg_ofList_cons υ _ _ _

/-- The `PreLift.{sequential,fused}` reductions agree at every depth χ.
Mutually recursive with `underListAt`. -/
private theorem preNaturalityLiftAt
    {C : Carrier} {pre τ : Shape C} [Proper τ]
    {α β : C.Arity} (ρ υ χ : List C.Arity)
    (ι : ∀ {δ : C.Arity}, ⌊α⌋ ∋ δ → Expr (pre ⧺ τ ⧺ Tele.ofList ρ ∷ δ))
    (η : (j : C.Binder β) → Expr ((pre ⧺ τ ∷ α) ⧺ Tele.ofList υ ∷ j.arity))
    (e : Expr ((pre ∷ β) ⧺ Tele.ofList χ)) :
  PreLift.sequential ρ υ χ ι η e = PreLift.fused ρ υ χ ι η e
  := by
  let κ : Subst C (pre ⧺ τ) ⌊α⌋ (Tele.ofList ρ) :=
    instOne α (Tele.ofList ρ) (fun i => ι (.here i))
  let lam : Subst C pre ⌊β⌋ ((τ ∷ α) ⧺ Tele.ofList υ) :=
    instOne β ((τ ∷ α) ⧺ Tele.ofList υ) η
  let lam' : Subst C pre ⌊β⌋ ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ) :=
    instOne β ((τ ⧺ Tele.ofList ρ) ⧺ Tele.ofList υ)
      (fun j => κ.act (Tele.ofList υ ∷ j.arity) (η j))
  change κ.act ((Tele.ofList υ) ⧺ Tele.ofList χ)
      (lam.act (Tele.ofList χ) e)
    =
    lam'.act (Tele.ofList χ) e
  match e with
  | .ap (α := γ) head args =>
    have ih_args : ∀ (j : C.Binder γ),
        κ.act ((Tele.ofList υ) ⧺
              Tele.ofList (j.arity :: χ))
            (lam.act (Tele.ofList (j.arity :: χ)) (args j))
          =
          lam'.act (Tele.ofList (j.arity :: χ)) (args j)
          := by
      intro j
      exact preNaturalityLiftAt ρ υ (j.arity :: χ) ι η
        (args j)
    rcases Proper.cover (Γ :=Tele.ofList χ) (pre ∷ β) head with
      ⟨xχ, h_xχ⟩ | ⟨below, h_below⟩
    · subst h_xχ
      refine (congrArg
        (κ.act ((Tele.ofList υ) ⧺ Tele.ofList χ))
        (Subst.act_ap_inr lam (Tele.ofList χ) xχ args)).trans ?_
      change κ.act ((Tele.ofList υ) ⧺ Tele.ofList χ)
          (.ap
            ((Proper.inr ((pre ⧺ (τ ∷ α)) ⧺ Tele.ofList υ)) xχ)
            (fun j => lam.act (Tele.ofList χ ∷ j.arity) (args j)))
        =
        lam'.act (Tele.ofList χ)
          (.ap ((Proper.inr (pre ∷ β)) xχ) args)
      rw [← Proper.extendList_inr_inr
        (Tele.ofList υ) χ (pre ⧺ (τ ∷ α)) xχ]
      refine (Subst.act_ap_inr κ
        ((Tele.ofList υ) ⧺ Tele.ofList χ)
        ((Proper.inr (Tele.ofList υ)) xχ)
        (fun j => lam.act (Tele.ofList χ ∷ j.arity) (args j))).trans ?_
      change .ap
          ((Proper.inr (pre ⧺ (τ ⧺ Tele.ofList ρ)))
            ((Proper.inr (Tele.ofList υ)) xχ))
          (fun j =>
            κ.act (((Tele.ofList υ) ⧺ Tele.ofList χ) ∷ j.arity)
              (lam.act (Tele.ofList χ ∷ j.arity) (args j)))
        =
        lam'.act (Tele.ofList χ)
          (.ap ((Proper.inr (pre ∷ β)) xχ) args)
      rw [Proper.extendList_inr_inr
        (Tele.ofList υ) χ (pre ⧺ (τ ⧺ Tele.ofList ρ)) xχ]
      refine Eq.trans ?_
        (Subst.act_ap_inr lam' (Tele.ofList χ) xχ args).symm
      congr 1
      funext j
      exact ih_args j
    · subst h_below
      rcases Proper.cover pre below with ⟨xβ, h_xβ⟩ | ⟨z, h_z⟩
      · subst h_xβ
        cases xβ with
        | here j =>
            refine (congrArg
              (κ.act ((Tele.ofList υ) ⧺ Tele.ofList χ))
              (Subst.act_ap_inl_dom lam (Tele.ofList χ)
                (.here j) args)).trans ?_
            let θ : ∀ {δ : C.Arity}, (⌊j.arity⌋) ∋ δ →
                Expr ((pre ⧺ τ) ⧺ ⌊α⌋ ⧺
                  (Tele.ofList υ) ⧺ Tele.ofList χ ∷ δ) :=
              fun q => match q with
              | .here k => lam.act (Tele.ofList χ ∷ k.arity) (args k)
            let θ' : ∀ {δ : C.Arity}, (⌊j.arity⌋) ∋ δ →
                Expr ((pre ⧺ τ ⧺ Tele.ofList ρ) ⧺
                  (Tele.ofList υ) ⧺ Tele.ofList χ ∷ δ) :=
              fun q => match q with
              | .here k => lam'.act (Tele.ofList χ ∷ k.arity) (args k)
            have hfill : ∀ (k : C.Binder j.arity),
                κ.act (((Tele.ofList υ) ⧺ Tele.ofList χ) ∷ k.arity)
                    (θ (.here k))
                  =
                θ' (.here k)
                := by
              intro k
              exact ih_args k
            have hunder := underListAt
              (pre := pre ⧺ τ) (dom := ⌊α⌋)
              (cod := Tele.ofList ρ) (τ := (Tele.ofList υ))
              κ χ [] (ι := θ) (e := η j)
            unfold UnderList.actThenInst
              UnderList.instThenAct
              instOne at hunder
            dsimp only at hunder
            refine Eq.trans hunder.symm ?_
            simp only [hfill, θ, θ']
            exact (Subst.act_ap_inl_dom lam' (Tele.ofList χ)
              (.here j) args).symm
        | there z => nomatch z
      · subst h_z
        refine (congrArg
          (κ.act ((Tele.ofList υ) ⧺ Tele.ofList χ))
          (Subst.act_ap_inl_pre lam (Tele.ofList χ) z args)).trans ?_
        unfold Subst.weakenCod
        rw [Proper.extendList_inl (τ ∷ α) υ pre z]
        change κ.act ((Tele.ofList υ) ⧺ Tele.ofList χ)
            (.ap
              ((Proper.inl ((pre ⧺ (τ ∷ α)) ⧺ Tele.ofList υ))
                ((Proper.inl (pre ⧺ (τ ∷ α)))
                  ((Proper.inl pre) z)))
              (fun i => lam.act (Tele.ofList χ ∷ i.arity) (args i)))
          =
          lam'.act (Tele.ofList χ)
            (.ap
              ((Proper.inl (pre ∷ β)) ((Proper.inl pre) z))
              args)
        rw [← Proper.extendList_inl
          (Tele.ofList υ) χ (pre ⧺ (τ ∷ α))
          ((Proper.inl pre) z)]
        change κ.act ((Tele.ofList υ) ⧺ Tele.ofList χ)
            (.ap
              ((Proper.inl ((pre ⧺ τ) ⧺ ⌊α⌋))
                ((Proper.inl (pre ⧺ τ))
                  ((Proper.inl pre) z)))
              (fun i => lam.act (Tele.ofList χ ∷ i.arity) (args i)))
          =
          lam'.act (Tele.ofList χ)
            (.ap
              ((Proper.inl (pre ∷ β)) ((Proper.inl pre) z))
              args)
        rw [Subst.act_ap_inl_pre κ
          ((Tele.ofList υ) ⧺ Tele.ofList χ)
          ((Proper.inl pre) z)]
        refine Eq.trans ?_
          (Subst.act_ap_inl_pre lam' (Tele.ofList χ) z args).symm
        congr 1
        · unfold Subst.weakenCod
          rw [← Proper.extendList_inl τ ρ pre z]
          rw [Proper.extendList_inl
            (τ ⧺ Tele.ofList ρ) υ pre z]
          change
            ((Proper.inl (pre ⧺ (τ ⧺ Tele.ofList ρ))) :
                (pre ⧺ (τ ⧺ Tele.ofList ρ)) →ʳ
                  (pre ⧺ (τ ⧺ Tele.ofList ρ)) ⧺
                    ((Tele.ofList υ) ⧺ Tele.ofList χ))
              ((Proper.inl pre) z)
            =
            ((Proper.inl ((pre ⧺ (τ ⧺ Tele.ofList ρ)) ⧺
                Tele.ofList υ)) :
                ((pre ⧺ (τ ⧺ Tele.ofList ρ)) ⧺ Tele.ofList υ) →ʳ
                  ((pre ⧺ (τ ⧺ Tele.ofList ρ)) ⧺ Tele.ofList υ) ⧺
                    Tele.ofList χ)
              (((Proper.inl (pre ⧺ (τ ⧺ Tele.ofList ρ))) :
                  (pre ⧺ (τ ⧺ Tele.ofList ρ)) →ʳ
                    (pre ⧺ (τ ⧺ Tele.ofList ρ)) ⧺
                      Tele.ofList υ)
                ((Proper.inl pre) z))
          rw [← Proper.extendList_inl
            (Tele.ofList υ) χ
            (pre ⧺ (τ ⧺ Tele.ofList ρ))
            ((Proper.inl pre) z)]
        funext k
        exact ih_args k
termination_by
  ((⟨⟨[β]⟩, ⟨[α]⟩⟩ : InterchangeFuel C),
    (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ))
decreasing_by
  all_goals
    subst_vars
    first
      | refine Prod.Lex.left _ _ (InterchangeFuel.Lt.left_swap ?_)
        exact DomLt.step β (List.Mem.head _) j.arity ⟨j, rfl⟩
      | refine Prod.Lex.right _ ?_
        exact Expr.Subterm.of_arg_ofList_cons χ head args _

end

/-- `preNaturalityLiftAt` specialised to empty χ. -/
private theorem preNaturalityLift
    {C : Carrier} {pre τ : Shape C} [Proper τ]
    {α β : C.Arity} (ρ υ : List C.Arity)
    (ι : ∀ {δ : C.Arity}, ⌊α⌋ ∋ δ → Expr (pre ⧺ τ ⧺ Tele.ofList ρ ∷ δ))
    (η : (j : C.Binder β) → Expr ((pre ⧺ τ ∷ α) ⧺ Tele.ofList υ ∷ j.arity))
    (e : Expr (pre ∷ β)) :
  PreLift.sequential ρ υ [] ι η e = PreLift.fused ρ υ [] ι η e
  := by
  exact preNaturalityLiftAt
    (pre := pre) (τ := τ) (α := α) (β := β)
    ρ υ [] ι η e

/-- `underListAt` specialised to empty υ. -/
private theorem underList
    {C : Carrier} {pre dom cod τ : Shape C} [Proper dom] [Proper cod] [Proper τ]
    (σ : Subst C pre dom cod) {α} (ρ : List C.Arity)
    (ι : ∀ {β : C.Arity}, ⌊α⌋ ∋ β → Expr (pre ⧺ dom ⧺ τ ⧺ Tele.ofList ρ ∷ β))
    (e : Expr (pre ⧺ dom ⧺ τ ∷ α)) :
  UnderList.actThenInst σ ρ [] ι e = UnderList.instThenAct σ ρ [] ι e
  := by
  exact underListAt σ ρ [] ι e

/-- The `PreNaturality.{sequential,fused}` reductions agree at every depth υ. -/
private theorem preNaturalityAt
    {C : Carrier} {pre dom cod : Shape C} [Proper dom] [Proper cod]
    (σ : Subst C pre dom cod) {α} (ρ υ : List C.Arity)
    (ι : ∀ {β : C.Arity}, ⌊α⌋ ∋ β → Expr (pre ⧺ dom ⧺ Tele.ofList ρ ∷ β))
    (e : Expr ((pre ∷ α) ⧺ Tele.ofList υ)) :
  PreNaturality.sequential σ ρ υ ι e = PreNaturality.fused σ ρ υ ι e
  := by
  let κ : Subst C pre ⌊α⌋ (dom ⧺ Tele.ofList ρ) :=
    instOne α (dom ⧺ Tele.ofList ρ) (fun i => ι (.here i))
  let κ' : Subst C pre ⌊α⌋ (cod ⧺ Tele.ofList ρ) :=
    instOne α (cod ⧺ Tele.ofList ρ)
      (fun i => σ.act (Tele.ofList ρ ∷ i.arity) (ι (.here i)))
  change σ.act ((Tele.ofList ρ) ⧺ Tele.ofList υ)
      (κ.act (Tele.ofList υ) e)
    =
    κ'.act (Tele.ofList υ) e
  match e with
  | .ap (α := β) head args =>
    rcases Proper.cover (Γ :=⌊α⌋ ⧺ Tele.ofList υ) pre head with
      ⟨top, h_top⟩ | ⟨below, h_below⟩
    · subst h_top
      rcases Proper.cover (Γ :=Tele.ofList υ) ⌊α⌋ top with
        ⟨xυ, h_xυ⟩ | ⟨xα, h_xα⟩
      · subst h_xυ
        rw [Proper.extendList_inr_inr ⌊α⌋ υ pre xυ]
        refine (congrArg (σ.act ((Tele.ofList ρ) ⧺ Tele.ofList υ))
          (Subst.act_ap_inr κ (Tele.ofList υ) xυ args)).trans ?_
        refine Eq.trans ?_ (Subst.act_ap_inr κ' (Tele.ofList υ) xυ args).symm
        change σ.act ((Tele.ofList ρ) ⧺ Tele.ofList υ)
            (.ap
              ((Proper.inr ((pre ⧺ dom) ⧺ Tele.ofList ρ)) xυ)
              (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j)))
          =
          .ap
            ((Proper.inr ((pre ⧺ cod) ⧺ Tele.ofList ρ)) xυ)
            (fun j => κ'.act (Tele.ofList υ ∷ j.arity) (args j))
        rw [← Proper.extendList_inr_inr
          (Tele.ofList ρ) υ (pre ⧺ dom) xυ]
        rw [Subst.act_ap_inr σ
          ((Tele.ofList ρ) ⧺ Tele.ofList υ)
          ((Proper.inr (Tele.ofList ρ)) xυ)
          (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))]
        rw [Proper.extendList_inr_inr
          (Tele.ofList ρ) υ (pre ⧺ cod) xυ]
        congr 1
        funext j
        exact preNaturalityAt σ ρ (j.arity :: υ) ι (args j)
      · subst h_xα
        rw [Proper.extendList_inr_inl
          ⌊α⌋ υ pre xα]
        refine (congrArg
          (σ.act ((Tele.ofList ρ) ⧺ Tele.ofList υ))
          (Subst.act_ap_inl_dom κ (Tele.ofList υ)
            xα args)).trans ?_
        refine Eq.trans ?_
          (Subst.act_ap_inl_dom κ' (Tele.ofList υ)
            xα args).symm
        have hsub :
            κ'.sub xα = σ.act (Tele.ofList ρ ∷ β) (κ.sub xα)
            := by
          cases xα with
          | here i => rfl
          | there z => nomatch z
        rw [hsub]
        let ιβ : ∀ {δ : C.Arity}, ⌊β⌋ ∋ δ →
            Expr (pre ⧺ dom ⧺ Tele.ofList ρ ⧺ Tele.ofList υ ∷ δ) :=
          fun q => match q with
          | .here j => κ.act (Tele.ofList υ ∷ j.arity) (args j)
        have hfill : ∀ (j : C.Binder β),
            σ.act (((Tele.ofList ρ) ⧺ Tele.ofList υ) ∷ j.arity)
                (κ.act (Tele.ofList υ ∷ j.arity) (args j))
              =
            κ'.act (Tele.ofList υ ∷ j.arity) (args j)
            := by
          intro j
          exact preNaturalityAt σ ρ (j.arity :: υ) ι
            (args j)
        simp only [← hfill]
        exact (underList σ υ
          (τ := (Tele.ofList ρ))
          (ι := ιβ)
          (e := κ.sub xα)).symm
    · subst h_below
      rw [Proper.extendList_inl ⌊α⌋ υ pre below]
      refine (congrArg
        (σ.act ((Tele.ofList ρ) ⧺ Tele.ofList υ))
        (Subst.act_ap_inl_pre κ (Tele.ofList υ)
          below args)).trans ?_
      refine Eq.trans ?_
        (Subst.act_ap_inl_pre κ' (Tele.ofList υ)
          below args).symm
      unfold Subst.weakenCod
      rw [Proper.extendList_inl dom ρ pre below]
      change σ.act ((Tele.ofList ρ) ⧺ Tele.ofList υ)
          (.ap
            ((Proper.inl ((pre ⧺ dom) ⧺ Tele.ofList ρ))
              ((Proper.inl (pre ⧺ dom))
                ((Proper.inl pre) below)))
            (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j)))
        =
        .ap
          ((Proper.inl (pre ⧺ (cod ⧺ Tele.ofList ρ)))
            ((Proper.inl pre) below))
          (fun j => κ'.act (Tele.ofList υ ∷ j.arity) (args j))
      rw [← Proper.extendList_inl (Tele.ofList ρ) υ
        (pre ⧺ dom) ((Proper.inl pre) below)]
      refine (Subst.act_ap_inl_pre σ
        ((Tele.ofList ρ) ⧺ Tele.ofList υ)
        below
        (fun j => κ.act (Tele.ofList υ ∷ j.arity) (args j))).trans ?_
      unfold Subst.weakenCod
      rw [Proper.extendList_inl cod ρ pre below]
      have hHead :
          ((Proper.inl (pre ⧺ cod) :
              (pre ⧺ cod) →ʳ
                (pre ⧺ cod) ⧺ ((Tele.ofList ρ) ⧺ Tele.ofList υ))
            ((Proper.inl pre) below))
            =
          ((Proper.inl (pre ⧺ (cod ⧺ Tele.ofList ρ)) :
              (pre ⧺ (cod ⧺ Tele.ofList ρ)) →ʳ
                (pre ⧺ (cod ⧺ Tele.ofList ρ)) ⧺ Tele.ofList υ)
            ((Proper.inl (pre ⧺ cod) :
              (pre ⧺ cod) →ʳ (pre ⧺ cod) ⧺ Tele.ofList ρ)
              ((Proper.inl pre) below)))
              := by
        exact Proper.extendList_inl (Tele.ofList ρ) υ
          (pre ⧺ cod) ((Proper.inl pre) below)
      rw [← hHead]
      congr 1
      funext j
      exact preNaturalityAt σ ρ (j.arity :: υ) ι
        (args j)
termination_by (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by
  all_goals
    subst_vars
    try subst β
    subst_vars
    exact Expr.Subterm.of_arg_ofList_cons υ _ _ _

/-- `preNaturalityAt` specialised to empty υ. -/
private theorem preNaturality
    {C : Carrier} {pre dom cod : Shape C} [Proper dom] [Proper cod]
    (σ : Subst C pre dom cod) {α} (ρ : List C.Arity)
    (ι : ∀ {β : C.Arity}, ⌊α⌋ ∋ β → Expr (pre ⧺ dom ⧺ Tele.ofList ρ ∷ β))
    (e : Expr (pre ∷ α)) :
  PreNaturality.sequential σ ρ [] ι e = PreNaturality.fused σ ρ [] ι e
  := by
  exact preNaturalityAt σ ρ [] ι e

/-- The `Interchange.{actThenInst,instThenAct}` reductions agree at every depth ρ.
The main interchange equation under a generic τ-stack. -/
private theorem interchange
    {C : Carrier} {pre dom cod τ : Shape C} [Proper dom] [Proper cod] [Proper τ]
    (σ : Subst C pre dom cod) {α}
    (ι : ∀ {β : C.Arity}, ⌊α⌋ ∋ β → Expr (pre ⧺ dom ⧺ τ ∷ β))
    (ρ : List C.Arity) (e : Expr (pre ⧺ dom ⧺ ⌊α⌋ ⧺ Tele.ofList ρ)) :
  Interchange.actThenInst σ ι ρ e = Interchange.instThenAct σ ι ρ e
  := by
  unfold Interchange.actThenInst
    Interchange.instThenAct
    instOne
  dsimp only
  let κ : Subst C (pre ⧺ dom) ⌊α⌋ τ :=
    instOne α τ (fun i => ι (.here i))
  let κ' : Subst C (pre ⧺ cod) ⌊α⌋ τ :=
    instOne α τ (fun i => σ.act (τ ∷ i.arity) (ι (.here i)))
  change κ'.act (Tele.ofList ρ)
      (σ.act (⌊α⌋ ⧺ Tele.ofList ρ) e)
    =
    σ.act (τ ⧺ Tele.ofList ρ)
      (κ.act (Tele.ofList ρ) e)
  match e with
  | .ap (α := β) head args =>
    rcases Proper.cover (Γ :=⌊α⌋ ⧺ Tele.ofList ρ) (pre ⧺ dom) head with
      ⟨top, h_top⟩ | ⟨below, h_below⟩
    · subst h_top
      rcases Proper.cover (Γ :=Tele.ofList ρ) ⌊α⌋ top with
        ⟨xρ, h_xρ⟩ | ⟨xα, h_xα⟩
      · subst h_xρ
        refine (congrArg (κ'.act (Tele.ofList ρ))
          (Subst.act_ap_inr σ (⌊α⌋ ⧺ Tele.ofList ρ)
            ((Proper.inr ⌊α⌋) xρ) args)).trans ?_
        rw [Proper.extendList_inr_inr ⌊α⌋ ρ (pre ⧺ dom) xρ]
        rw [Proper.extendList_inr_inr ⌊α⌋ ρ (pre ⧺ cod) xρ]
        refine (Subst.act_ap_inr κ' (Tele.ofList ρ) xρ
          (fun j => σ.act ((⌊α⌋ ⧺ Tele.ofList ρ) ∷ j.arity) (args j))).trans ?_
        rw [Subst.act_ap_inr κ (Tele.ofList ρ) xρ args]
        rw [← Proper.extendList_inr_inr τ ρ (pre ⧺ dom) xρ]
        refine Eq.trans ?_ (Subst.act_ap_inr σ (τ ⧺ Tele.ofList ρ)
          ((Proper.inr τ) xρ)
          (fun j => κ.act (Tele.ofList ρ ∷ j.arity) (args j))).symm
        rw [Proper.extendList_inr_inr τ ρ (pre ⧺ cod) xρ]
        congr 1
        funext j
        exact interchange σ ι (j.arity :: ρ) (args j)
      · subst h_xα
        have hfillTop : ∀ (j : C.Binder β),
            κ'.act (Tele.ofList ρ ∷ j.arity)
                (σ.act ((⌊α⌋ ⧺ Tele.ofList ρ) ∷ j.arity)
                  (args j))
              =
            σ.act ((τ ⧺ Tele.ofList ρ) ∷ j.arity)
                (κ.act (Tele.ofList ρ ∷ j.arity) (args j))
                := by
          intro j
          exact interchange σ ι (j.arity :: ρ) (args j)
        cases xα with
        | here i =>
            refine (congrArg (κ'.act (Tele.ofList ρ))
              (Subst.act_ap_inr σ (⌊α⌋ ⧺ Tele.ofList ρ)
                ((Proper.inl ⌊α⌋) (.here i)) args)).trans ?_
            rw [Proper.extendList_inr_inl
              ⌊α⌋ ρ (pre ⧺ cod) (.here i)]
            refine (Subst.act_ap_inl_dom κ' (Tele.ofList ρ)
              (.here i)
              (fun j => σ.act ((⌊α⌋ ⧺ Tele.ofList ρ) ∷ j.arity)
                (args j))).trans ?_
            rw [Proper.extendList_inr_inl
              ⌊α⌋ ρ (pre ⧺ dom) (.here i)]
            rw [Subst.act_ap_inl_dom κ (Tele.ofList ρ)
              (.here i) args]
            rw [show κ'.sub (.here i)
                  = σ.act (τ ∷ i.arity) (ι (.here i)) from rfl]
            rw [show κ.sub (.here i)
                  = ι (.here i) from rfl]
            let ιβ : ∀ {δ : C.Arity}, (⌊i.arity⌋) ∋ δ →
                Expr (pre ⧺ dom ⧺ τ ⧺ Tele.ofList ρ ∷ δ) :=
              fun q => match q with
              | .here j => κ.act (Tele.ofList ρ ∷ j.arity) (args j)
            have hfill : ∀ (j : C.Binder i.arity),
                κ'.act (Tele.ofList ρ ∷ j.arity)
                    (σ.act ((⌊α⌋ ⧺ Tele.ofList ρ) ∷ j.arity)
                      (args j))
                  =
                σ.act ((τ ⧺ Tele.ofList ρ) ∷ j.arity)
                    (ιβ (.here j))
                    := by
              intro j
              exact hfillTop j
            simp only [hfill]
            exact underList σ ρ
              (ι := ιβ)
              (e := ι (.here i))
        | there z => nomatch z
    · subst h_below
      rcases Proper.cover pre below with ⟨z, h_z⟩ | ⟨z, h_z⟩
      · subst h_z
        refine (congrArg (κ'.act (Tele.ofList ρ))
          (Subst.act_ap_inl_dom σ
            (⌊α⌋ ⧺ Tele.ofList ρ) z args)).trans ?_
        let ιβ : ∀ {δ : C.Arity}, ⌊β⌋ ∋ δ →
            Expr (pre ⧺ cod ⧺ ⌊α⌋ ⧺ Tele.ofList ρ ∷ δ) :=
          fun q => match q with
          | .here j =>
              σ.act ((⌊α⌋ ⧺ Tele.ofList ρ) ∷ j.arity) (args j)
        have hpre := preNaturality κ' ρ
          (ι := ιβ) (e := σ z)
        unfold PreNaturality.sequential
          PreNaturality.fused
          instOne at hpre
        dsimp only at hpre
        refine hpre.trans ?_
        have hfill : ∀ (j : C.Binder β),
            κ'.act (Tele.ofList ρ ∷ j.arity)
                (ιβ (.here j))
              =
            σ.act ((τ ⧺ Tele.ofList ρ) ∷ j.arity)
                (κ.act (Tele.ofList ρ ∷ j.arity) (args j))
                := by
          intro j
          exact interchange σ ι (j.arity :: ρ) (args j)
        simp only [hfill]
        rw [Proper.extendList_inl
          ⌊α⌋ ρ (pre ⧺ dom) ((Proper.inr pre) z)]
        rw [Subst.act_ap_inl_pre κ (Tele.ofList ρ)
          ((Proper.inr pre) z) args]
        unfold Subst.weakenCod
        rw [← Proper.extendList_inl τ ρ (pre ⧺ dom)
          ((Proper.inr pre) z)]
        exact (Subst.act_ap_inl_dom σ (τ ⧺ Tele.ofList ρ) z
          (fun j => κ.act (Tele.ofList ρ ∷ j.arity) (args j))).symm
      · subst h_z
        refine (congrArg (κ'.act (Tele.ofList ρ))
          (Subst.act_ap_inl_pre σ
            (⌊α⌋ ⧺ Tele.ofList ρ) z args)).trans ?_
        rw [Proper.extendList_inl
          ⌊α⌋ ρ (pre ⧺ cod) ((Subst.weakenCod σ) z)]
        refine (Subst.act_ap_inl_pre κ' (Tele.ofList ρ)
          ((Subst.weakenCod σ) z)
          (fun j => σ.act ((⌊α⌋ ⧺ Tele.ofList ρ) ∷ j.arity)
            (args j))).trans ?_
        rw [Proper.extendList_inl
          ⌊α⌋ ρ (pre ⧺ dom) ((Proper.inl pre) z)]
        rw [Subst.act_ap_inl_pre κ (Tele.ofList ρ)
          ((Proper.inl pre) z) args]
        unfold Subst.weakenCod
        rw [← Proper.extendList_inl τ ρ (pre ⧺ dom)
          ((Proper.inl pre) z)]
        refine Eq.trans ?_ (Subst.act_ap_inl_pre σ (τ ⧺ Tele.ofList ρ) z
          (fun j => κ.act (Tele.ofList ρ ∷ j.arity) (args j))).symm
        unfold Subst.weakenCod
        rw [← Proper.extendList_inl τ ρ (pre ⧺ cod)
          ((Proper.inl pre) z)]
        congr 1
        funext j
        exact interchange σ ι (j.arity :: ρ) (args j)
termination_by (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by
  all_goals
    subst_vars
    exact Expr.Subterm.of_arg_ofList_cons ρ _ _ _

/-- `interchange` specialised to empty ρ.  The headline substitution-action
interchange equation. -/
private theorem fusion
    {C : Carrier} {Δ Ε τ : Shape C} [Proper Δ] [Proper Ε] [Proper τ]
    (g : ∀ {β : C.Arity}, Δ ∋ β → Expr (Ε ∷ β))
    {α} (ι : ∀ {β : C.Arity}, ⌊α⌋ ∋ β → Expr (Δ ⧺ τ ∷ β))
    (e : Expr (Δ ∷ α)) :
  Interchange.actThenInst (τ := τ) (toSubst g) ι [] e
    = Interchange.instThenAct (τ := τ) (toSubst g) ι [] e
  := by
  exact interchange (toSubst g) ι [] e


/-- **`act_kcomp`** — acting via a Kleisli composition factors.
Translates to `lift (g ∘ f) = lift g ∘ lift f` (comp_lift).  Generalised over
the depth `τ` so the recursive call on each arg fits the same statement. -/
theorem Subst.act_kcomp
    {C : Carrier} {Γ Δ Ξ : Shape C} [Proper Γ] [Proper Δ] [Proper Ξ]
    (f : ∀ {β}, Γ ∋ β → Expr (Δ ∷ β))
    (g : ∀ {β}, Δ ∋ β → Expr (Ξ ∷ β))
    (τ : Shape C) [Proper τ] (e : Expr (Γ ⧺ τ)) :
  (toSubst (Subst.kcomp f g)).act τ e = (toSubst g).act τ ((toSubst f).act τ e)
  := by
  match e with
  | .ap (α := β) head args =>
    rcases Proper.cover Γ head with
      ⟨x, h_x⟩ | ⟨y, h_y⟩
    · subst h_x
      refine (Subst.act_ap_inr (toSubst (Subst.kcomp f g)) τ x args).trans ?_
      change
        .ap ((Proper.inr (Shape.nil ⧺ Ξ)) x)
          (fun j => (toSubst (Subst.kcomp f g)).act (τ ∷ j.arity) (args j))
        =
        (toSubst g).act τ
          ((toSubst f).act τ
            (.ap ((Proper.inr (Shape.nil ⧺ Γ)) x) args))
      rw [Subst.act_ap_inr (toSubst f) τ x args]
      rw [Subst.act_ap_inr (toSubst g) τ x
        (fun i => (toSubst f).act (τ ∷ i.arity) (args i))]
      congr 1
      funext i
      exact Subst.act_kcomp f g (τ ∷ i.arity) (args i)
    · subst h_y
      rw [← Proper.inr_nil_id y]
      refine (Subst.act_ap_inl_dom
        (toSubst (Subst.kcomp f g)) τ y args).trans ?_
      have ih_args : ∀ (i : C.Binder β),
          (toSubst (Subst.kcomp f g)).act (τ ∷ i.arity) (args i)
            =
          (toSubst g).act (τ ∷ i.arity)
            ((toSubst f).act (τ ∷ i.arity) (args i)) :=
        fun i => Subst.act_kcomp f g (τ ∷ i.arity) (args i)
      rw [show (toSubst (Subst.kcomp f g)).sub y
            = (toSubst g).act ⌊β⌋ (f y) from rfl]
      simp only [ih_args]
      change
        ⟦Subst.inst ⌊β⌋
          (fun {δ} (q : ⌊β⌋ ∋ δ) => match q with
          | .here i =>
            (toSubst g).act (τ ∷ i.arity)
              ((toSubst f).act (τ ∷ i.arity) (args i)))⟧ˢ
          ((toSubst g).act ⌊β⌋ (f y))
        =
        (toSubst g).act τ
          ((toSubst f).act τ
            (.ap
              ((Proper.inl (Shape.nil ⧺ Γ))
                ((Proper.inr Shape.nil) y)) args))
      rw [Subst.act_ap_inl_dom (toSubst f) τ y args]
      exact fusion g
        (τ := τ)
        (ι := fun {δ} (q : ⌊β⌋ ∋ δ) => match q with
          | .here i => (toSubst f).act (τ ∷ i.arity) (args i))
        (e := f y)
termination_by (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg head args _
