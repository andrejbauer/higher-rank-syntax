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


/-! ## Monad law: comp_lift (TODO: port from old design) -/

/-- **`act_kcomp`** — Kleisli composition factors through `Subst.act`.
Translates to `lift (g ∘ʷ f) = lift g ∘ lift f` (comp_lift). -/
theorem Subst.act_kcomp
    {C : Carrier} {Γ Δ Ξ : Shape C} [Proper Γ] [Proper Δ] [Proper Ξ]
    (f : ∀ {β}, Γ ∋ β → Expr (Δ ∷ β))
    (g : ∀ {β}, Δ ∋ β → Expr (Ξ ∷ β))
    (τ : List C.Arity) (e : Expr (Γ ⧺ Tele.ofList τ)) :
  (toSubst (Subst.kcomp f g)).act Shape.nil τ e
    = (toSubst g).act Shape.nil τ ((toSubst f).act Shape.nil τ e)
  := by
  sorry  -- TODO: port from old design using new (outer, inner) dispatch
