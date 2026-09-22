import HigherRankSyntax.Typing.Telescope

/-!
# The judgements

Four relations over an ambient, well formed or not, defined by one simultaneous
induction: an expression is well formed, two expressions are equal, two
boundaries are equal, and a substitution fills a telescope.  Filling a telescope
runs over its slots in order: the first slot's filler is checked against the
boundary that slot declares, over the ambient extended by the entries it binds,
and is then substituted into the declarations that follow.
-/



mutual

/-- An expression over an ambient is well formed. -/
inductive Wf_e : {Δ : C.Arity} → Ambient Δ → Expr Δ → Prop where
  | ap {Δ : C.Arity} {Ξ : Ambient Δ} {α : C.Arity} (x : Δ ∋ α) (args : Subst α Δ)
      (head : ¬ (Ξ.declaration x).isEq)
      (fill : Wf_s Ξ (Ξ.binding x) args) :
      Wf_e Ξ (.ap x args)

/-- Two expressions over an ambient are equal. -/
inductive Eq_e : {Δ : C.Arity} → Ambient Δ → Expr Δ → Expr Δ → Prop where
  | refl {Δ : C.Arity} {Ξ : Ambient Δ} {e : Expr Δ} (h : Wf_e Ξ e) : Eq_e Ξ e e
  | symm {Δ : C.Arity} {Ξ : Ambient Δ} {e e' : Expr Δ} (h : Eq_e Ξ e e') : Eq_e Ξ e' e
  | trans {Δ : C.Arity} {Ξ : Ambient Δ} {e e' e'' : Expr Δ}
      (h : Eq_e Ξ e e') (h' : Eq_e Ξ e' e'') : Eq_e Ξ e e''
  | hyp {Δ : C.Arity} {Ξ : Ambient Δ} {Λ : C.Arity} (q : Δ ∋ Λ) (l r : Expr (Δ ⋈ Λ))
      (args : Subst Λ Δ)
      (decl : Ξ.declaration q = .eq l r)
      (hl : Wf_e (Ξ ⋈ Ξ.binding q) l)
      (hr : Wf_e (Ξ ⋈ Ξ.binding q) r)
      (fill : Wf_s Ξ (Ξ.binding q) args) :
      Eq_e Ξ (args ⋆ l) (args ⋆ r)
  | congr {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω} {e e' : Expr (Δ ⋈ Ω)}
      (σ θ : Subst Ω Δ) (hΘ : Wf_t Ξ Θ) (hσ : Wf_s Ξ Θ σ) (hθ : Wf_s Ξ Θ θ)
      (agree : Eq_s Ξ Θ σ θ) (h : Eq_e (Ξ ⋈ Θ) e e') :
      Eq_e Ξ (σ ⋆ e) (θ ⋆ e')

/-- Two boundaries over an ambient are equal. -/
inductive Eq_bd : {Δ : C.Arity} → Ambient Δ → Bd Δ → Bd Δ → Prop where
  | sort {Δ : C.Arity} {Ξ : Ambient Δ} : Eq_bd Ξ .sort .sort
  | of {Δ : C.Arity} {Ξ : Ambient Δ} {S S' : Expr Δ} (h : Eq_e Ξ S S') :
      Eq_bd Ξ (.of S) (.of S')
  | eq {Δ : C.Arity} {Ξ : Ambient Δ} {l r l' r' : Expr Δ}
      (hl : Eq_e Ξ l l') (hr : Eq_e Ξ r r') : Eq_bd Ξ (.eq l r) (.eq l' r')

/-- A substitution fills a telescope over an ambient. -/
inductive Wf_s : {Δ Ω : C.Arity} → Ambient Δ → dTel Δ Ω → Subst Ω Δ → Prop where
  | nil {Δ : C.Arity} {Ξ : Ambient Δ} {σ : Subst 1 Δ} : Wf_s Ξ .nil σ
  | cons {Δ α Ω : C.Arity} {Ξ : Ambient Δ} {bind : dTel Δ α} {boundary : Bd (Δ ⋈ α)}
      {rest : dTel (Δ ⋈ C.single α) Ω} {σ : Subst (C.single α ⋈ Ω) Δ}
      (equation : ∀ l r : Expr (Δ ⋈ α), boundary = .eq l r → Eq_e (Ξ ⋈ bind) l r)
      (filler : ¬ boundary.isEq → Wf_e (Ξ ⋈ bind) (σ (C.inl (C.singleSlot α))))
      (declared : ¬ boundary.isEq →
          Eq_bd (Ξ ⋈ bind) ((Ξ ⋈ bind).boundaryOf (σ (C.inl (C.singleSlot α))))
            boundary)
      (hrest : Wf_s Ξ
          (dTel.instantiate (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) rest)
          (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j))) :
      Wf_s Ξ (dTel.cons bind boundary rest) σ

/-- Two fillings of a telescope agree at every non-equational slot. -/
inductive Eq_s : {Δ Ω : C.Arity} → Ambient Δ → dTel Δ Ω → Subst Ω Δ → Subst Ω Δ → Prop
  where
  | nil {Δ : C.Arity} {Ξ : Ambient Δ} {σ θ : Subst 1 Δ} : Eq_s Ξ .nil σ θ
  | cons {Δ α Ω : C.Arity} {Ξ : Ambient Δ} {bind : dTel Δ α} {boundary : Bd (Δ ⋈ α)}
      {rest : dTel (Δ ⋈ C.single α) Ω} {σ θ : Subst (C.single α ⋈ Ω) Δ}
      (slot : ¬ boundary.isEq →
          Eq_e (Ξ ⋈ bind) (σ (C.inl (C.singleSlot α))) (θ (C.inl (C.singleSlot α))))
      (hrest : Eq_s Ξ
          (dTel.instantiate (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) rest)
          (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j))
          (fun ⦃β⦄ (j : Ω ∋ β) => θ (C.inr j))) :
      Eq_s Ξ (dTel.cons bind boundary rest) σ θ

/-- A declaration is well formed over the ambient extended by the entries its
slot binds. -/
inductive Wf_bd : {Δ Λ : C.Arity} → Ambient Δ → dTel Δ Λ → Bd (Δ ⋈ Λ) → Prop where
  | sort {Δ Λ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Λ} : Wf_bd Ξ Θ .sort
  | of {Δ Λ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Λ} {S : Expr (Δ ⋈ Λ)}
      (hS : Wf_e (Ξ ⋈ Θ) S)
      (hsort : Eq_bd (Ξ ⋈ Θ) ((Ξ ⋈ Θ).boundaryOf S) .sort) :
      Wf_bd Ξ Θ (.of S)
  | eq {Δ Λ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Λ} {l r : Expr (Δ ⋈ Λ)}
      (hl : Wf_e (Ξ ⋈ Θ) l) (hr : Wf_e (Ξ ⋈ Θ) r)
      (heq : Eq_bd (Ξ ⋈ Θ) ((Ξ ⋈ Θ).boundaryOf l) ((Ξ ⋈ Θ).boundaryOf r)) :
      Wf_bd Ξ Θ (.eq l r)

/-- A telescope over an ambient is well formed. -/
inductive Wf_t : {Δ Ω : C.Arity} → Ambient Δ → dTel Δ Ω → Prop where
  | nil {Δ : C.Arity} {Ξ : Ambient Δ} : Wf_t Ξ .nil
  | cons {Δ α Ω : C.Arity} {Ξ : Ambient Δ} {bind : dTel Δ α} {boundary : Bd (Δ ⋈ α)}
      {rest : dTel (Δ ⋈ C.single α) Ω}
      (hbind : Wf_t Ξ bind) (hboundary : Wf_bd Ξ bind boundary)
      (hrest : Wf_t (Ξ ⋈ dTel.cons bind boundary .nil) rest) :
      Wf_t Ξ (dTel.cons bind boundary rest)

end

/-! ### Notation

One turnstile, overloaded on what stands to the right of it: an expression, a
substitution, or a telescope.  The arguments parse above `≈` so that
`Ξ ⊢ e ≈ e'` is not read as `Ξ ⊢ (e ≈ e')`. -/

@[inherit_doc Wf_e] notation:50 Ξ " ⊢ " e:51 => Wf_e Ξ e
@[inherit_doc Eq_e] notation:50 Ξ " ⊢ " e:51 " ≈ " e':51 => Eq_e Ξ e e'
@[inherit_doc Eq_bd] notation:50 Ξ " ⊢ " β:51 " ≈ " β':51 => Eq_bd Ξ β β'
@[inherit_doc Wf_s] notation:50 Ξ " ⊢ " σ:51 " : " Θ:51 => Wf_s Ξ Θ σ
@[inherit_doc Eq_s] notation:50 Ξ " ⊢ " σ:51 " ≈ " θ:51 " : " Θ:51 => Eq_s Ξ Θ σ θ

/-! ### Fillings

The slotwise reading of `Wf_s`: at every slot the filler is well formed and has
the declared boundary, both read through the whole substitution. -/

/-- The two sides of a filled equational declaration are equal. -/
theorem Wf_s.equation {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {Ω : C.Arity} {Θ : dTel Δ Ω} {σ : Subst Ω Δ}, Wf_s Ξ Θ σ →
      ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ) (l r : Expr (Δ ⋈ Λ)),
        σ ⋆ Θ.declaration z = .eq l r → Eq_e (Ξ ⋈ σ ⋆ Θ.binding z) l r
  | _, _, _, .nil, _, z => (C.unit_is_empty z).elim
  | _, _, _, .cons (α := α) (Ω := Ω) (σ := σ) (bind := bind)
      (boundary := boundary) (rest := rest) equation _ _ hrest, Λ, z => by
      refine slotCases (α := α) (Δ := Ω)
        (motive := fun ⦃Λ⦄ z => ∀ (l r : Expr (Δ ⋈ Λ)),
          σ ⋆ (dTel.cons bind boundary rest).declaration z = .eq l r →
          Eq_e (Ξ ⋈ σ ⋆ (dTel.cons bind boundary rest).binding z) l r) ?head ?tail z
      case head =>
        intro l r h
        refine Eq.mp (congrArg (fun T => Eq_e (Ξ ⋈ T) l r)
          (dTel.binding_head_instantiate bind boundary rest σ).symm) ?_
        exact equation l r
          ((dTel.declaration_head_instantiate bind boundary rest σ).symm.trans h)
      case tail =>
        intro γ y l r h
        refine Eq.mp (congrArg (fun T => Eq_e (Ξ ⋈ T) l r)
          (dTel.binding_tail_instantiate bind boundary rest σ y).symm) ?_
        exact Wf_s.equation hrest y l r
          ((dTel.declaration_tail_instantiate bind boundary rest σ y).symm.trans h)

/-- The filler at a non-equational slot is well formed. -/
theorem Wf_s.filler {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {Ω : C.Arity} {Θ : dTel Δ Ω} {σ : Subst Ω Δ}, Wf_s Ξ Θ σ →
      ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ), ¬ (σ ⋆ Θ.declaration z).isEq →
        Wf_e (Ξ ⋈ σ ⋆ Θ.binding z) (σ z)
  | _, _, _, .nil, _, z => (C.unit_is_empty z).elim
  | _, _, _, .cons (α := α) (Ω := Ω) (σ := σ) (bind := bind)
      (boundary := boundary) (rest := rest) _ filler _ hrest, Λ, z => by
      refine slotCases (α := α) (Δ := Ω)
        (motive := fun ⦃Λ⦄ z =>
          ¬ (σ ⋆ (dTel.cons bind boundary rest).declaration z).isEq →
          Wf_e (Ξ ⋈ σ ⋆ (dTel.cons bind boundary rest).binding z) (σ z)) ?head ?tail z
      case head =>
        intro hne
        refine Eq.mp (congrArg (fun T => Wf_e (Ξ ⋈ T)
          (σ (C.inl (C.singleSlot α))))
          (dTel.binding_head_instantiate bind boundary rest σ).symm) ?_
        exact filler (fun hEq => hne (Eq.mp (congrArg Bd.isEq
          (dTel.declaration_head_instantiate bind boundary rest σ).symm) hEq))
      case tail =>
        intro γ y hne
        refine Eq.mp (congrArg (fun T => Wf_e (Ξ ⋈ T) (σ (C.inr y)))
          (dTel.binding_tail_instantiate bind boundary rest σ y).symm) ?_
        exact Wf_s.filler hrest y (fun hEq => hne (Eq.mp (congrArg Bd.isEq
          (dTel.declaration_tail_instantiate bind boundary rest σ y).symm) hEq))

/-- The computed boundary of the filler at a non-equational slot is the filled
declaration. -/
theorem Wf_s.declared {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {Ω : C.Arity} {Θ : dTel Δ Ω} {σ : Subst Ω Δ}, Wf_s Ξ Θ σ →
      ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ), ¬ (σ ⋆ Θ.declaration z).isEq →
        Eq_bd (Ξ ⋈ σ ⋆ Θ.binding z) ((Ξ ⋈ σ ⋆ Θ.binding z).boundaryOf (σ z))
          (σ ⋆ Θ.declaration z)
  | _, _, _, .nil, _, z => (C.unit_is_empty z).elim
  | _, _, _, .cons (α := α) (Ω := Ω) (σ := σ) (bind := bind)
      (boundary := boundary) (rest := rest) _ _ declared hrest, Λ, z => by
      refine slotCases (α := α) (Δ := Ω)
        (motive := fun ⦃Λ⦄ z =>
          ¬ (σ ⋆ (dTel.cons bind boundary rest).declaration z).isEq →
          Eq_bd (Ξ ⋈ σ ⋆ (dTel.cons bind boundary rest).binding z)
            ((Ξ ⋈ σ ⋆ (dTel.cons bind boundary rest).binding z).boundaryOf (σ z))
            (σ ⋆ (dTel.cons bind boundary rest).declaration z)) ?head ?tail z
      case head =>
        intro hne
        refine Eq.mp (congrArg₂ (fun (T : dTel Δ α) (b : Bd (Δ ⋈ α)) =>
          Eq_bd (Ξ ⋈ T) ((Ξ ⋈ T).boundaryOf (σ (C.inl (C.singleSlot α)))) b)
          (dTel.binding_head_instantiate bind boundary rest σ).symm
          (dTel.declaration_head_instantiate bind boundary rest σ).symm) ?_
        exact declared (fun hEq => hne (Eq.mp (congrArg Bd.isEq
          (dTel.declaration_head_instantiate bind boundary rest σ).symm) hEq))
      case tail =>
        intro γ y hne
        refine Eq.mp (congrArg₂ (fun (T : dTel Δ γ) (b : Bd (Δ ⋈ γ)) =>
          Eq_bd (Ξ ⋈ T) ((Ξ ⋈ T).boundaryOf (σ (C.inr y))) b)
          (dTel.binding_tail_instantiate bind boundary rest σ y).symm
          (dTel.declaration_tail_instantiate bind boundary rest σ y).symm) ?_
        exact Wf_s.declared hrest y (fun hEq => hne (Eq.mp (congrArg Bd.isEq
          (dTel.declaration_tail_instantiate bind boundary rest σ y).symm) hEq))

/-- A filling of a telescope whose base is substituted, from the conditions at
every slot. -/
theorem Wf_s.slotwise_actBase {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {Γ Ω : C.Arity} (Θ : dTel Γ Ω) (κ : Subst Γ Δ) {σ : Subst Ω Δ},
      (∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ) (l r : Expr (Δ ⋈ Λ)),
          σ ⋆ (dTel.actBase κ Θ).declaration z = .eq l r →
          Eq_e (Ξ ⋈ σ ⋆ (dTel.actBase κ Θ).binding z) l r) →
      (∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
          ¬ (σ ⋆ (dTel.actBase κ Θ).declaration z).isEq →
          Wf_e (Ξ ⋈ σ ⋆ (dTel.actBase κ Θ).binding z) (σ z)) →
      (∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
          ¬ (σ ⋆ (dTel.actBase κ Θ).declaration z).isEq →
          Eq_bd (Ξ ⋈ σ ⋆ (dTel.actBase κ Θ).binding z)
            ((Ξ ⋈ σ ⋆ (dTel.actBase κ Θ).binding z).boundaryOf (σ z))
            (σ ⋆ (dTel.actBase κ Θ).declaration z)) →
      Wf_s Ξ (dTel.actBase κ Θ) σ
  | _, _, .nil, _, _, _, _, _ => .nil
  | _, _, .cons (α := α) (Δ := Ω) bind boundary rest, κ, σ,
      equation, filler, declared => by
      have hd := dTel.declaration_head_instantiate (dTel.actBase κ bind)
        (Bd.act (Γ := 1) κ α boundary)
        (dTel.actBase (Subst.lift κ (C.single α)) rest) σ
      have hb := dTel.binding_head_instantiate (dTel.actBase κ bind)
        (Bd.act (Γ := 1) κ α boundary)
        (dTel.actBase (Subst.lift κ (C.single α)) rest) σ
      have hcat := dTel.actBase_comp (Subst.lift κ (C.single α))
        (Subst.copair (Subst.id Δ)
          (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i))) rest
      refine .cons ?equation ?filler ?declared ?hrest
      case equation =>
        intro l r h
        refine Eq.mp (congrArg (fun T => Eq_e (Ξ ⋈ T) l r) hb) ?_
        exact equation (C.inl (C.singleSlot α)) l r (hd.trans h)
      case filler =>
        intro hne
        refine Eq.mp (congrArg (fun T =>
          Wf_e (Ξ ⋈ T) (σ (C.inl (C.singleSlot α)))) hb) ?_
        exact filler (C.inl (C.singleSlot α))
          (fun hEq => hne (Eq.mp (congrArg Bd.isEq hd) hEq))
      case declared =>
        intro hne
        refine Eq.mp (congrArg₂ (fun (T : dTel Δ α) (b : Bd (Δ ⋈ α)) =>
          Eq_bd (Ξ ⋈ T) ((Ξ ⋈ T).boundaryOf (σ (C.inl (C.singleSlot α)))) b)
          hb hd) ?_
        exact declared (C.inl (C.singleSlot α))
          (fun hEq => hne (Eq.mp (congrArg Bd.isEq hd) hEq))
      case hrest =>
        have hdt : ∀ ⦃γ : C.Arity⦄ (y : Ω ∋ γ),
            (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j)) ⋆
                (dTel.actBase (Subst.comp (Γ := 1) (Subst.lift κ (C.single α))
                  (Subst.copair (Subst.id Δ)
                    (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)))) rest).declaration y
              = σ ⋆ (dTel.actBase κ (dTel.cons bind boundary rest)).declaration
                  (C.inr y) := by
          intro γ y
          refine Eq.trans (congrArg (fun T =>
            (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j)) ⋆ dTel.declaration T y) hcat) ?_
          exact (dTel.declaration_tail_instantiate _ _ _ σ y).symm
        have hbt : ∀ ⦃γ : C.Arity⦄ (y : Ω ∋ γ),
            (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j)) ⋆
                (dTel.actBase (Subst.comp (Γ := 1) (Subst.lift κ (C.single α))
                  (Subst.copair (Subst.id Δ)
                    (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)))) rest).binding y
              = σ ⋆ (dTel.actBase κ (dTel.cons bind boundary rest)).binding
                  (C.inr y) := by
          intro γ y
          refine Eq.trans (congrArg (fun (T : dTel Δ Ω) =>
            dTel.instantiate (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j))
              (dTel.binding T y)) hcat) ?_
          exact (dTel.binding_tail_instantiate _ _ _ σ y).symm
        refine Eq.mp (congrArg (fun T =>
          Wf_s Ξ T (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j))) hcat) ?_
        refine Wf_s.slotwise_actBase rest _ ?e ?f ?d
        case e =>
          intro γ y l r h
          refine Eq.mp (congrArg (fun T => Eq_e (Ξ ⋈ T) l r) (hbt y).symm) ?_
          exact equation (C.inr y) l r ((hdt y).symm.trans h)
        case f =>
          intro γ y hne
          refine Eq.mp (congrArg (fun T => Wf_e (Ξ ⋈ T) (σ (C.inr y)))
            (hbt y).symm) ?_
          exact filler (C.inr y) (fun hEq => hne (Eq.mp (congrArg Bd.isEq
            (hdt y).symm) hEq))
        case d =>
          intro γ y hne
          refine Eq.mp (congrArg₂ (fun (T : dTel Δ γ) (b : Bd (Δ ⋈ γ)) =>
            Eq_bd (Ξ ⋈ T) ((Ξ ⋈ T).boundaryOf (σ (C.inr y))) b)
            (hbt y).symm (hdt y).symm) ?_
          exact declared (C.inr y) (fun hEq => hne (Eq.mp (congrArg Bd.isEq
            (hdt y).symm) hEq))

/-- A filling, from the conditions at every slot. -/
theorem Wf_s.slotwise {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω}
    {σ : Subst Ω Δ}
    (equation : ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ) (l r : Expr (Δ ⋈ Λ)),
        σ ⋆ Θ.declaration z = .eq l r → Eq_e (Ξ ⋈ σ ⋆ Θ.binding z) l r)
    (filler : ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ), ¬ (σ ⋆ Θ.declaration z).isEq →
        Wf_e (Ξ ⋈ σ ⋆ Θ.binding z) (σ z))
    (declared : ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ), ¬ (σ ⋆ Θ.declaration z).isEq →
        Eq_bd (Ξ ⋈ σ ⋆ Θ.binding z) ((Ξ ⋈ σ ⋆ Θ.binding z).boundaryOf (σ z))
          (σ ⋆ Θ.declaration z)) :
    Wf_s Ξ Θ σ := by
  have hid := dTel.actBase_id Θ
  refine Eq.mp (congrArg (fun T => Wf_s Ξ T σ) hid) ?_
  refine Wf_s.slotwise_actBase Θ (Subst.id Δ) ?e ?f ?d
  case e =>
    intro Λ z l r h
    refine Eq.mp (congrArg (fun T => Eq_e (Ξ ⋈ σ ⋆ dTel.binding T z) l r)
      hid.symm) ?_
    exact equation z l r (Eq.mp (congrArg (fun T =>
      σ ⋆ dTel.declaration T z = Bd.eq l r) hid) h)
  case f =>
    intro Λ z hne
    refine Eq.mp (congrArg (fun T => Wf_e (Ξ ⋈ σ ⋆ dTel.binding T z) (σ z))
      hid.symm) ?_
    exact filler z (fun hEq => hne (Eq.mp (congrArg (fun T =>
      (σ ⋆ dTel.declaration T z).isEq) hid.symm) hEq))
  case d =>
    intro Λ z hne
    refine Eq.mp (congrArg (fun T => Eq_bd (Ξ ⋈ σ ⋆ dTel.binding T z)
      ((Ξ ⋈ σ ⋆ dTel.binding T z).boundaryOf (σ z))
      (σ ⋆ dTel.declaration T z)) hid.symm) ?_
    exact declared z (fun hEq => hne (Eq.mp (congrArg (fun T =>
      (σ ⋆ dTel.declaration T z).isEq) hid.symm) hEq))

/-! ### Equality of boundaries -/

/-- Equality of boundaries is symmetric. -/
theorem Eq_bd.symm {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {β β' : Bd Δ}, Eq_bd Ξ β β' → Eq_bd Ξ β' β
  | _, _, .sort => .sort
  | _, _, .of h => .of h.symm
  | _, _, .eq hl hr => .eq hl.symm hr.symm

/-- Equality of boundaries is transitive. -/
theorem Eq_bd.trans {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {β β' β'' : Bd Δ}, Eq_bd Ξ β β' → Eq_bd Ξ β' β'' → Eq_bd Ξ β β''
  | _, _, _, .sort, .sort => .sort
  | _, _, _, .of h, .of h' => .of (h.trans h')
  | _, _, _, .eq hl hr, .eq hl' hr' => .eq (hl.trans hl') (hr.trans hr')

/-- A boundary equal to an equation is an equation with equal sides. -/
theorem Eq_bd.eq_inv {Δ : C.Arity} {Ξ : Ambient Δ} {l r : Expr Δ} {β : Bd Δ} :
    Eq_bd Ξ (.eq l r) β → ∃ l' r', β = .eq l' r' ∧ Eq_e Ξ l l' ∧ Eq_e Ξ r r'
  | .eq hl hr => ⟨_, _, rfl, hl, hr⟩

/-- The agreement of two fillings, at one slot. -/
theorem Eq_s.slot {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {Ω : C.Arity} {Θ : dTel Δ Ω} {σ θ : Subst Ω Δ}, Eq_s Ξ Θ σ θ →
      ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ), ¬ (σ ⋆ Θ.declaration z).isEq →
        Eq_e (Ξ ⋈ σ ⋆ Θ.binding z) (σ z) (θ z)
  | _, _, _, _, .nil, _, z => (C.unit_is_empty z).elim
  | _, _, _, _, .cons (α := α) (Ω := Ω) (σ := σ) (θ := θ) (bind := bind)
      (boundary := boundary) (rest := rest) slot hrest, Λ, z => by
      refine slotCases (α := α) (Δ := Ω)
        (motive := fun ⦃Λ⦄ z =>
          ¬ (σ ⋆ (dTel.cons bind boundary rest).declaration z).isEq →
          Eq_e (Ξ ⋈ σ ⋆ (dTel.cons bind boundary rest).binding z) (σ z) (θ z))
        ?head ?tail z
      case head =>
        intro hne
        refine Eq.mp (congrArg (fun T => Eq_e (Ξ ⋈ T)
          (σ (C.inl (C.singleSlot α))) (θ (C.inl (C.singleSlot α))))
          (dTel.binding_head_instantiate bind boundary rest σ).symm) ?_
        exact slot (fun hEq => hne (Eq.mp (congrArg Bd.isEq
          (dTel.declaration_head_instantiate bind boundary rest σ).symm) hEq))
      case tail =>
        intro γ y hne
        refine Eq.mp (congrArg (fun T => Eq_e (Ξ ⋈ T) (σ (C.inr y)) (θ (C.inr y)))
          (dTel.binding_tail_instantiate bind boundary rest σ y).symm) ?_
        exact Eq_s.slot hrest y (fun hEq => hne (Eq.mp (congrArg Bd.isEq
          (dTel.declaration_tail_instantiate bind boundary rest σ y).symm) hEq))

/-- The first slot of a filling is filled. -/
theorem Wf_s.head {Δ α Ω : C.Arity} {Ξ : Ambient Δ} {bind : dTel Δ α}
    {boundary : Bd (Δ ⋈ α)} {rest : dTel (Δ ⋈ C.single α) Ω}
    {σ : Subst (C.single α ⋈ Ω) Δ}
    (h : Wf_s Ξ (dTel.cons bind boundary rest) σ) :
    Wf_s Ξ (dTel.cons bind boundary (.nil : dTel (Δ ⋈ C.single α) 1))
      (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) := by
  have hd := dTel.declaration_head_instantiate bind boundary rest σ
  have hb := dTel.binding_head_instantiate bind boundary rest σ
  have hd' := dTel.declaration_head_instantiate bind boundary
    (.nil : dTel (Δ ⋈ C.single α) 1) (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i))
  have hb' := dTel.binding_head_instantiate bind boundary
    (.nil : dTel (Δ ⋈ C.single α) 1) (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i))
  refine Wf_s.slotwise ?equation ?filler ?declared
  case equation =>
    intro Λ z
    refine slotCases (α := α) (Δ := 1)
      (motive := fun ⦃Λ⦄ z => ∀ (l r : Expr (Δ ⋈ Λ)),
        (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) ⋆
            (dTel.cons bind boundary (.nil : dTel (Δ ⋈ C.single α) 1)).declaration z
          = Bd.eq l r →
        Eq_e (Ξ ⋈ (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) ⋆
            (dTel.cons bind boundary (.nil : dTel (Δ ⋈ C.single α) 1)).binding z)
          l r) ?_ (fun _ y => (C.unit_is_empty y).elim) z
    intro l r heq
    refine Eq.mp (congrArg (fun T => Eq_e (Ξ ⋈ T) l r) hb'.symm) ?_
    refine Eq.mp (congrArg (fun T => Eq_e (Ξ ⋈ T) l r) hb) ?_
    exact h.equation (C.inl (C.singleSlot α)) l r (hd.trans (hd'.symm.trans heq))
  case filler =>
    intro Λ z
    refine slotCases (α := α) (Δ := 1)
      (motive := fun ⦃Λ⦄ z =>
        ¬ ((fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) ⋆
            (dTel.cons bind boundary (.nil : dTel (Δ ⋈ C.single α) 1)).declaration
              z).isEq →
        Wf_e (Ξ ⋈ (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) ⋆
            (dTel.cons bind boundary (.nil : dTel (Δ ⋈ C.single α) 1)).binding z)
          ((fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) z))
      ?_ (fun _ y => (C.unit_is_empty y).elim) z
    intro hne
    refine Eq.mp (congrArg (fun T => Wf_e (Ξ ⋈ T)
      (σ (C.inl (C.singleSlot α)))) hb'.symm) ?_
    refine Eq.mp (congrArg (fun T => Wf_e (Ξ ⋈ T)
      (σ (C.inl (C.singleSlot α)))) hb) ?_
    exact h.filler (C.inl (C.singleSlot α))
      (fun hEq => hne (Eq.mp (congrArg Bd.isEq (hd.trans hd'.symm)) hEq))
  case declared =>
    intro Λ z
    refine slotCases (α := α) (Δ := 1)
      (motive := fun ⦃Λ⦄ z =>
        ¬ ((fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) ⋆
            (dTel.cons bind boundary (.nil : dTel (Δ ⋈ C.single α) 1)).declaration
              z).isEq →
        Eq_bd (Ξ ⋈ (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) ⋆
            (dTel.cons bind boundary (.nil : dTel (Δ ⋈ C.single α) 1)).binding z)
          ((Ξ ⋈ (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) ⋆
            (dTel.cons bind boundary (.nil : dTel (Δ ⋈ C.single α) 1)).binding
              z).boundaryOf ((fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) z))
          ((fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) ⋆
            (dTel.cons bind boundary (.nil : dTel (Δ ⋈ C.single α) 1)).declaration z))
      ?_ (fun _ y => (C.unit_is_empty y).elim) z
    intro hne
    refine Eq.mp (congrArg₂ (fun (T : dTel Δ α) (b : Bd (Δ ⋈ α)) =>
      Eq_bd (Ξ ⋈ T) ((Ξ ⋈ T).boundaryOf (σ (C.inl (C.singleSlot α)))) b)
      hb'.symm hd'.symm) ?_
    refine Eq.mp (congrArg₂ (fun (T : dTel Δ α) (b : Bd (Δ ⋈ α)) =>
      Eq_bd (Ξ ⋈ T) ((Ξ ⋈ T).boundaryOf (σ (C.inl (C.singleSlot α)))) b) hb hd) ?_
    exact h.declared (C.inl (C.singleSlot α))
      (fun hEq => hne (Eq.mp (congrArg Bd.isEq (hd.trans hd'.symm)) hEq))

/-- The slots after the first of a filling are filled. -/
theorem Wf_s.tail {Δ α Ω : C.Arity} {Ξ : Ambient Δ} {bind : dTel Δ α}
    {boundary : Bd (Δ ⋈ α)} {rest : dTel (Δ ⋈ C.single α) Ω}
    {σ : Subst (C.single α ⋈ Ω) Δ}
    (h : Wf_s Ξ (dTel.cons bind boundary rest) σ) :
    Wf_s Ξ (dTel.instantiate (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) rest)
      (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j)) := by
  refine Wf_s.slotwise (fun Λ y l r heq => ?_) (fun Λ y hne => ?_)
    (fun Λ y hne => ?_)
  · refine Eq.mp (congrArg (fun T => Eq_e (Ξ ⋈ T) l r)
      (dTel.binding_tail_instantiate bind boundary rest σ y)) ?_
    exact h.equation (C.inr y) l r
      ((dTel.declaration_tail_instantiate bind boundary rest σ y).trans heq)
  · refine Eq.mp (congrArg (fun T => Wf_e (Ξ ⋈ T) (σ (C.inr y)))
      (dTel.binding_tail_instantiate bind boundary rest σ y)) ?_
    exact h.filler (C.inr y) (fun hEq => hne (Eq.mp (congrArg Bd.isEq
      (dTel.declaration_tail_instantiate bind boundary rest σ y)) hEq))
  · refine Eq.mp (congrArg₂ (fun (T : dTel Δ Λ) (b : Bd (Δ ⋈ Λ)) =>
      Eq_bd (Ξ ⋈ T) ((Ξ ⋈ T).boundaryOf (σ (C.inr y))) b)
      (dTel.binding_tail_instantiate bind boundary rest σ y)
      (dTel.declaration_tail_instantiate bind boundary rest σ y)) ?_
    exact h.declared (C.inr y) (fun hEq => hne (Eq.mp (congrArg Bd.isEq
      (dTel.declaration_tail_instantiate bind boundary rest σ y)) hEq))

/-- Agreement of two fillings of a base-substituted telescope, from the
comparison at every slot. -/
theorem Eq_s.slotwise_actBase {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {Γ Ω : C.Arity} (Θ : dTel Γ Ω) (κ : Subst Γ Δ) {σ θ : Subst Ω Δ},
      (∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
          ¬ (σ ⋆ (dTel.actBase κ Θ).declaration z).isEq →
          Eq_e (Ξ ⋈ σ ⋆ (dTel.actBase κ Θ).binding z) (σ z) (θ z)) →
      Eq_s Ξ (dTel.actBase κ Θ) σ θ
  | _, _, .nil, _, _, _, _ => .nil
  | _, _, .cons (α := α) (Δ := Ω) bind boundary rest, κ, σ, θ, slot => by
      have hd := dTel.declaration_head_instantiate (dTel.actBase κ bind)
        (Bd.act (Γ := 1) κ α boundary)
        (dTel.actBase (Subst.lift κ (C.single α)) rest) σ
      have hb := dTel.binding_head_instantiate (dTel.actBase κ bind)
        (Bd.act (Γ := 1) κ α boundary)
        (dTel.actBase (Subst.lift κ (C.single α)) rest) σ
      have hcat := dTel.actBase_comp (Subst.lift κ (C.single α))
        (Subst.copair (Subst.id Δ)
          (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i))) rest
      refine .cons ?slot ?hrest
      case slot =>
        intro hne
        refine Eq.mp (congrArg (fun T => Eq_e (Ξ ⋈ T)
          (σ (C.inl (C.singleSlot α))) (θ (C.inl (C.singleSlot α)))) hb) ?_
        exact slot (C.inl (C.singleSlot α))
          (fun hEq => hne (Eq.mp (congrArg Bd.isEq hd) hEq))
      case hrest =>
        have hdt : ∀ ⦃γ : C.Arity⦄ (y : Ω ∋ γ),
            (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j)) ⋆
                (dTel.actBase (Subst.comp (Γ := 1) (Subst.lift κ (C.single α))
                  (Subst.copair (Subst.id Δ)
                    (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)))) rest).declaration y
              = σ ⋆ (dTel.actBase κ (dTel.cons bind boundary rest)).declaration
                  (C.inr y) := by
          intro γ y
          refine Eq.trans (congrArg (fun T =>
            (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j)) ⋆ dTel.declaration T y) hcat) ?_
          exact (dTel.declaration_tail_instantiate _ _ _ σ y).symm
        have hbt : ∀ ⦃γ : C.Arity⦄ (y : Ω ∋ γ),
            (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j)) ⋆
                (dTel.actBase (Subst.comp (Γ := 1) (Subst.lift κ (C.single α))
                  (Subst.copair (Subst.id Δ)
                    (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)))) rest).binding y
              = σ ⋆ (dTel.actBase κ (dTel.cons bind boundary rest)).binding
                  (C.inr y) := by
          intro γ y
          refine Eq.trans (congrArg (fun (T : dTel Δ Ω) =>
            dTel.instantiate (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j))
              (dTel.binding T y)) hcat) ?_
          exact (dTel.binding_tail_instantiate _ _ _ σ y).symm
        refine Eq.mp (congrArg (fun T =>
          Eq_s Ξ T (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j))
            (fun ⦃β⦄ (j : Ω ∋ β) => θ (C.inr j))) hcat) ?_
        refine Eq_s.slotwise_actBase rest _ ?_
        intro γ y hne
        refine Eq.mp (congrArg (fun T => Eq_e (Ξ ⋈ T) (σ (C.inr y)) (θ (C.inr y)))
          (hbt y).symm) ?_
        exact slot (C.inr y) (fun hEq => hne (Eq.mp (congrArg Bd.isEq
          (hdt y).symm) hEq))

/-- Agreement of two fillings, from the comparison at every slot. -/
theorem Eq_s.slotwise {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω}
    {σ θ : Subst Ω Δ}
    (slot : ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ), ¬ (σ ⋆ Θ.declaration z).isEq →
        Eq_e (Ξ ⋈ σ ⋆ Θ.binding z) (σ z) (θ z)) :
    Eq_s Ξ Θ σ θ := by
  have hid := dTel.actBase_id Θ
  refine Eq.mp (congrArg (fun T => Eq_s Ξ T σ θ) hid) ?_
  refine Eq_s.slotwise_actBase Θ (Subst.id Δ) ?_
  intro Λ z hne
  refine Eq.mp (congrArg (fun T => Eq_e (Ξ ⋈ σ ⋆ dTel.binding T z) (σ z) (θ z))
    hid.symm) ?_
  exact slot z (fun hEq => hne (Eq.mp (congrArg (fun T =>
    (σ ⋆ dTel.declaration T z).isEq) hid.symm) hEq))

/-- A well-formed filling agrees with itself. -/
theorem Eq_s.refl {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω} {σ : Subst Ω Δ}
    (h : Wf_s Ξ Θ σ) : Eq_s Ξ Θ σ σ :=
  Eq_s.slotwise (fun ⦃_⦄ z hne => .refl (h.filler z hne))

/-- The slots after the first of two agreeing fillings agree. -/
theorem Eq_s.tail {Δ α Ω : C.Arity} {Ξ : Ambient Δ} {bind : dTel Δ α}
    {boundary : Bd (Δ ⋈ α)} {rest : dTel (Δ ⋈ C.single α) Ω}
    {σ θ : Subst (C.single α ⋈ Ω) Δ}
    (h : Eq_s Ξ (dTel.cons bind boundary rest) σ θ) :
    Eq_s Ξ (dTel.instantiate (fun ⦃β⦄ (i : C.single α ∋ β) => σ (C.inl i)) rest)
      (fun ⦃β⦄ (j : Ω ∋ β) => σ (C.inr j))
      (fun ⦃β⦄ (j : Ω ∋ β) => θ (C.inr j)) := by
  refine Eq_s.slotwise (fun Λ y hne => ?_)
  refine Eq.mp (congrArg (fun T => Eq_e ((Ξ ⋈ T)) (σ (C.inr y)) (θ (C.inr y)))
    (dTel.binding_tail_instantiate bind boundary rest σ y)) ?_
  exact h.slot (C.inr y) (fun hEq => hne (Eq.mp (congrArg Bd.isEq
    (dTel.declaration_tail_instantiate bind boundary rest σ y)) hEq))

/-- A well-formed filling is equal to itself. -/
theorem Wf_s.refl {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω} {σ : Subst Ω Δ}
    (h : Wf_s Ξ Θ σ) : Eq_s Ξ Θ σ σ :=
  Eq_s.slotwise (fun _ z hne => .refl (h.filler z hne))

/-- Equality of boundaries under the substitution rule. -/
theorem Eq_bd.congr {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω}
    (σ θ : Subst Ω Δ) (hΘ : Wf_t Ξ Θ) (hσ : Wf_s Ξ Θ σ) (hθ : Wf_s Ξ Θ θ)
    (agree : Eq_s Ξ Θ σ θ) :
    ∀ {β β' : Bd (Δ ⋈ Ω)}, Eq_bd (Ξ ⋈ Θ) β β' → Eq_bd Ξ (σ ⋆ β) (θ ⋆ β')
  | _, _, .sort => .sort
  | _, _, .of h => .of (Eq_e.congr σ θ hΘ hσ hθ agree h)
  | _, _, .eq hl hr =>
      .eq (Eq_e.congr σ θ hΘ hσ hθ agree hl) (Eq_e.congr σ θ hΘ hσ hθ agree hr)

private def Wf_t.parts : {Δ Ω : C.Arity} → Ambient Δ → dTel Δ Ω → Prop
  | _, _, _, .nil => True
  | _, _, Ξ, .cons bind boundary rest =>
      Wf_t Ξ bind ∧ Wf_bd Ξ bind boundary ∧
        Wf_t ((Ξ ⋈ dTel.cons bind boundary .nil)) rest

private theorem Wf_t.toParts {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {Ω : C.Arity} {Θ : dTel Δ Ω}, Wf_t Ξ Θ → Wf_t.parts Ξ Θ
  | _, _, .nil => by rw [Wf_t.parts]; trivial
  | _, _, .cons hbind hboundary hrest => by
      rw [Wf_t.parts]
      exact ⟨hbind, hboundary, hrest⟩

/-- A well-formed telescope binds well-formed entries at its first slot, declares
a well-formed boundary there, and is well formed after it. -/
theorem Wf_t.cons_inv {Δ α Ω : C.Arity} {Ξ : Ambient Δ} {bind : dTel Δ α}
    {boundary : Bd (Δ ⋈ α)} {rest : dTel (Δ ⋈ C.single α) Ω}
    (h : Wf_t Ξ (dTel.cons bind boundary rest)) :
    Wf_t Ξ bind ∧ Wf_bd Ξ bind boundary ∧
      Wf_t ((Ξ ⋈ dTel.cons bind boundary .nil)) rest := by
  have hp := Wf_t.toParts h
  rwa [Wf_t.parts] at hp

/-- Concatenating well-formed telescopes is well formed. -/
theorem Wf_t.concatenate {Δ : C.Arity} {Ξ : Ambient Δ} :
    ∀ {Ω Φ : C.Arity} {Θ : dTel Δ Ω} {X : dTel (Δ ⋈ Ω) Φ},
      Wf_t Ξ Θ → Wf_t (Ξ ⋈ Θ) X → Wf_t Ξ (dTel.concatenate Θ X)
  | _, _, _, X, .nil, hX =>
      Eq.mp (congrArg (fun A => Wf_t A X) (dTel.concatenate_nil Ξ)) hX
  | _, _, _, X, .cons (bind := bind) (boundary := boundary) (rest := rest)
      hbind hboundary hrest, hX =>
      .cons hbind hboundary (Wf_t.concatenate hrest
        (Eq.mp (congrArg (fun A => Wf_t A X)
          (dTel.concatenate_assoc Ξ (dTel.cons bind boundary .nil) rest).symm) hX))

/-! ### Telescopes -/

/-- The left side of a well-formed equational declaration is well formed. -/
theorem Wf_bd.eq_left {Δ Λ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Λ}
    {l r : Expr (Δ ⋈ Λ)} : Wf_bd Ξ Θ (.eq l r) → Wf_e (Ξ ⋈ Θ) l
  | .eq hl _ _ => hl

/-- The right side of a well-formed equational declaration is well formed. -/
theorem Wf_bd.eq_right {Δ Λ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Λ}
    {l r : Expr (Δ ⋈ Λ)} : Wf_bd Ξ Θ (.eq l r) → Wf_e (Ξ ⋈ Θ) r
  | .eq _ hr _ => hr

/-- The two sides of a well-formed equational declaration have equal computed
boundaries. -/
theorem Wf_bd.eq_boundary {Δ Λ : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Λ}
    {l r : Expr (Δ ⋈ Λ)} : Wf_bd Ξ Θ (.eq l r) →
      Eq_bd (Ξ ⋈ Θ) ((Ξ ⋈ Θ).boundaryOf l) ((Ξ ⋈ Θ).boundaryOf r)
  | .eq _ _ heq => heq

/-- Two telescopes of one arity are equal when at every slot the entries bound
are equal and the declarations are equal over the ambient built from the
preceding slots and those entries. -/
def Eq_t : {Δ Ω : C.Arity} → Ambient Δ → dTel Δ Ω → dTel Δ Ω → Prop
  | _, _, _, .nil, Θ' => Θ' = .nil
  | Δ, _, Ξ, .cons (α := α) (Δ := Ω) bind boundary rest, Θ' =>
      ∃ (bind' : dTel Δ α) (boundary' : Bd (Δ ⋈ α))
        (rest' : dTel (Δ ⋈ C.single α) Ω),
        Θ' = dTel.cons bind' boundary' rest' ∧ Eq_t Ξ bind bind' ∧
          Eq_bd (Ξ ⋈ bind) boundary boundary' ∧
          Eq_t (Ξ ⋈ dTel.cons bind boundary .nil) rest rest'

/-- Telescopes with no slots are equal. -/
theorem Eq_t.nil {Δ : C.Arity} {Ξ : Ambient Δ} :
    Eq_t Ξ (.nil : dTel Δ 1) .nil := by
  rw [Eq_t]

/-- Telescopes are equal when their first slots bind equal entries and declare
equal boundaries and their tails are equal. -/
theorem Eq_t.cons {Δ α Ω : C.Arity} {Ξ : Ambient Δ} {bind bind' : dTel Δ α}
    {boundary boundary' : Bd (Δ ⋈ α)} {rest rest' : dTel (Δ ⋈ C.single α) Ω}
    (hbind : Eq_t Ξ bind bind')
    (hboundary : Eq_bd (Ξ ⋈ bind) boundary boundary')
    (hrest : Eq_t (Ξ ⋈ dTel.cons bind boundary .nil) rest rest') :
    Eq_t Ξ (dTel.cons bind boundary rest) (dTel.cons bind' boundary' rest') := by
  rw [Eq_t]
  exact ⟨bind', boundary', rest', rfl, hbind, hboundary, hrest⟩

/-- A telescope equal to one with no slots has none. -/
theorem Eq_t.nil_inv {Δ : C.Arity} {Ξ : Ambient Δ} {Θ' : dTel Δ 1}
    (h : Eq_t Ξ .nil Θ') : Θ' = .nil := by
  rw [Eq_t] at h
  exact h

/-- A telescope equal to one with a first slot has a matching first slot. -/
theorem Eq_t.cons_inv {Δ α Ω : C.Arity} {Ξ : Ambient Δ} {bind : dTel Δ α}
    {boundary : Bd (Δ ⋈ α)} {rest : dTel (Δ ⋈ C.single α) Ω}
    {Θ' : dTel Δ (C.single α ⋈ Ω)}
    (h : Eq_t Ξ (dTel.cons bind boundary rest) Θ') :
    ∃ (bind' : dTel Δ α) (boundary' : Bd (Δ ⋈ α))
      (rest' : dTel (Δ ⋈ C.single α) Ω),
      Θ' = dTel.cons bind' boundary' rest' ∧ Eq_t Ξ bind bind' ∧
        Eq_bd (Ξ ⋈ bind) boundary boundary' ∧
        Eq_t (Ξ ⋈ dTel.cons bind boundary .nil) rest rest' := by
  rw [Eq_t] at h
  exact h

/-- Two telescopes of one arity are equal over two ambients when at every slot
the entries bound are equal and the declarations are equal over both of the
ambients built from the preceding slots and those entries. -/
def Eq_t.Both : {Δ Ω : C.Arity} →
    Ambient Δ → Ambient Δ → dTel Δ Ω → dTel Δ Ω → Prop
  | _, _, _, _, .nil, Θ' => Θ' = .nil
  | Δ, _, Ξ, Ξ', .cons (α := α) (Δ := Ω) bind boundary rest, Θ' =>
      ∃ (bind' : dTel Δ α) (boundary' : Bd (Δ ⋈ α))
        (rest' : dTel (Δ ⋈ C.single α) Ω),
        Θ' = dTel.cons bind' boundary' rest' ∧ Eq_t.Both Ξ Ξ' bind bind' ∧
          Eq_bd (Ξ ⋈ bind) boundary boundary' ∧
          Eq_bd (Ξ' ⋈ bind') boundary boundary' ∧
          Eq_t.Both (Ξ ⋈ dTel.cons bind boundary .nil)
            (Ξ' ⋈ dTel.cons bind' boundary' .nil) rest rest'

/-- Telescopes with no slots are equal over two ambients. -/
theorem Eq_t.Both.nil {Δ : C.Arity} {Ξ Ξ' : Ambient Δ} :
    Eq_t.Both Ξ Ξ' (.nil : dTel Δ 1) .nil := by
  rw [Eq_t.Both]

/-- Telescopes are equal over two ambients when their first slots bind equal
entries and declare boundaries equal over both, and their tails are equal. -/
theorem Eq_t.Both.cons {Δ α Ω : C.Arity} {Ξ Ξ' : Ambient Δ} {bind bind' : dTel Δ α}
    {boundary boundary' : Bd (Δ ⋈ α)} {rest rest' : dTel (Δ ⋈ C.single α) Ω}
    (hbind : Eq_t.Both Ξ Ξ' bind bind')
    (hboundary : Eq_bd (Ξ ⋈ bind) boundary boundary')
    (hboundary' : Eq_bd (Ξ' ⋈ bind') boundary boundary')
    (hrest : Eq_t.Both (Ξ ⋈ dTel.cons bind boundary .nil)
      (Ξ' ⋈ dTel.cons bind' boundary' .nil) rest rest') :
    Eq_t.Both Ξ Ξ' (dTel.cons bind boundary rest)
      (dTel.cons bind' boundary' rest') := by
  rw [Eq_t.Both]
  exact ⟨bind', boundary', rest', rfl, hbind, hboundary, hboundary', hrest⟩

/-- A telescope equal over two ambients to one with no slots has none. -/
theorem Eq_t.Both.nil_inv {Δ : C.Arity} {Ξ Ξ' : Ambient Δ} {Θ' : dTel Δ 1}
    (h : Eq_t.Both Ξ Ξ' .nil Θ') : Θ' = .nil := by
  rw [Eq_t.Both] at h
  exact h

/-- A telescope equal over two ambients to one with a first slot has a matching
first slot. -/
theorem Eq_t.Both.cons_inv {Δ α Ω : C.Arity} {Ξ Ξ' : Ambient Δ} {bind : dTel Δ α}
    {boundary : Bd (Δ ⋈ α)} {rest : dTel (Δ ⋈ C.single α) Ω}
    {Θ' : dTel Δ (C.single α ⋈ Ω)}
    (h : Eq_t.Both Ξ Ξ' (dTel.cons bind boundary rest) Θ') :
    ∃ (bind' : dTel Δ α) (boundary' : Bd (Δ ⋈ α))
      (rest' : dTel (Δ ⋈ C.single α) Ω),
      Θ' = dTel.cons bind' boundary' rest' ∧ Eq_t.Both Ξ Ξ' bind bind' ∧
        Eq_bd (Ξ ⋈ bind) boundary boundary' ∧
        Eq_bd (Ξ' ⋈ bind') boundary boundary' ∧
        Eq_t.Both (Ξ ⋈ dTel.cons bind boundary .nil)
          (Ξ' ⋈ dTel.cons bind' boundary' .nil) rest rest' := by
  rw [Eq_t.Both] at h
  exact h

/-- Telescopes equal over two ambients are equal over the first. -/
theorem Eq_t.Both.toEq_t {Δ : C.Arity} {Ξ Ξ' : Ambient Δ} :
    ∀ {Ω : C.Arity} {Θ Θ' : dTel Δ Ω}, Eq_t.Both Ξ Ξ' Θ Θ' → Eq_t Ξ Θ Θ'
  | _, .nil, _, h => by
      obtain rfl := Eq_t.Both.nil_inv h
      exact Eq_t.nil
  | _, .cons _ _ _, _, h => by
      obtain ⟨_, _, _, rfl, hbind, hboundary, _, hrest⟩ := Eq_t.Both.cons_inv h
      exact Eq_t.cons hbind.toEq_t hboundary hrest.toEq_t

/-- An ambient is well formed. -/
def Ambient.Wf {Δ : C.Arity} (Ξ : Ambient Δ) : Prop :=
  Wf_t (.nil : Ambient 1) Ξ

section SmokeTests

variable {Δ Ω : C.Arity} (Ξ : Ambient Δ) (e e' : Expr Δ) (β β' : Bd Δ)
  (Θ : dTel Δ Ω) (σ : Subst Ω Δ)

example : Prop := Ξ ⊢ e
example : Prop := Ξ ⊢ e ≈ e'
example : Prop := Ξ ⊢ β ≈ β'
example : Prop := Ξ ⊢ σ : Θ

end SmokeTests

