import HigherRankSyntax.Typing.Telescope

/-!
# The judgements

Four relations over an ambient, well formed or not, defined by one simultaneous
induction: an expression is well formed, two expressions are equal, two
boundaries are equal, and a substitution fills a telescope.  A slot's
declaration and the entries it binds are already read over the whole ambient, so
no premise restricts a substitution to the slots preceding it.
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
      (agree : ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
          ¬ (σ ⋆ Θ.declaration z).isEq →
          Eq_e (Ξ ⋈ σ ⋆ Θ.binding z) (σ z) (θ z))
      (h : Eq_e (Ξ ⋈ Θ) e e') :
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
  | mk {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω} {σ : Subst Ω Δ}
      (equation : ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ) (l r : Expr (Δ ⋈ Λ)),
          σ ⋆ Θ.declaration z = .eq l r →
          Eq_e (Ξ ⋈ σ ⋆ Θ.binding z) l r)
      (filler : ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
          ¬ (σ ⋆ Θ.declaration z).isEq →
          Wf_e (Ξ ⋈ σ ⋆ Θ.binding z) (σ z))
      (declared : ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
          ¬ (σ ⋆ Θ.declaration z).isEq →
          Eq_bd (Ξ ⋈ σ ⋆ Θ.binding z)
            ((Ξ ⋈ σ ⋆ Θ.binding z).boundaryOf (σ z))
            (σ ⋆ Θ.declaration z)) :
      Wf_s Ξ Θ σ

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

/-- A filling agrees with itself at every non-equational slot. -/
theorem Wf_s.agree {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω} {σ : Subst Ω Δ} :
    Wf_s Ξ Θ σ → ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ), ¬ (σ ⋆ Θ.declaration z).isEq →
      Eq_e (Ξ ⋈ σ ⋆ Θ.binding z) (σ z) (σ z)
  | .mk _ filler _, _, z, hne => .refl (filler z hne)

/-- Equality of boundaries under the substitution rule. -/
theorem Eq_bd.congr {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω}
    (σ θ : Subst Ω Δ) (hΘ : Wf_t Ξ Θ) (hσ : Wf_s Ξ Θ σ) (hθ : Wf_s Ξ Θ θ)
    (agree : ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
        ¬ (σ ⋆ Θ.declaration z).isEq → Eq_e (Ξ ⋈ σ ⋆ Θ.binding z) (σ z) (θ z)) :
    ∀ {β β' : Bd (Δ ⋈ Ω)}, Eq_bd (Ξ ⋈ Θ) β β' → Eq_bd Ξ (σ ⋆ β) (θ ⋆ β')
  | _, _, .sort => .sort
  | _, _, .of h => .of (Eq_e.congr σ θ hΘ hσ hθ agree h)
  | _, _, .eq hl hr =>
      .eq (Eq_e.congr σ θ hΘ hσ hθ agree hl) (Eq_e.congr σ θ hΘ hσ hθ agree hr)

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

/-- Two telescopes of one arity are equal when their slots are declared equal. -/
def Eq_t : {Δ Ω : C.Arity} → Ambient Δ → dTel Δ Ω → dTel Δ Ω → Prop
  | _, _, Ξ, Θ, Θ' => ∀ ⦃Λ : C.Arity⦄ (z : _ ∋ Λ),
      Eq_bd (Ξ ⋈ Θ ⋈ Θ.binding z) (Θ.declaration z) (Θ'.declaration z) ∧
      Eq_t (Ξ ⋈ Θ) (Θ.binding z) (Θ'.binding z)
termination_by Δ Ω _ _ _ => Ω
decreasing_by exact ⟨z⟩

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

