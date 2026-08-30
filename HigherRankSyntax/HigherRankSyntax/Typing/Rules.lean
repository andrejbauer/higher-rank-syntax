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
      (hl : Wf_e (Ξ.extend (Ξ.binding q)) l)
      (hr : Wf_e (Ξ.extend (Ξ.binding q)) r)
      (fill : Wf_s Ξ (Ξ.binding q) args) :
      Eq_e Ξ (Subst.act (Γ := Δ) (Ξ := 1) args 1 l)
        (Subst.act (Γ := Δ) (Ξ := 1) args 1 r)
  | subst {Δ Ω : C.Arity} {Ξ : Ambient Δ} {Θ : dTel Δ Ω} {e e' : Expr (Δ ⋈ Ω)}
      (σ θ : Subst Ω Δ) (hσ : Wf_s Ξ Θ σ) (hθ : Wf_s Ξ Θ θ)
      (agree : ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
          ¬ (Bd.act (Ξ := 1) σ Λ (Θ.declaration z)).isEq →
          Eq_e (Ξ.extend (dTel.instantiate σ (Θ.binding z))) (σ z) (θ z))
      (h : Eq_e (Ξ.extend Θ) e e') :
      Eq_e Ξ (Subst.act (Γ := Δ) (Ξ := 1) σ 1 e) (Subst.act (Γ := Δ) (Ξ := 1) θ 1 e')

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
          Bd.act (Ξ := 1) σ Λ (Θ.declaration z) = .eq l r →
          Eq_e (Ξ.extend (dTel.instantiate σ (Θ.binding z))) l r)
      (filler : ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
          ¬ (Bd.act (Ξ := 1) σ Λ (Θ.declaration z)).isEq →
          Wf_e (Ξ.extend (dTel.instantiate σ (Θ.binding z))) (σ z))
      (declared : ∀ ⦃Λ : C.Arity⦄ (z : Ω ∋ Λ),
          ¬ (Bd.act (Ξ := 1) σ Λ (Θ.declaration z)).isEq →
          Eq_bd (Ξ.extend (dTel.instantiate σ (Θ.binding z)))
            ((Ξ.extend (dTel.instantiate σ (Θ.binding z))).boundaryOf (σ z))
            (Bd.act (Ξ := 1) σ Λ (Θ.declaration z))) :
      Wf_s Ξ Θ σ

end

/-! ### Notation

One turnstile, overloaded on what stands to the right of it: an expression, a
substitution, or a telescope.  The arguments parse above `≈` so that
`Ξ ⊢ e ≈ e'` is not read as `Ξ ⊢ (e ≈ e')`. -/

@[inherit_doc Wf_e] notation:50 Ξ " ⊢ " e:51 => Wf_e Ξ e
@[inherit_doc Eq_e] notation:50 Ξ " ⊢ " e:51 " ≈ " e':51 => Eq_e Ξ e e'
@[inherit_doc Eq_bd] notation:50 Ξ " ⊢ " β:51 " ≈ " β':51 => Eq_bd Ξ β β'
@[inherit_doc Wf_s] notation:50 Ξ " ⊢ " σ:51 " : " Θ:51 => Wf_s Ξ Θ σ

/-! ### Well-formed telescopes -/

/-- A declaration is well formed over the ambient extended by the entries its
slot binds. -/
def Wf_bd {Δ Λ : C.Arity} (Ξ : Ambient Δ) (Θ : dTel Δ Λ) : Bd (Δ ⋈ Λ) → Prop
  | .sort => True
  | .of S =>
      Wf_e (Ξ.extend Θ) S ∧
      Eq_bd (Ξ.extend Θ) ((Ξ.extend Θ).boundaryOf S) .sort
  | .eq l r =>
      Wf_e (Ξ.extend Θ) l ∧ Wf_e (Ξ.extend Θ) r ∧
      Eq_bd (Ξ.extend Θ) ((Ξ.extend Θ).boundaryOf l) ((Ξ.extend Θ).boundaryOf r)

/-- A telescope over an ambient is well formed. -/
def Wf_t : {Δ Ω : C.Arity} → Ambient Δ → dTel Δ Ω → Prop
  | _, _, _, .nil => True
  | _, _, Ξ, .cons bind boundary rest =>
      Wf_t Ξ bind ∧ Wf_bd Ξ bind boundary ∧
      Wf_t (Ξ.extend (dTel.cons bind boundary .nil)) rest

/-- Two telescopes of one arity are equal when their slots are declared equal. -/
def Eq_t : {Δ Ω : C.Arity} → Ambient Δ → dTel Δ Ω → dTel Δ Ω → Prop
  | _, _, Ξ, Θ, Θ' => ∀ ⦃Λ : C.Arity⦄ (z : _ ∋ Λ),
      Eq_bd ((Ξ.extend Θ).extend (Θ.binding z)) (Θ.declaration z) (Θ'.declaration z) ∧
      Eq_t (Ξ.extend Θ) (Θ.binding z) (Θ'.binding z)
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

