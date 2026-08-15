import HigherRankSyntax.Instantiation
import HigherRankSyntax.Interchange
import Batteries.Tactic.Trans

/-!
# The three relative-monad laws for `Subst.act`

* `act_id` — the identity substitution acts as the identity (unit_right).
* `act_η` — acting on an η-expansion applies the substitution (unit_left).
* `act_comp` — action by a composite factors (comp_lift).
-/

variable {A : Type} {C : Carrier A}

/-- **`act_id`** — the identity substitution acts as the identity (unit_right). -/
theorem act_id (Γ Φ : C.Arity) {τ : C.Ty} (e : Expr (Γ ⋈ Φ) τ) :
  Subst.act (Subst.id Γ) (Γ := 1) Φ e = e
  := act_idOfη (Γ := 1) (Subst.id Γ)
       (fun z => by rw [C.unit_left Γ z]; rfl) Φ e

/-- **`act_η`** — acting on an η-expansion reduces to applying `σ` (unit_left). -/
theorem act_η
    {Δ Ξ : C.Arity}
    (σ : Subst Δ Ξ) (Θ : C.Arity) {τ : C.Ty} (x : Δ ∋[τ] Θ) :
  σ.act (Γ := 1) Θ (.η x) = σ x
  := by
  rw [Expr.η.eq_1]
  trans
  · convert act_middle (Γ := 1) σ Θ x (fun {_} {_} i => Expr.η (C.inr i)) using 2
    · congr 1
      rw [C.unit_left Δ x]
  · calc
      _ = Subst.act (Subst.instId Ξ Θ) 1 (σ x) := by
            congr 1
            funext Ω υ i
            apply act_η_right
      _ = σ x := by apply act_inst_id

/-- Acting by the eta-substitution of a renaming is the renaming action. -/
theorem act_ofRenaming
    {Γ Δ Φ : C.Arity} (ρ : Γ →ʳ Δ) {τ : C.Ty} :
    ∀ e : Expr (Γ ⋈ Φ) τ,
      Subst.act (Subst.ofRenaming ρ) (Γ := 1) Φ e =
        Renaming.act (ρ ⇑ʳ Φ) e
  | .ap (α := β) x args => by
      rcases C.cover Γ Φ x with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · have hz :
          (C.inl z : Γ ⋈ Φ ∋[τ] β) =
            C.inl (C.inr z : 1 ⋈ Γ ∋[τ] β) := by
            congr 1
            exact (C.unit_left Γ z).symm
        conv_lhs => rw [hz]
        rw [Renaming.act_ap]
        conv_lhs => unfold Subst.act
        simp only [Subst.threeway_middle]
        rw [Subst.ofRenaming, act_inst_η]
        congr 1
        · exact (Renaming.extend_inl ρ z).symm
        · funext Ω υ i
          rw [← Renaming.extend_assoc]
          exact act_ofRenaming (Φ := Φ ⋈ Ω) ρ (args i)
      · rw [Renaming.act_ap]
        trans .ap (C.inr z : Δ ⋈ Φ ∋[τ] β)
          (fun {_} {_} i =>
            Subst.act (Subst.ofRenaming ρ) (Γ := 1) (Φ ⋈ _) (args i))
        · convert act_right (Γ := 1) (Subst.ofRenaming ρ) Φ z args using 1
        · congr 1
          · exact (Renaming.extend_inr ρ z).symm
          · funext Ω υ i
            rw [← Renaming.extend_assoc]
            exact act_ofRenaming (Φ := Φ ⋈ Ω) ρ (args i)
termination_by e =>
  (⟨_, _, e⟩ : Σ Γ : C.Arity, Σ τ : C.Ty, Expr Γ τ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args i

/-- Eta-substitution below a fixed prefix is the corresponding prefixed
renaming action. -/
theorem act_ofRenaming_prefixed
    {S Γ Δ Φ : C.Arity} (ρ : Γ →ʳ Δ) {τ : C.Ty} :
    ∀ e : Expr (S ⋈ Γ ⋈ Φ) τ,
      Subst.act (Γ := S)
          (fun ⦃_⦄ ⦃_⦄ x => Expr.η (C.inr (ρ x))) Φ e =
        Renaming.act ((Renaming.prefixed S ρ) ⇑ʳ Φ) e
  | .ap x args => by
      head_cases x with z
      case right =>
        rw [act_right, Renaming.act_ap]
        congr 1
        · exact (Renaming.extend_inr (Renaming.prefixed S ρ) z).symm
        · funext Ω υ i
          rw [← Renaming.extend_assoc]
          exact act_ofRenaming_prefixed (S := S) (Φ := Φ ⋈ Ω) ρ (args i)
      case middle =>
        rw [act_middle, Renaming.act_ap]
        rw [Renaming.extend_inl, Renaming.prefixed_inr]
        rw [act_inst_η]
        congr 1
        funext Ω υ i
        rw [← Renaming.extend_assoc]
        exact act_ofRenaming_prefixed (S := S) (Φ := Φ ⋈ Ω) ρ (args i)
      case left =>
        rw [act_left, Renaming.act_ap]
        rw [Renaming.extend_inl, Renaming.prefixed_inl]
        congr 1
        funext Ω υ i
        rw [← Renaming.extend_assoc]
        exact act_ofRenaming_prefixed (S := S) (Φ := Φ ⋈ Ω) ρ (args i)
termination_by e =>
  (⟨_, _, e⟩ : Σ Γ : C.Arity, Σ τ : C.Ty, Expr Γ τ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args i

/-- **`act_comp`** — action by a composite factors (comp_lift). -/
theorem act_comp
    {Γ Δ Θ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Θ)) (θ : Subst Θ (Γ ⋈ Ξ))
    (Φ : C.Arity) {τ : C.Ty} (e : Expr (Γ ⋈ Δ ⋈ Φ) τ) :
  Subst.act (Subst.comp σ θ) Φ e = θ.act Φ (σ.act Φ e)
  := by
  match e with
  | .ap (α := β) x args =>
    head_cases x with z
    case right =>
      rw [act_right, act_right, act_right]
      congr 1
      funext Ω υ i
      apply act_comp σ θ (Φ ⋈ Ω) (args i)
    case middle =>
      rw [act_middle, act_middle, act_interchange]
      congr 1
      funext Ω υ i
      apply act_comp σ θ (Φ ⋈ Ω) (args i)
    case left =>
      rw [act_left, act_left, act_left]
      congr 1
      funext Ω υ i
      apply act_comp σ θ (Φ ⋈ Ω) (args i)
termination_by (⟨_, _, e⟩ : Σ Γ : C.Arity, Σ τ : C.Ty, Expr Γ τ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args _

/-- Changing only the current-depth arity commutes with raw substitution. -/
theorem act_cast_suffix {Γ Δ Ξ Φ Ψ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Ξ)) (h : Φ = Ψ)
    {τ : C.Ty} (e : Expr (Γ ⋈ Δ ⋈ Φ) τ) :
    cast (congrArg (fun Λ => Expr (Γ ⋈ Ξ ⋈ Λ) τ) h)
      (Subst.act σ Φ e) =
      Subst.act σ Ψ
        (cast (congrArg (fun Λ => Expr (Γ ⋈ Δ ⋈ Λ) τ) h) e) := by
  subst Ψ
  rfl

namespace Subst

private theorem cast_mul_assoc (Γ Φ Ψ : C.Arity) {τ : C.Ty}
    (e : Expr ((Γ ⋈ Φ) ⋈ Ψ) τ) :
    cast (congrArg (fun Ω => Expr Ω τ) (mul_assoc Γ Φ Ψ)) e = e := by
  have hp : congrArg (fun Ω => Expr Ω τ) (mul_assoc Γ Φ Ψ) = rfl :=
    Subsingleton.elim _ _
  cases hp
  rfl

/-- Extend a substitution by identity fillers for a fixed suffix.  This is the
special case of `pushforward` used by dependent telescope concatenation. -/
def lift {Γ Δ : C.Arity} (σ : Subst Γ Δ) (Φ : C.Arity) :
    Subst (Γ ⋈ Φ) (Δ ⋈ Φ) :=
  pushforward (Γ := 1) (Ω := Φ) σ (Subst.id (Γ ⋈ Φ))

/-- Extend a substitution below a fixed prefix by identity fillers for a fixed
suffix. -/
def liftPrefixed {S Γ Δ : C.Arity} (σ : Subst Γ (S ⋈ Δ))
    (Φ : C.Arity) : Subst (Γ ⋈ Φ) (S ⋈ (Δ ⋈ Φ)) :=
  pushforward (Γ := S) (Ω := Φ) σ
    (fun ⦃Λ⦄ ⦃τ⦄ x => Expr.η
      (cast (congrArg (fun Ω => Ω ∋[τ] Λ) (mul_assoc S Γ Φ).symm)
        (C.inr x)))

/-- Acting by a fixed-prefix lift is action below its fixed suffix. -/
theorem act_liftPrefixed {S Γ Δ Φ Ψ : C.Arity}
    (σ : Subst Γ (S ⋈ Δ)) {τ : C.Ty}
    (e : Expr (S ⋈ (Γ ⋈ Φ) ⋈ Ψ) τ) :
    Subst.act (Γ := S) (liftPrefixed σ Φ) Ψ e =
      Subst.act (Γ := S) σ (Φ ⋈ Ψ) e := by
  let κ : Subst (Γ ⋈ Φ) (S ⋈ Γ ⋈ Φ) :=
    fun ⦃Λ⦄ ⦃υ⦄ x => Expr.η
      (cast (congrArg (fun Ω => Ω ∋[υ] Λ) (mul_assoc S Γ Φ).symm)
        (C.inr x))
  have h := act_interchange.subst (Γ := S) (Θ := 1) (Ω := Δ)
    (Φ := Φ) (Χ := Ψ) σ κ e
  have hκ : ∀ {Λ : C.Arity} {υ : C.Ty} (x : Γ ⋈ Φ ∋[υ] Λ),
      κ x = Expr.η (C.inr x) := by
    intro Λ υ x
    rcases C.cover Γ Φ x with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · unfold κ
      have hProof :
          congrArg (fun Ω => Ω ∋[υ] Λ) (mul_assoc S Γ Φ).symm =
            Eq.refl _ := Subsingleton.elim _ _
      rw [hProof]
      congr 1
    · unfold κ
      have hProof :
          congrArg (fun Ω => Ω ∋[υ] Λ) (mul_assoc S Γ Φ).symm =
            Eq.refl _ := Subsingleton.elim _ _
      rw [hProof]
      congr 1
  have hIdentity := act_idOfη (Γ := S) κ hκ Ψ e
  unfold liftPrefixed
  unfold κ at h
  exact h.symm.trans (congrArg (Subst.act σ (Φ ⋈ Ψ)) hIdentity)

/-- Acting by a lifted substitution is action below its fixed suffix. -/
theorem act_lift {Γ Δ : C.Arity} (σ : Subst Γ Δ) (Φ Ψ : C.Arity)
    {τ : C.Ty} (e : Expr (Γ ⋈ Φ ⋈ Ψ) τ) :
    cast (congrArg (fun Ω => Expr Ω τ) (mul_assoc Δ Φ Ψ))
        (Subst.act (Γ := 1) (Ξ := Δ ⋈ Φ) (lift σ Φ) Ψ e) =
      Subst.act (Γ := 1) σ (Φ ⋈ Ψ) e := by
  convert (act_interchange.subst (Γ := 1) (Θ := 1) (Φ := Φ)
    σ (Subst.id (Γ ⋈ Φ)) e).symm using 1
  · congr 1
    exact (act_id (Γ ⋈ Φ) Ψ e).symm

/-- Lifting the identity substitution is the identity on the extended base. -/
theorem lift_id (Γ Φ : C.Arity) :
    lift (Subst.id Γ) Φ = Subst.id (Γ ⋈ Φ) := by
  funext Λ τ x
  unfold lift pushforward Subst.id
  apply act_id

/-- The value of a lifted substitution is the original substitution acting
on the eta-expansion of the extended slot. -/
theorem lift_apply {Γ Δ : C.Arity} (σ : Subst Γ Δ) (Φ : C.Arity)
    {Λ : C.Arity} {τ : C.Ty} (x : Γ ⋈ Φ ∋[τ] Λ) :
    cast (congrArg (fun Ω => Expr Ω τ) (mul_assoc Δ Φ Λ)) (lift σ Φ x) =
      Subst.act (Γ := 1) σ (Φ ⋈ Λ)
        (Expr.η x : Expr (Γ ⋈ Φ ⋈ Λ) τ) := by
  rw [← act_η (lift σ Φ) Λ x]
  apply act_lift

/-- Extending by the empty suffix does not change a substitution. -/
theorem lift_one {Γ Δ : C.Arity} (σ : Subst Γ Δ) :
    lift σ 1 = σ := by
  funext α τ x
  have h := lift_apply σ 1 x
  simp only [cast_mul_assoc] at h
  exact h.trans (act_η σ α x)

/-- Successive fixed-suffix extensions agree with extension by their product. -/
theorem lift_assoc {Γ Δ : C.Arity} (σ : Subst Γ Δ) (Φ Ψ : C.Arity) :
    lift σ (Φ ⋈ Ψ) = lift (lift σ Φ) Ψ := by
  funext α τ x
  let e : Expr ((Γ ⋈ Φ) ⋈ (Ψ ⋈ α)) τ :=
    cast (congrArg (fun Ω => Expr Ω τ) (mul_assoc (Γ ⋈ Φ) Ψ α))
      (Expr.η x : Expr (((Γ ⋈ Φ) ⋈ Ψ) ⋈ α) τ)
  have hd := lift_apply σ (Φ ⋈ Ψ) x
  have ho := lift_apply (lift σ Φ) Ψ x
  have ha := act_lift σ Φ (Ψ ⋈ α) e
  simp only [cast_mul_assoc] at hd ho ha
  simp only [e, cast_mul_assoc] at ha
  exact hd.symm.trans (ha.symm.trans ho)

/-- Lifting preserves Kleisli composition. -/
theorem lift_comp {Γ Δ Ξ : C.Arity} (σ : Subst Γ Δ)
    (θ : Subst Δ Ξ) (Φ : C.Arity) :
    lift (Subst.comp (Γ := 1) (Ξ := Ξ) σ θ) Φ =
      Subst.comp (Γ := 1) (Θ := Δ ⋈ Φ) (Ξ := Ξ ⋈ Φ)
        (lift σ Φ) (lift θ Φ) := by
  funext Λ τ x
  apply (Equiv.cast
    (congrArg (fun Ω => Expr Ω τ) (mul_assoc Ξ Φ Λ))).injective
  simp only [Equiv.cast_apply]
  have hleft := lift_apply
    (Subst.comp (Γ := 1) (Ξ := Ξ) σ θ : Subst Γ Ξ) Φ x
  apply Eq.trans hleft
  unfold Subst.comp
  rw [act_lift]
  trans Subst.act θ (Φ ⋈ Λ)
    (Subst.act σ (Φ ⋈ Λ) (Expr.η x : Expr (Γ ⋈ Φ ⋈ Λ) τ))
  · apply act_comp
  · apply congrArg (fun e : Expr (Δ ⋈ (Φ ⋈ Λ)) τ =>
      Subst.act (Γ := 1) θ (Φ ⋈ Λ) e)
    exact (lift_apply σ Φ x).symm

end Subst
