import HigherRankSyntax.Instantiation
import HigherRankSyntax.Interchange
import Batteries.Tactic.Trans

/-!
# The three relative-monad laws for `Subst.act`

* `act_id` — the identity substitution acts as the identity (unit_right).
* `act_η` — acting on an η-expansion applies the substitution (unit_left).
* `act_comp` — action by a composite factors (comp_lift).
-/

/-- **`act_id`** — the identity substitution acts as the identity (unit_right). -/
theorem act_id (Γ Φ : C.Arity) (e : Expr (Γ ⋈ Φ)) :
  Subst.act (Subst.id Γ) (Γ := 1) Φ e = e
  := act_idOfη (Γ := 1) (Subst.id Γ)
       (fun z => by rw [C.unit_left Γ z]; rfl) Φ e

/-- **`act_η`** — acting on an η-expansion reduces to applying `σ` (unit_left). -/
theorem act_η
    {Δ Ξ : C.Arity}
    (σ : Subst Δ Ξ) (Θ : C.Arity) (x : Δ ∋ Θ) :
  σ.act (Γ := 1) Θ (.η x) = σ x
  := by
  rw [Expr.η.eq_1]
  trans
  · convert act_middle (Γ := 1) σ Θ x (fun {_} i => Expr.η (C.inr i)) using 2
    · congr 1
      rw [C.unit_left Δ x]
  · calc
      _ = Subst.act (Subst.instId Ξ Θ) 1 (σ x) := by
            congr 1
            funext Ω i
            apply act_η_right
      _ = σ x := by apply act_inst_id

/-- An application is the substitution instance of an η-expansion by its own
arguments. -/
theorem ap_eq_act_η {Γ α : C.Arity} (x : Γ ∋ α) (args : Subst α Γ) :
  Expr.ap x args
    = Subst.act (Γ := Γ) (Δ := α) (Ξ := 1) args 1 ((Expr.η x : Expr (Γ ⋈ α)))
  := by
  rw [act_inst_η]
  congr 1
  exact (C.unit_right Γ x).symm

/-- Acting by `Subst.copair (Subst.id Γ) args` on an expression weakened by a
`Γ`-prefix is acting by `args`. -/
theorem act_copair_id {Γ α : C.Arity} (args : Subst α Γ) (Φ : C.Arity) :
    ∀ e : Expr (Γ ⋈ α ⋈ Φ),
      Subst.act (Γ := Γ) (Δ := Γ ⋈ α) (Ξ := 1)
          (Subst.copair (Subst.id Γ) args) Φ
          (⟦ (fun ⦃_⦄ y => C.inr y : (Γ ⋈ α) →ʳ Γ ⋈ (Γ ⋈ α)) ⇑ʳ Φ ⟧ʳ e)
        = Subst.act (Γ := Γ) (Δ := α) (Ξ := 1) args Φ e
  | .ap (α := β) x args' => by
    head_cases x with z
    case right =>
      rw [Renaming.act_ap, Renaming.extend_inr, act_right, act_right]
      congr 1
      funext Ω i
      rw [← Renaming.extend_assoc]
      exact act_copair_id args (Φ ⋈ Ω) (args' i)
    case middle =>
      rw [Renaming.act_ap, Renaming.extend_inl, act_middle, act_middle,
        Subst.copair_inr]
      congr 1
      funext Ω i
      rw [← Renaming.extend_assoc]
      exact act_copair_id args (Φ ⋈ Ω) (args' i)
    case left =>
      rw [Renaming.act_ap, Renaming.extend_inl, act_middle, act_left,
        Subst.copair_inl, Subst.id]
      trans
      · apply act_inst_η
      · congr 1
        · rw [C.unit_right]
        · funext Ω i
          rw [← Renaming.extend_assoc]
          exact act_copair_id args (Φ ⋈ Ω) (args' i)
termination_by e => (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args' i

/-- Substituting the fresh block of a weakened expression by the slots it came
from returns the expression. -/
theorem act_instId_weaken (Γ α : C.Arity) :
    ∀ {Φ : C.Arity} (e : Expr (Γ ⋈ α ⋈ Φ)),
      Subst.act (Γ := Γ ⋈ α) (Δ := α) (Ξ := 1) (Subst.instId Γ α) Φ
          (⟦ (Renaming.inl Γ α ⇑ʳ α) ⇑ʳ Φ ⟧ʳ e) = e
  | Φ, .ap (α := β) x args => by
      head_cases x with z
      case right =>
        rw [Renaming.act_ap, Renaming.extend_inr, act_right]
        congr 1
        funext Ω i
        rw [← Renaming.extend_assoc]
        exact act_instId_weaken Γ α (Φ := Φ ⋈ Ω) (args i)
      case middle =>
        rw [Renaming.act_ap, Renaming.extend_inl, Renaming.extend_inr, act_middle,
          Subst.instId]
        trans
        · apply act_inst_η
        · congr 1
          funext Ω i
          rw [← Renaming.extend_assoc]
          exact act_instId_weaken Γ α (Φ := Φ ⋈ Ω) (args i)
      case left =>
        rw [Renaming.act_ap, Renaming.extend_inl, Renaming.extend_inl, act_left]
        congr 1
        · rw [C.unit_right]
          rfl
        · funext Ω i
          rw [← Renaming.extend_assoc]
          exact act_instId_weaken Γ α (Φ := Φ ⋈ Ω) (args i)
termination_by Φ e => (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args i

/-- Acting by the eta-substitution of a renaming is the renaming action. -/
theorem act_ofRenaming
    {Γ Δ Φ : C.Arity} (ρ : Γ →ʳ Δ) :
    ∀ e : Expr (Γ ⋈ Φ),
      Subst.act (Subst.ofRenaming ρ) (Γ := 1) Φ e =
        Renaming.act (ρ ⇑ʳ Φ) e
  | .ap (α := β) x args => by
      rcases C.cover Γ Φ x with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · have hz :
          (C.inl z : Γ ⋈ Φ ∋ β) =
            C.inl (C.inr z : 1 ⋈ Γ ∋ β) := by
            congr 1
            exact (C.unit_left Γ z).symm
        conv_lhs => rw [hz]
        rw [Renaming.act_ap]
        conv_lhs => unfold Subst.act
        simp only [Subst.threeway_middle]
        rw [Subst.ofRenaming, act_inst_η]
        congr 1
        · exact (Renaming.extend_inl ρ z).symm
        · funext Ω i
          rw [← Renaming.extend_assoc]
          exact act_ofRenaming (Φ := Φ ⋈ Ω) ρ (args i)
      · rw [Renaming.act_ap]
        trans .ap (C.inr z : Δ ⋈ Φ ∋ β)
          (fun {_} i =>
            Subst.act (Subst.ofRenaming ρ) (Γ := 1) (Φ ⋈ _) (args i))
        · convert act_right (Γ := 1) (Subst.ofRenaming ρ) Φ z args using 1
        · congr 1
          · exact (Renaming.extend_inr ρ z).symm
          · funext Ω i
            rw [← Renaming.extend_assoc]
            exact act_ofRenaming (Φ := Φ ⋈ Ω) ρ (args i)
termination_by e =>
  (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args i

/-- Eta-substitution below a fixed prefix is the corresponding prefixed
renaming action. -/
theorem act_ofRenaming_prefixed
    {S Γ Δ Φ : C.Arity} (ρ : Γ →ʳ Δ) :
    ∀ e : Expr (S ⋈ Γ ⋈ Φ),
      Subst.act (Γ := S)
          (fun ⦃_⦄ x => Expr.η (C.inr (ρ x))) Φ e =
        Renaming.act ((Renaming.prefixed S ρ) ⇑ʳ Φ) e
  | .ap x args => by
      head_cases x with z
      case right =>
        rw [act_right, Renaming.act_ap]
        congr 1
        · exact (Renaming.extend_inr (Renaming.prefixed S ρ) z).symm
        · funext Ω i
          rw [← Renaming.extend_assoc]
          exact act_ofRenaming_prefixed (S := S) (Φ := Φ ⋈ Ω) ρ (args i)
      case middle =>
        rw [act_middle, Renaming.act_ap]
        rw [Renaming.extend_inl, Renaming.prefixed_inr]
        rw [act_inst_η]
        congr 1
        funext Ω i
        rw [← Renaming.extend_assoc]
        exact act_ofRenaming_prefixed (S := S) (Φ := Φ ⋈ Ω) ρ (args i)
      case left =>
        rw [act_left, Renaming.act_ap]
        rw [Renaming.extend_inl, Renaming.prefixed_inl]
        congr 1
        funext Ω i
        rw [← Renaming.extend_assoc]
        exact act_ofRenaming_prefixed (S := S) (Φ := Φ ⋈ Ω) ρ (args i)
termination_by e =>
  (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args i

/-- Instantiating a block commutes with a renaming of the base, when the fillers
are renamed as well. -/
theorem act_rename (Γ Δ Θ : C.Arity) (ρ : Γ →ʳ Δ) (σ : Subst Θ Γ) (e : Expr (Γ ⋈ Θ)) :
    Subst.act (Γ := Δ) (Δ := Θ) (Ξ := 1)
        (fun ⦃Λ⦄ i => ⟦ ρ ⇑ʳ Λ ⟧ʳ (σ i)) 1 ((⟦ ρ ⇑ʳ Θ ⟧ʳ e : Expr (Δ ⋈ Θ)))
      = ⟦ ρ ⟧ʳ (Subst.act (Γ := Γ) (Δ := Θ) (Ξ := 1) σ 1 e) := by
  let θ : Subst Γ (1 ⋈ Δ) := Subst.ofRenaming ρ
  have key := act_interchange (Γ := 1) (Θ := Γ) (Ξ := Δ) (Ψ := Θ) (Ω := 1) θ σ e
  have hpush : (fun ⦃Λ⦄ (i : Θ ∋ Λ) => ⟦ ρ ⇑ʳ Λ ⟧ʳ (σ i))
      = pushforward (Γ := 1) (Ω := 1) θ σ := by
    funext Λ i
    exact (act_ofRenaming ρ (σ i)).symm
  have he : (⟦ ρ ⇑ʳ Θ ⟧ʳ e : Expr (Δ ⋈ Θ)) = θ.act Θ e :=
    (act_ofRenaming (Φ := Θ) ρ e).symm
  have hout : ⟦ ρ ⟧ʳ (Subst.act (Γ := Γ) (Δ := Θ) (Ξ := 1) σ 1 e)
      = θ.act 1 (Subst.act (Γ := Γ) (Δ := Θ) (Ξ := 1) σ 1 e) := by
    refine Eq.trans ?_ (act_ofRenaming (Φ := 1) ρ _).symm
    exact congrArg (fun κ => Renaming.act κ (Subst.act (Γ := Γ) (Δ := Θ) (Ξ := 1) σ 1 e))
      (Renaming.extend_unit ρ).symm
  rw [he]
  refine Eq.trans ?_ hout.symm
  refine Eq.trans ?_ key.symm
  exact congrArg (fun s => Subst.act (Γ := Δ) s 1 (θ.act Θ e)) hpush

/-- Instantiating a block under a suffix commutes with a renaming of the base. -/
theorem act_rename_suffix (Γ Δ Θ : C.Arity) (ρ : Γ →ʳ Δ) (σ : Subst Θ Γ) (Φ : C.Arity)
    (e : Expr (Γ ⋈ Θ ⋈ Φ)) :
    Subst.act (Γ := Δ) (Δ := Θ) (Ξ := 1)
        (fun ⦃Λ⦄ i => ⟦ ρ ⇑ʳ Λ ⟧ʳ (σ i)) Φ ((⟦ (ρ ⇑ʳ Θ) ⇑ʳ Φ ⟧ʳ e : Expr (Δ ⋈ Θ ⋈ Φ)))
      = ⟦ ρ ⇑ʳ Φ ⟧ʳ (Subst.act (Γ := Γ) (Δ := Θ) (Ξ := 1) σ Φ e) := by
  let θ : Subst Γ (1 ⋈ Δ) := Subst.ofRenaming ρ
  have key := act_interchange.aux (Γ := 1) (Δ := Γ) (Ξ := Δ) (Θ := 1) (Ω := 1) (Ψ := Θ)
    θ σ Φ e
  have hpush : (fun ⦃Λ⦄ (i : Θ ∋ Λ) => ⟦ ρ ⇑ʳ Λ ⟧ʳ (σ i))
      = pushforward (Γ := 1) (Ω := 1) θ σ := by
    funext Λ i
    exact (act_ofRenaming ρ (σ i)).symm
  have he : (⟦ (ρ ⇑ʳ Θ) ⇑ʳ Φ ⟧ʳ e : Expr (Δ ⋈ Θ ⋈ Φ)) = θ.act (Θ ⋈ Φ) e := by
    refine Eq.trans ?_ (act_ofRenaming (Φ := Θ ⋈ Φ) ρ e).symm
    exact congrArg (fun κ => Renaming.act κ e) (Renaming.extend_assoc ρ Θ Φ).symm
  have hout : ⟦ ρ ⇑ʳ Φ ⟧ʳ (Subst.act (Γ := Γ) (Δ := Θ) (Ξ := 1) σ Φ e)
      = θ.act Φ (Subst.act (Γ := Γ) (Δ := Θ) (Ξ := 1) σ Φ e) :=
    (act_ofRenaming (Φ := Φ) ρ _).symm
  rw [he]
  refine Eq.trans ?_ hout.symm
  refine Eq.trans ?_ key.symm
  exact congrArg (fun s => Subst.act (Γ := Δ) s Φ (θ.act (Θ ⋈ Φ) e)) hpush

/-- **`act_comp`** — action by a composite factors (comp_lift). -/
theorem act_comp
    {Γ Δ Θ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Θ)) (θ : Subst Θ (Γ ⋈ Ξ))
    (Φ : C.Arity) (e : Expr (Γ ⋈ Δ ⋈ Φ)) :
  Subst.act (Subst.comp σ θ) Φ e = θ.act Φ (σ.act Φ e)
  := by
  match e with
  | .ap (α := β) x args =>
    head_cases x with z
    case right =>
      rw [act_right, act_right, act_right]
      congr 1
      funext Ω i
      apply act_comp σ θ (Φ ⋈ Ω) (args i)
    case middle =>
      rw [act_middle, act_middle, act_interchange]
      congr 1
      funext Ω i
      apply act_comp σ θ (Φ ⋈ Ω) (args i)
    case left =>
      rw [act_left, act_left, act_left]
      congr 1
      funext Ω i
      apply act_comp σ θ (Φ ⋈ Ω) (args i)
termination_by (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args _

/-- Renaming an η-expansion renames the slot. -/
theorem Renaming.act_eta : ∀ {Γ Δ α : C.Arity} (ρ : Γ →ʳ Δ) (x : Γ ∋ α),
    (⟦ ρ ⇑ʳ α ⟧ʳ (Expr.η x) : Expr (Δ ⋈ α)) = Expr.η (ρ x)
  | _, _, α, ρ, x => by
      rw [Expr.η.eq_1, Renaming.act_ap, Expr.η.eq_1]
      refine congrArg₂ Expr.ap (Renaming.extend_inl ρ x) ?_
      funext Ω i
      exact (Renaming.act_eta (ρ ⇑ʳ α) (C.inr i)).trans
        (congrArg Expr.η (Renaming.extend_inr ρ i))
termination_by Γ Δ α _ _ => α
decreasing_by exact ⟨i⟩

/-- A square of substitutions and renamings, from associativity. -/
theorem act_square {Γ Γ' Δ Δ' : C.Arity} (ρ : Γ →ʳ Γ') (ρ' : Δ →ʳ Δ')
    (κ : Subst Γ' Δ') (κ' : Subst Γ Δ)
    (h : ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α), κ (ρ x) = ⟦ ρ' ⇑ʳ α ⟧ʳ (κ' x))
    (Φ : C.Arity) (e : Expr (Γ ⋈ Φ)) :
    Subst.act (Γ := 1) κ Φ (⟦ ρ ⇑ʳ Φ ⟧ʳ e) = ⟦ ρ' ⇑ʳ Φ ⟧ʳ (Subst.act (Γ := 1) κ' Φ e) := by
  have hl : Subst.act (Γ := 1) κ Φ (⟦ ρ ⇑ʳ Φ ⟧ʳ e)
      = Subst.act (Γ := 1) (Subst.comp (Subst.ofRenaming ρ) κ) Φ e := by
    refine Eq.trans (congrArg (Subst.act (Γ := 1) κ Φ)
      (act_ofRenaming (Φ := Φ) ρ e).symm) ?_
    exact (act_comp (Γ := 1) (Subst.ofRenaming ρ) κ Φ e).symm
  have hr : ⟦ ρ' ⇑ʳ Φ ⟧ʳ (Subst.act (Γ := 1) κ' Φ e)
      = Subst.act (Γ := 1) (Subst.comp κ' (Subst.ofRenaming ρ')) Φ e := by
    refine Eq.trans (act_ofRenaming (Φ := Φ) ρ' _).symm ?_
    exact (act_comp (Γ := 1) κ' (Subst.ofRenaming ρ') Φ e).symm
  refine hl.trans (Eq.trans ?_ hr.symm)
  refine congrArg (fun s => Subst.act (Γ := 1) s Φ e) ?_
  funext α x
  exact ((act_η κ α (ρ x)).trans (h x)).trans (act_ofRenaming (Φ := α) ρ' (κ' x)).symm

/-- Changing only the current-depth arity commutes with raw substitution. -/
theorem act_cast_suffix {Γ Δ Ξ Φ Ψ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Ξ)) (h : Φ = Ψ)
    (e : Expr (Γ ⋈ Δ ⋈ Φ)) :
    cast (congrArg (fun Λ => Expr (Γ ⋈ Ξ ⋈ Λ)) h)
      (Subst.act σ Φ e) =
      Subst.act σ Ψ
        (cast (congrArg (fun Λ => Expr (Γ ⋈ Δ ⋈ Λ)) h) e) := by
  subst Ψ
  rfl

namespace Subst

private theorem cast_mul_assoc (Γ Φ Ψ : C.Arity)
    (e : Expr ((Γ ⋈ Φ) ⋈ Ψ)) :
    cast (congrArg (fun Ω => Expr Ω) (mul_assoc Γ Φ Ψ)) e = e := by
  have hp : congrArg (fun Ω => Expr Ω) (mul_assoc Γ Φ Ψ) = rfl :=
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
    (fun ⦃Λ⦄ x => Expr.η
      (cast (congrArg (fun Ω => Ω ∋ Λ) (mul_assoc S Γ Φ).symm)
        (C.inr x)))

/-- Acting by a fixed-prefix lift is action below its fixed suffix. -/
theorem act_liftPrefixed {S Γ Δ Φ Ψ : C.Arity}
    (σ : Subst Γ (S ⋈ Δ))
    (e : Expr (S ⋈ (Γ ⋈ Φ) ⋈ Ψ)) :
    Subst.act (Γ := S) (liftPrefixed σ Φ) Ψ e =
      Subst.act (Γ := S) σ (Φ ⋈ Ψ) e := by
  let κ : Subst (Γ ⋈ Φ) (S ⋈ Γ ⋈ Φ) :=
    fun ⦃Λ⦄ x => Expr.η
      (cast (congrArg (fun Ω => Ω ∋ Λ) (mul_assoc S Γ Φ).symm)
        (C.inr x))
  have h := act_interchange.subst (Γ := S) (Θ := 1) (Ω := Δ)
    (Φ := Φ) (Χ := Ψ) σ κ e
  have hκ : ∀ {Λ : C.Arity} (x : Γ ⋈ Φ ∋ Λ),
      κ x = Expr.η (C.inr x) := by
    intro Λ x
    rcases C.cover Γ Φ x with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · unfold κ
      have hProof :
          congrArg (fun Ω => Ω ∋ Λ) (mul_assoc S Γ Φ).symm =
            Eq.refl _ := Subsingleton.elim _ _
      rw [hProof]
      congr 1
    · unfold κ
      have hProof :
          congrArg (fun Ω => Ω ∋ Λ) (mul_assoc S Γ Φ).symm =
            Eq.refl _ := Subsingleton.elim _ _
      rw [hProof]
      congr 1
  have hIdentity := act_idOfη (Γ := S) κ hκ Ψ e
  unfold liftPrefixed
  unfold κ at h
  exact h.symm.trans (congrArg (Subst.act σ (Φ ⋈ Ψ)) hIdentity)

/-- Acting by a lifted substitution is action below its fixed suffix. -/
theorem act_lift {Γ Δ : C.Arity} (σ : Subst Γ Δ) (Φ Ψ : C.Arity)
    (e : Expr (Γ ⋈ Φ ⋈ Ψ)) :
    cast (congrArg (fun Ω => Expr Ω) (mul_assoc Δ Φ Ψ))
        (Subst.act (Γ := 1) (Ξ := Δ ⋈ Φ) (lift σ Φ) Ψ e) =
      Subst.act (Γ := 1) σ (Φ ⋈ Ψ) e := by
  convert (act_interchange.subst (Γ := 1) (Θ := 1) (Φ := Φ)
    σ (Subst.id (Γ ⋈ Φ)) e).symm using 1
  · congr 1
    exact (act_id (Γ ⋈ Φ) Ψ e).symm

/-- Lifting the identity substitution is the identity on the extended base. -/
theorem lift_id (Γ Φ : C.Arity) :
    lift (Subst.id Γ) Φ = Subst.id (Γ ⋈ Φ) := by
  funext Λ x
  unfold lift pushforward Subst.id
  apply act_id

/-- The value of a lifted substitution is the original substitution acting
on the eta-expansion of the extended slot. -/
theorem lift_apply {Γ Δ : C.Arity} (σ : Subst Γ Δ) (Φ : C.Arity)
    {Λ : C.Arity} (x : Γ ⋈ Φ ∋ Λ) :
    cast (congrArg (fun Ω => Expr Ω) (mul_assoc Δ Φ Λ)) (lift σ Φ x) =
      Subst.act (Γ := 1) σ (Φ ⋈ Λ)
        (Expr.η x : Expr (Γ ⋈ Φ ⋈ Λ)) := by
  rw [← act_η (lift σ Φ) Λ x]
  apply act_lift

/-- Extending by the empty suffix does not change a substitution. -/
theorem lift_one {Γ Δ : C.Arity} (σ : Subst Γ Δ) :
    lift σ 1 = σ := by
  funext α x
  have h := lift_apply σ 1 x
  simp only [cast_mul_assoc] at h
  exact h.trans (act_η σ α x)

/-- Successive fixed-suffix extensions agree with extension by their product. -/
theorem lift_assoc {Γ Δ : C.Arity} (σ : Subst Γ Δ) (Φ Ψ : C.Arity) :
    lift σ (Φ ⋈ Ψ) = lift (lift σ Φ) Ψ := by
  funext α x
  let e : Expr ((Γ ⋈ Φ) ⋈ (Ψ ⋈ α)) :=
    cast (congrArg (fun Ω => Expr Ω) (mul_assoc (Γ ⋈ Φ) Ψ α))
      (Expr.η x : Expr (((Γ ⋈ Φ) ⋈ Ψ) ⋈ α))
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
  funext Λ x
  apply (Equiv.cast
    (congrArg (fun Ω => Expr Ω) (mul_assoc Ξ Φ Λ))).injective
  simp only [Equiv.cast_apply]
  have hleft := lift_apply
    (Subst.comp (Γ := 1) (Ξ := Ξ) σ θ : Subst Γ Ξ) Φ x
  apply Eq.trans hleft
  unfold Subst.comp
  rw [act_lift]
  trans Subst.act θ (Φ ⋈ Λ)
    (Subst.act σ (Φ ⋈ Λ) (Expr.η x : Expr (Γ ⋈ Φ ⋈ Λ)))
  · apply act_comp
  · apply congrArg (fun e : Expr (Δ ⋈ (Φ ⋈ Λ)) =>
      Subst.act (Γ := 1) θ (Φ ⋈ Λ) e)
    exact (lift_apply σ Φ x).symm

end Subst

/-- The square is preserved by lifting. -/
theorem lift_square {Γ Γ' Δ Δ' : C.Arity} (ρ : Γ →ʳ Γ') (ρ' : Δ →ʳ Δ')
    (κ : Subst Γ' Δ') (κ' : Subst Γ Δ)
    (h : ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α), κ (ρ x) = ⟦ ρ' ⇑ʳ α ⟧ʳ (κ' x)) (S : C.Arity) :
    ∀ ⦃γ : C.Arity⦄ (x : (Γ ⋈ S) ∋ γ),
      Subst.lift κ S ((ρ ⇑ʳ S) x) = ⟦ (ρ' ⇑ʳ S) ⇑ʳ γ ⟧ʳ (Subst.lift κ' S x) := by
  intro γ x
  refine Eq.trans (congrArg (Subst.act (Γ := 1) κ (S ⋈ γ))
    (Renaming.act_eta (ρ ⇑ʳ S) x).symm) ?_
  refine Eq.trans (congrArg (fun s => Subst.act (Γ := 1) κ (S ⋈ γ) (Renaming.act s (Expr.η x)))
    (Renaming.extend_assoc ρ S γ).symm) ?_
  refine Eq.trans (act_square ρ ρ' κ κ' h (S ⋈ γ) ((Expr.η x : Expr ((Γ ⋈ S) ⋈ γ)))) ?_
  exact congrArg (fun s => Renaming.act s (Subst.act (Γ := 1) κ' (S ⋈ γ) ((Expr.η x : Expr ((Γ ⋈ S) ⋈ γ)))))
    (Renaming.extend_assoc ρ' S γ)
