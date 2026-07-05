import HigherRankSyntax.Dispatch
import Batteries.Tactic.Trans
import Mathlib.Order.GameAdd
import Mathlib.Tactic.Convert

universe u

/-!
# The substitution commuting square

`act_interchange.aux` is the general square: acting by `σ` commutes with
instantiating `κ` (pushed forward along `σ`).  `act_interchange` is its
`Θ = 1`, `Φ = 1` instance, used by `act_comp`.
-/

variable {A : Type} {C : Carrier A}

/-- Push `κ` forward along `σ`. -/
abbrev pushforward
    {Γ Δ Ξ Θ Ω : C.Arity}
    (σ : Subst Δ (Γ ⋈ Ξ)) (κ : Subst Θ (Γ ⋈ Δ ⋈ Ω)) :
  Subst Θ (Γ ⋈ Ξ ⋈ Ω) :=
    fun {β} {_} x => σ.act (Ω ⋈ β) (κ x)

/-- `σ.act` preserves a head from the `Φ` component of depth `Λ ⋈ Φ ⋈ Ρ`. -/
theorem act_ap_depth
    {Γ Δ Ξ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ)) (Λ Φ Ρ : C.Arity)
    {α : C.Arity} {τ : C.Ty} (z : Φ ∋[τ] α)
    (args : Expr.Args (Γ ⋈ Δ ⋈ Λ ⋈ Φ ⋈ Ρ) α) :
  σ.act (Λ ⋈ Φ ⋈ Ρ) (Expr.ap (C.inl (Δ := Ρ) (C.inr (Γ := Γ ⋈ Δ ⋈ Λ) z)) args)
    = Expr.ap (C.inl (C.inr (Γ := Γ ⋈ Ξ ⋈ Λ) z))
        (fun {Ω} {_} j => σ.act (Λ ⋈ Φ ⋈ Ρ ⋈ Ω) (args j))
  := by
  convert act_right σ (Λ ⋈ Φ ⋈ Ρ) (C.inl (Γ := Λ ⋈ Φ) (Δ := Ρ) (C.inr z)) args using 2
  · congr 1
    rw [← C.inr_inr]
    symm
    apply C.inr_inl
  · congr 1
    · rw [← C.inr_inr]
      symm
      apply C.inr_inl

/-- `σ.act` preserves heads obtained by extending a renaming from `Γ`. -/
theorem act_renamed_head
    {Γ Δ Ξ Θ Ρ Φ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ)) {β : C.Arity} {τ : C.Ty}
    (p : Γ ⋈ Θ ⋈ Ρ ⋈ Φ ∋[τ] β) (args : Expr.Args (Γ ⋈ Δ ⋈ Θ ⋈ Ρ ⋈ Φ) β) :
  σ.act (Θ ⋈ Ρ ⋈ Φ)
      (.ap (((((fun {_} {_} x => C.inl x : Γ →ʳ Γ ⋈ Δ) ⇑ʳ Θ) ⇑ʳ Ρ) ⇑ʳ Φ) p) args)
    = .ap (((((fun {_} {_} x => C.inl x : Γ →ʳ Γ ⋈ Ξ) ⇑ʳ Θ) ⇑ʳ Ρ) ⇑ʳ Φ) p)
        (fun {_} {_} j => σ.act (Θ ⋈ Ρ ⋈ Φ ⋈ _) (args j))
  := by
  head_cases p with z
  case right =>
    simp only [Renaming.extend_inr]
    convert act_right σ (Θ ⋈ Ρ ⋈ Φ) (C.inr z) args using 2
    · congr 1
      symm
      apply C.inr_inr (Γ ⋈ Δ) (Θ ⋈ Ρ) Φ z
    · symm
      apply C.inr_inr (Γ ⋈ Ξ) (Θ ⋈ Ρ) Φ z
  case middle =>
    simp only [Renaming.extend_inl, Renaming.extend_inr]
    apply act_ap_depth
  case left =>
    rcases C.cover Γ Θ z with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · simp only [Renaming.extend_inl]
      convert act_left σ (Θ ⋈ Ρ ⋈ Φ) w args using 2
      · congr 1
        rw [C.inl_inl, C.inl_inl]
        rfl
      · rw [C.inl_inl, C.inl_inl]
        rfl
    · simp only [Renaming.extend_inl, Renaming.extend_inr]
      convert act_ap_depth σ 1 Θ (Ρ ⋈ Φ) w args using 2
      · congr 1
        symm
        apply C.inl_inl (Γ ⋈ Δ ⋈ Θ) Ρ Φ
      · congr 1
        symm
        apply C.inl_inl (Γ ⋈ Ξ ⋈ Θ) Ρ Φ

section

local instance : WellFoundedRelation (Sym2 C.Arity) where
  rel := Sym2.GameAdd (@WellFoundedRelation.rel C.Arity inferInstance)
  wf := WellFounded.sym2_gameAdd (@WellFoundedRelation.wf C.Arity inferInstance)

mutual

/-- Acting by `θ` commutes with applying `κ` when `θ` acts on variables that may
occur in the fillers of `κ`. -/
theorem act_interchange.subst
    {Γ Λ Θ Ψ Ω Φ Χ : C.Arity} (θ : Subst Ψ (Γ ⋈ Θ ⋈ Ω))
    (κ : Subst Λ (Γ ⋈ Θ ⋈ Ψ ⋈ Φ)) {τ : C.Ty} (e : Expr (Γ ⋈ Λ ⋈ Χ) τ) :
  θ.act (Φ ⋈ Χ) (Subst.act (Ξ := Θ ⋈ Ψ ⋈ Φ) κ Χ e)
    = Subst.act (Ξ := Θ ⋈ Ω ⋈ Φ) (pushforward (Ω := Φ) θ κ) Χ e
  := by
  match e with
  | .ap (α := β) x args =>
    let actedArgs : Expr.Args (Γ ⋈ Θ ⋈ Ψ ⋈ (Φ ⋈ Χ)) β :=
      fun {Λ} {_} (i : _) => Subst.act (Ξ := Θ ⋈ Ψ ⋈ Φ) κ (Χ ⋈ Λ) (args i)
    head_cases x with z
    case right =>
      rw [act_right]
      trans
      · convert act_right θ (Φ ⋈ Χ) (C.inr z) actedArgs using 2
        · congr 1
          symm
          apply C.inr_inr (Γ ⋈ Θ ⋈ Ψ) Φ Χ
      · rw [act_right]
        congr 1
        · apply C.inr_inr (Γ ⋈ Θ ⋈ Ω) Φ Χ
        · funext Λ υ i
          dsimp [actedArgs]
          convert act_interchange.subst (Χ := Χ ⋈ Λ) θ κ (args i) using 2
    case middle =>
      rw [act_middle]
      convert act_interchange.aux θ actedArgs 1 (κ z) using 2
      · rw [act_middle]
        congr 1
        funext Λ υ i
        symm
        dsimp [actedArgs]
        convert act_interchange.subst (Χ := Χ ⋈ Λ) θ κ (args i) using 2
    case left =>
      rw [act_left]
      convert act_left θ (Φ ⋈ Χ) (C.inl z) actedArgs using 2
      · congr 1
        rw [C.inl_inl Γ (Θ ⋈ Ψ) Φ z]
        rw [C.inl_inl Γ Θ Ψ z]
        symm
        apply C.inl_inl
      · rw [act_left]
        congr 1
        · rw [C.inl_inl Γ (Θ ⋈ Ω) Φ z]
          rw [C.inl_inl Γ Θ Ω z]
          symm
          apply C.inl_inl
        · funext Ω' υ i
          symm
          dsimp [actedArgs]
          convert act_interchange.subst (Χ := Χ ⋈ Ω') θ κ (args i) using 2
termination_by (s(Ψ, Λ), (⟨_, _, e⟩ : Σ Γ : C.Arity, Σ τ : C.Ty, Expr Γ τ))
decreasing_by
  all_goals
    first
    | apply Prod.Lex.right
      exact Expr.Subterm.of_arg x args _
    | apply Prod.Lex.left
      apply Sym2.GameAdd.snd
      exact ⟨_, ⟨z⟩⟩

/-- Acting by `σ` commutes with instantiating `κ` (pushed forward along `σ`). -/
theorem act_interchange.aux
    {Γ Δ Ξ Θ Ψ Ω : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ))
    (κ : Subst Ψ (Γ ⋈ Δ ⋈ Θ ⋈ Ω)) (Φ : C.Arity)
    {τ : C.Ty} (e : Expr (Γ ⋈ Δ ⋈ Θ ⋈ Ψ ⋈ Φ) τ) :
  σ.act (Θ ⋈ Ω ⋈ Φ) (κ.act Φ e)
    = Subst.act (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω)
        (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ (σ.act (Θ ⋈ Ψ ⋈ Φ) e)
  := by
  match e with
  | .ap (α := β) x args =>
    let instantiatedArgs : Expr.Args (Γ ⋈ Δ ⋈ Θ ⋈ Ω ⋈ Φ) β :=
      fun {Λ} {_} i => κ.act (Φ ⋈ Λ) (args i)
    head_cases x with z
    case right =>
      rw [act_right]
      have headΩ := act_renamed_head σ (C.inr z)
        (fun {Λ} {_} i => κ.act (Φ ⋈ Λ) (args i))
      simp only [Renaming.extend_inr] at headΩ
      apply Eq.trans headΩ
      symm
      trans Subst.act (Ξ := Ω)
          (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ
          (.ap (C.inr z) (fun {_} {_} j => σ.act (Θ ⋈ Ψ ⋈ Φ ⋈ _) (args j)))
      · congr 1
        have headΨ := act_renamed_head σ (C.inr z) args
        simp only [Renaming.extend_inr] at headΨ
        apply headΨ
      · rw [act_right]
        congr 1
        funext Λ υ i
        simpa using (act_interchange.aux σ κ (Φ ⋈ Λ) (args i)).symm
    case middle =>
      rw [act_middle]
      convert act_interchange.aux (Θ := Θ ⋈ Ω) σ instantiatedArgs 1 (κ z) using 2
      · let shiftedArgs : Expr.Args (Γ ⋈ Ξ ⋈ Θ ⋈ Ψ ⋈ Φ) β :=
          fun {Λ} {_} i => σ.act (Θ ⋈ Ψ ⋈ Φ ⋈ Λ) (args i)
        trans Subst.act (Ξ := Ω)
          (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ
          (.ap (C.inl (C.inr z)) shiftedArgs)
        · apply congrArg
          convert act_ap_depth σ Θ Ψ Φ z args using 2
        · rw [act_middle]
          congr 1
          funext Λ υ i
          dsimp [shiftedArgs, instantiatedArgs, pushforward]
          simpa using (act_interchange.aux σ κ (Φ ⋈ Λ) (args i)).symm
    case left =>
      head_cases z with w
      case right =>
        rw [act_left]
        have headΩ := act_renamed_head σ (C.inl (C.inl (C.inr w)))
          (fun {Λ} {_} i => κ.act (Φ ⋈ Λ) (args i))
        simp only [Renaming.extend_inl, Renaming.extend_inr] at headΩ
        apply Eq.trans headΩ
        symm
        trans Subst.act (Ξ := Ω)
            (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ
            (.ap (C.inl (C.inl (C.inr w)))
              (fun {_} {_} j => σ.act (Θ ⋈ Ψ ⋈ Φ ⋈ _) (args j)))
        · congr 1
          have headΨ := act_renamed_head σ (C.inl (C.inl (C.inr w))) args
          simp only [Renaming.extend_inl, Renaming.extend_inr] at headΨ
          apply headΨ
        · rw [act_left (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω)
              (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ (C.inr w)]
          congr 1
          funext Λ υ i
          simpa using (act_interchange.aux σ κ (Φ ⋈ Λ) (args i)).symm
      case middle =>
        rw [act_left]
        let shiftedArgs : Subst β ((Γ ⋈ Ξ) ⋈ (Θ ⋈ Ψ ⋈ Φ)) :=
          fun {Λ} {_} i => σ.act (Θ ⋈ Ψ ⋈ Φ ⋈ Λ) (args i)
        trans σ.act (Θ ⋈ Ω ⋈ Φ) (.ap (C.inl (C.inr w)) instantiatedArgs)
        · congr 2
          simp only [← C.inl_inl]
          exact (C.inl_inl (Γ ⋈ Δ) (Θ ⋈ Ω) Φ (C.inr w)).symm
        · rw [act_middle]
          symm
          trans Subst.act (Ξ := Ω)
              (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ
              (shiftedArgs.act 1 (σ w))
          · apply congrArg
            trans σ.act (Θ ⋈ Ψ ⋈ Φ) (.ap (C.inl (C.inr w)) args)
            · congr 2
              simp only [← C.inl_inl]
              exact (C.inl_inl (Γ ⋈ Δ) (Θ ⋈ Ψ) Φ (C.inr w)).symm
            · apply act_middle
          · convert act_interchange.subst (Γ := Γ ⋈ Ξ) (Λ := β)
              (Θ := Θ) (Ψ := Ψ) (Ω := Ω) (Φ := Φ) (Χ := 1)
              (pushforward (Ω := Θ ⋈ Ω) σ κ) shiftedArgs (σ w) using 2
            · congr 1
              funext Λ υ i
              dsimp [shiftedArgs, instantiatedArgs, pushforward]
              simpa using act_interchange.aux σ κ (Φ ⋈ Λ) (args i)
      case left =>
        rw [act_left]
        have headΩ := act_renamed_head σ (C.inl (C.inl (C.inl w)))
          (fun {Λ} {_} i => κ.act (Φ ⋈ Λ) (args i))
        simp only [Renaming.extend_inl] at headΩ
        apply Eq.trans headΩ
        symm
        trans Subst.act (Ξ := Ω)
            (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ
            (.ap (C.inl (C.inl (C.inl (C.inl w))))
              (fun {_} {_} j => σ.act (Θ ⋈ Ψ ⋈ Φ ⋈ _) (args j)))
        · congr 1
          have headΨ := act_renamed_head σ (C.inl (C.inl (C.inl w))) args
          simp only [Renaming.extend_inl] at headΨ
          apply headΨ
        · rw [act_left (Ξ := Ω) (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ (C.inl (C.inl w))]
          congr 1
          funext Λ υ i
          simpa using (act_interchange.aux σ κ (Φ ⋈ Λ) (args i)).symm
termination_by (s(Δ, Ψ), (⟨_, _, e⟩ : Σ Γ : C.Arity, Σ τ : C.Ty, Expr Γ τ))
decreasing_by
  all_goals
    first
    | apply Prod.Lex.right
      exact Expr.Subterm.of_arg x args _
    | apply Prod.Lex.left
      apply Sym2.GameAdd.snd
      exact ⟨_, ⟨z⟩⟩
    | apply Prod.Lex.left
      apply Sym2.GameAdd.snd_fst
      exact ⟨_, ⟨w⟩⟩

end

end


/-- Acting by `θ` commutes with instantiating `κ`: substituting `κ` then acting
by `θ` equals acting by `θ` then substituting the pushed-forward `κ`. -/
theorem act_interchange
    {Γ Θ Ξ Ψ Ω : C.Arity} (θ : Subst Θ (Γ ⋈ Ξ))
    (κ : Subst Ψ (Γ ⋈ Θ ⋈ Ω)) {τ : C.Ty} (e : Expr (Γ ⋈ Θ ⋈ Ψ) τ) :
  θ.act Ω (κ.act 1 e) = Subst.act (pushforward θ κ) 1 (θ.act Ψ e)
  := by
  apply act_interchange.aux (Θ := 1) _ _ 1
