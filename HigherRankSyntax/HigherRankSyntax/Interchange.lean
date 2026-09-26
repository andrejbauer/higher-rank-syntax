import HigherRankSyntax.Dispatch
import Batteries.Tactic.Trans
import Mathlib.Order.GameAdd
import Mathlib.Tactic.Convert

/-!
# Interchange of substitutions

* `act_interchange.aux`: acting by `κ` and then by `σ` equals acting by `σ` and
  then by `pushforward σ κ`.
* `act_interchange`: `θ.act Ω (κ.act 1 e) = (pushforward θ κ).act 1 (θ.act Ψ e)`.
-/

/-- The substitution sending each slot `x : Θ ∋ β` to `σ` acting at depth `Ω ⋈ β`
on `κ x`. -/
abbrev pushforward
    {Γ Δ Ξ Θ Ω : C.Arity}
    (σ : Subst Δ (Γ ⋈ Ξ)) (κ : Subst Θ (Γ ⋈ Δ ⋈ Ω)) :
  Subst Θ (Γ ⋈ Ξ ⋈ Ω) :=
    fun {β} x => σ.act (Ω ⋈ β) (κ x)

/-- `σ` acting at depth `Λ ⋈ Φ ⋈ Ρ` keeps a head `C.inl (C.inr z)` with
`z : Φ ∋ α` and acts on the arguments. -/
theorem act_ap_depth
    {Γ Δ Ξ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ)) (Λ Φ Ρ : C.Arity)
    {α : C.Arity} (z : Φ ∋ α)
    (args : Expr.Args (Γ ⋈ Δ ⋈ Λ ⋈ Φ ⋈ Ρ) α) :
  σ.act (Λ ⋈ Φ ⋈ Ρ) (Expr.ap (C.inl (Δ := Ρ) (C.inr (Γ := Γ ⋈ Δ ⋈ Λ) z)) args)
    = Expr.ap (C.inl (C.inr (Γ := Γ ⋈ Ξ ⋈ Λ) z))
        (fun {Ω} j => σ.act (Λ ⋈ Φ ⋈ Ρ ⋈ Ω) (args j))
  := by
  have head : ∀ Θ : C.Arity,
      (C.inl (C.inr z) : Θ ⋈ Λ ⋈ Φ ⋈ Ρ ∋ α) = C.inr (Γ := Θ) (C.inl (C.inr z)) := by
    intro Θ
    rw [← C.inr_inr]
    symm
    apply C.inr_inl
  rw [head, head]
  apply act_right

/-- `σ` acting at depth `Θ ⋈ Ρ ⋈ Φ` keeps a head `(((C.inl ⇑ʳ Θ) ⇑ʳ Ρ) ⇑ʳ Φ) p`
with `p : Γ ⋈ Θ ⋈ Ρ ⋈ Φ ∋ β` and acts on the arguments. -/
theorem act_renamed_head
    {Γ Δ Ξ Θ Ρ Φ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ)) {β : C.Arity}
    (p : Γ ⋈ Θ ⋈ Ρ ⋈ Φ ∋ β) (args : Expr.Args (Γ ⋈ Δ ⋈ Θ ⋈ Ρ ⋈ Φ) β) :
  σ.act (Θ ⋈ Ρ ⋈ Φ)
      (.ap (((((fun {_} x => C.inl x : Γ →ʳ Γ ⋈ Δ) ⇑ʳ Θ) ⇑ʳ Ρ) ⇑ʳ Φ) p) args)
    = .ap (((((fun {_} x => C.inl x : Γ →ʳ Γ ⋈ Ξ) ⇑ʳ Θ) ⇑ʳ Ρ) ⇑ʳ Φ) p)
        (fun {_} j => σ.act (Θ ⋈ Ρ ⋈ Φ ⋈ _) (args j))
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

/-- Acting by `κ` at depth `Χ` and then by `θ`, which substitutes the `Ψ`-slots of
the fillers of `κ`, equals acting by `pushforward θ κ` at depth `Χ`. -/
theorem act_interchange.subst
    {Γ Λ Θ Ψ Ω Φ Χ : C.Arity} (θ : Subst Ψ (Γ ⋈ Θ ⋈ Ω))
    (κ : Subst Λ (Γ ⋈ Θ ⋈ Ψ ⋈ Φ)) (e : Expr (Γ ⋈ Λ ⋈ Χ)) :
  θ.act (Φ ⋈ Χ) (Subst.act (Ξ := Θ ⋈ Ψ ⋈ Φ) κ Χ e)
    = Subst.act (Ξ := Θ ⋈ Ω ⋈ Φ) (pushforward (Ω := Φ) θ κ) Χ e
  := by
  match e with
  | .ap (α := β) x args =>
    let actedArgs : Expr.Args (Γ ⋈ Θ ⋈ Ψ ⋈ (Φ ⋈ Χ)) β :=
      fun {Ξ} i => Subst.act (Ξ := Θ ⋈ Ψ ⋈ Φ) κ (Χ ⋈ Ξ) (args i)
    head_cases x with z
    case right =>
      rw [act_right]
      trans
      · convert act_right θ (Φ ⋈ Χ) (C.inr z) actedArgs using 2
        congr 1
        symm
        apply C.inr_inr (Γ ⋈ Θ ⋈ Ψ) Φ Χ
      · rw [act_right]
        congr 1
        · apply C.inr_inr (Γ ⋈ Θ ⋈ Ω) Φ Χ
        · funext Ξ i
          exact act_interchange.subst (Χ := Χ ⋈ Ξ) θ κ (args i)
    case middle =>
      rw [act_middle]
      convert act_interchange.aux θ actedArgs 1 (κ z) using 2
      rw [act_middle]
      congr 1
      funext Ξ i
      symm
      exact act_interchange.subst (Χ := Χ ⋈ Ξ) θ κ (args i)
    case left =>
      rw [act_left]
      convert act_left θ (Φ ⋈ Χ) (C.inl z) actedArgs using 2
      · congr 1
        rw [C.inl_inl Γ (Θ ⋈ Ψ) Φ z, C.inl_inl Γ Θ Ψ z]
        symm
        apply C.inl_inl
      · rw [act_left]
        congr 1
        · rw [C.inl_inl Γ (Θ ⋈ Ω) Φ z, C.inl_inl Γ Θ Ω z]
          symm
          apply C.inl_inl
        · funext Ξ i
          symm
          exact act_interchange.subst (Χ := Χ ⋈ Ξ) θ κ (args i)
termination_by (s(Ψ, Λ), (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ))
decreasing_by
  · exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)
  · exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)
  · exact Prod.Lex.left _ _ (Sym2.GameAdd.snd ⟨z⟩)
  · exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)

/-- Acting by `κ` at depth `Φ` and then by `σ` equals acting by `σ` and then by
`pushforward σ κ` at depth `Φ`. -/
theorem act_interchange.aux
    {Γ Δ Ξ Θ Ψ Ω : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ))
    (κ : Subst Ψ (Γ ⋈ Δ ⋈ Θ ⋈ Ω)) (Φ : C.Arity)
    (e : Expr (Γ ⋈ Δ ⋈ Θ ⋈ Ψ ⋈ Φ)) :
  σ.act (Θ ⋈ Ω ⋈ Φ) (κ.act Φ e)
    = Subst.act (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω)
        (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ (σ.act (Θ ⋈ Ψ ⋈ Φ) e)
  := by
  match e with
  | .ap (α := β) x args =>
    let instantiatedArgs : Expr.Args (Γ ⋈ Δ ⋈ Θ ⋈ Ω ⋈ Φ) β :=
      fun {Λ} i => κ.act (Φ ⋈ Λ) (args i)
    head_cases x with z
    case right =>
      have headΩ := act_renamed_head σ (C.inr z) instantiatedArgs
      have headΨ := act_renamed_head σ (C.inr z) args
      simp only [Renaming.extend_inr] at headΩ headΨ
      rw [act_right]
      apply Eq.trans headΩ
      symm
      trans Subst.act (Ξ := Ω) (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ
          (.ap (C.inr z) (fun {_} j => σ.act (Θ ⋈ Ψ ⋈ Φ ⋈ _) (args j)))
      · apply congrArg _ headΨ
      · rw [act_right]
        congr 1
        funext Λ i
        symm
        exact act_interchange.aux σ κ (Φ ⋈ Λ) (args i)
    case middle =>
      rw [act_middle]
      convert act_interchange.aux (Θ := Θ ⋈ Ω) σ instantiatedArgs 1 (κ z) using 2
      trans Subst.act (Ξ := Ω) (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ
          (.ap (C.inl (C.inr z)) (fun {_} j => σ.act (Θ ⋈ Ψ ⋈ Φ ⋈ _) (args j)))
      · apply congrArg
        apply act_ap_depth
      · rw [act_middle]
        congr 1
        funext Λ i
        symm
        exact act_interchange.aux σ κ (Φ ⋈ Λ) (args i)
    case left =>
      head_cases z with w
      case right =>
        have headΩ := act_renamed_head σ (C.inl (C.inl (C.inr w))) instantiatedArgs
        have headΨ := act_renamed_head σ (C.inl (C.inl (C.inr w))) args
        simp only [Renaming.extend_inl, Renaming.extend_inr] at headΩ headΨ
        rw [act_left]
        apply Eq.trans headΩ
        symm
        trans Subst.act (Ξ := Ω) (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ
            (.ap (C.inl (C.inl (C.inr w))) (fun {_} j => σ.act (Θ ⋈ Ψ ⋈ Φ ⋈ _) (args j)))
        · apply congrArg _ headΨ
        · rw [act_left (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω) (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ (C.inr w)]
          congr 1
          funext Λ i
          symm
          exact act_interchange.aux σ κ (Φ ⋈ Λ) (args i)
      case middle =>
        rw [act_left]
        let shiftedArgs : Subst β ((Γ ⋈ Ξ) ⋈ (Θ ⋈ Ψ ⋈ Φ)) :=
          fun {Λ} i => σ.act (Θ ⋈ Ψ ⋈ Φ ⋈ Λ) (args i)
        trans σ.act (Θ ⋈ Ω ⋈ Φ) (.ap (C.inl (C.inr w)) instantiatedArgs)
        · congr 2
          rw [← C.inl_inl, ← C.inl_inl]
          rfl
        · rw [act_middle]
          symm
          trans Subst.act (Ξ := Ω) (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ (shiftedArgs.act 1 (σ w))
          · apply congrArg
            trans σ.act (Θ ⋈ Ψ ⋈ Φ) (.ap (C.inl (C.inr w)) args)
            · congr 2
              rw [← C.inl_inl, ← C.inl_inl]
              rfl
            · apply act_middle
          · convert act_interchange.subst (Γ := Γ ⋈ Ξ) (Θ := Θ) (Ω := Ω) (Φ := Φ) (Χ := 1)
              (pushforward (Ω := Θ ⋈ Ω) σ κ) shiftedArgs (σ w) using 2
            congr 1
            funext Λ i
            exact act_interchange.aux σ κ (Φ ⋈ Λ) (args i)
      case left =>
        have headΩ := act_renamed_head σ (C.inl (C.inl (C.inl w))) instantiatedArgs
        have headΨ := act_renamed_head σ (C.inl (C.inl (C.inl w))) args
        simp only [Renaming.extend_inl] at headΩ headΨ
        rw [act_left]
        apply Eq.trans headΩ
        symm
        trans Subst.act (Ξ := Ω) (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ
            (.ap (C.inl (C.inl (C.inl (C.inl w)))) (fun {_} j => σ.act (Θ ⋈ Ψ ⋈ Φ ⋈ _) (args j)))
        · apply congrArg _ headΨ
        · rw [act_left (Ξ := Ω) (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ (C.inl (C.inl w))]
          congr 1
          funext Λ i
          symm
          exact act_interchange.aux σ κ (Φ ⋈ Λ) (args i)
termination_by (s(Δ, Ψ), (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ))
decreasing_by
  · exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)
  · exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)
  · exact Prod.Lex.left _ _ (Sym2.GameAdd.snd ⟨z⟩)
  · exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)
  · exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)
  · exact Prod.Lex.left _ _ (Sym2.GameAdd.snd_fst ⟨w⟩)
  · exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)

end

end

/-- Acting by `κ` at depth `1` and then by `θ` equals acting by `θ` and then by
`pushforward θ κ` at depth `1`. -/
theorem act_interchange
    {Γ Θ Ξ Ψ Ω : C.Arity} (θ : Subst Θ (Γ ⋈ Ξ))
    (κ : Subst Ψ (Γ ⋈ Θ ⋈ Ω)) (e : Expr (Γ ⋈ Θ ⋈ Ψ)) :
  θ.act Ω (κ.act 1 e) = Subst.act (pushforward θ κ) 1 (θ.act Ψ e)
  := by
  apply act_interchange.aux (Θ := 1) _ _ 1
