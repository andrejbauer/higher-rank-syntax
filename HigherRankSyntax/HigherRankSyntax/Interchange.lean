import HigherRankSyntax.Dispatch
import Mathlib.Order.GameAdd

/-!
# Interchange of substitutions

* `act_interchange.aux`: acting by `κ` and then by `σ` equals acting by `σ` and
  then by `pushforward σ κ`.
* `act_interchange.subst`: acting by `κ` and then by `θ`, which substitutes slots
  of the values of `κ`, equals acting by `pushforward θ κ`.
* `act_interchange`: `θ.act Ω (κ.act 1 e) = (pushforward θ κ).act 1 (θ.act Ψ e)`.
-/

/-- The substitution sending each slot `x : Θ ∋ β` to `σ` acting at depth `Ω ⋈ β`
on `κ x`. -/
abbrev pushforward
    {Γ Δ Ξ Θ Ω : C.Arity}
    (σ : Subst Δ (Γ ⋈ Ξ)) (κ : Subst Θ (Γ ⋈ Δ ⋈ Ω)) :
  Subst Θ (Γ ⋈ Ξ ⋈ Ω) :=
  fun {β} x => σ.act (Ω ⋈ β) (κ x)

/-- `σ` acting at depth `Θ ⋈ Ψ ⋈ Φ` keeps a head `(((Renaming.inl Γ Δ ⇑ʳ Θ) ⇑ʳ Ψ) ⇑ʳ Φ) p`
with `p : Γ ⋈ Θ ⋈ Ψ ⋈ Φ ∋ β` and acts on the arguments. -/
theorem act_renamed_head
    {Γ Δ Ξ Θ Ψ Φ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ)) {β : C.Arity}
    (p : Γ ⋈ Θ ⋈ Ψ ⋈ Φ ∋ β) (args : Expr.Args (Γ ⋈ Δ ⋈ Θ ⋈ Ψ ⋈ Φ) β) :
  σ.act (Θ ⋈ Ψ ⋈ Φ) (.ap ((((Renaming.inl Γ Δ ⇑ʳ Θ) ⇑ʳ Ψ) ⇑ʳ Φ) p) args)
    = .ap ((((Renaming.inl Γ Ξ ⇑ʳ Θ) ⇑ʳ Ψ) ⇑ʳ Φ) p)
        (fun {_} j => σ.act (Θ ⋈ Ψ ⋈ Φ ⋈ _) (args j))
  := by
  head_cases p with z
  case right =>
    simp only [Renaming.extend_inr]
    rw [← C.inr_inr (Γ ⋈ Δ ⋈ Θ) Ψ Φ, ← C.inr_inr (Γ ⋈ Δ) Θ (Ψ ⋈ Φ),
      ← C.inr_inr (Γ ⋈ Ξ ⋈ Θ) Ψ Φ, ← C.inr_inr (Γ ⋈ Ξ) Θ (Ψ ⋈ Φ)]
    apply act_right
  case middle =>
    simp only [Renaming.extend_inl, Renaming.extend_inr]
    rw [← C.inr_inl (Γ ⋈ Δ ⋈ Θ) Ψ Φ, ← C.inr_inr (Γ ⋈ Δ) Θ (Ψ ⋈ Φ),
      ← C.inr_inl (Γ ⋈ Ξ ⋈ Θ) Ψ Φ, ← C.inr_inr (Γ ⋈ Ξ) Θ (Ψ ⋈ Φ)]
    apply act_right
  case left =>
    rcases C.cover Γ Θ z with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · simp only [Renaming.extend_inl, Renaming.inl]
      rw [← C.inl_inl (Γ ⋈ Δ ⋈ Θ) Ψ Φ, ← C.inl_inl (Γ ⋈ Δ) Θ (Ψ ⋈ Φ),
        ← C.inl_inl (Γ ⋈ Ξ ⋈ Θ) Ψ Φ, ← C.inl_inl (Γ ⋈ Ξ) Θ (Ψ ⋈ Φ)]
      apply act_left
    · simp only [Renaming.extend_inl, Renaming.extend_inr]
      rw [← C.inl_inl (Γ ⋈ Δ ⋈ Θ) Ψ Φ, ← C.inr_inl (Γ ⋈ Δ) Θ (Ψ ⋈ Φ),
        ← C.inl_inl (Γ ⋈ Ξ ⋈ Θ) Ψ Φ, ← C.inr_inl (Γ ⋈ Ξ) Θ (Ψ ⋈ Φ)]
      apply act_right

section

local instance : WellFoundedRelation (Sym2 C.Arity) where
  rel := Sym2.GameAdd (@WellFoundedRelation.rel C.Arity inferInstance)
  wf := WellFounded.sym2_gameAdd (@WellFoundedRelation.wf C.Arity inferInstance)

mutual

/-- Acting by `κ` at depth `Χ` and then by `θ` at depth `Φ ⋈ Χ`, which substitutes the
`Ψ`-slots of the values of `κ`, equals acting by `pushforward θ κ` at depth `Χ`. -/
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
      rw [act_right, act_right]
      erw [← C.inr_inr (Γ ⋈ Θ ⋈ Ψ) Φ Χ, act_right]
      congr 1
      · apply C.inr_inr
      · funext Ξ i
        exact act_interchange.subst (Χ := Χ ⋈ Ξ) θ κ (args i)
    case middle =>
      rw [act_middle, act_middle]
      apply Eq.trans (act_interchange.aux θ actedArgs 1 (κ z))
      congr 1
      funext Ξ i
      exact act_interchange.subst (Χ := Χ ⋈ Ξ) θ κ (args i)
    case left =>
      have head : ∀ Λ : C.Arity,
          (C.inl (C.inl z) : Γ ⋈ (Θ ⋈ Λ ⋈ Φ) ⋈ Χ ∋ β)
            = C.inl (Δ := Φ ⋈ Χ) (C.inl (C.inl z)) := by
        intro Λ
        rw [C.inl_inl Γ (Θ ⋈ Λ) Φ z, C.inl_inl Γ Θ Λ z]
        symm
        apply C.inl_inl
      rw [act_left, act_left, head Ψ, head Ω]
      erw [act_left]
      congr 1
      funext Ξ i
      exact act_interchange.subst (Χ := Χ ⋈ Ξ) θ κ (args i)
termination_by (s(Ψ, Λ), (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ))
decreasing_by
  · exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)
  · exact Prod.Lex.left _ _ (Sym2.GameAdd.snd ⟨z⟩)
  · exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)
  · exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)

/-- Acting by `κ` at depth `Φ` and then by `σ` at depth `Θ ⋈ Ω ⋈ Φ` equals acting by
`σ` at depth `Θ ⋈ Ψ ⋈ Φ` and then by `pushforward σ κ` at depth `Φ`. -/
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
      erw [headΩ, headΨ, act_right]
      congr 1
      funext Λ i
      exact act_interchange.aux σ κ (Φ ⋈ Λ) (args i)
    case middle =>
      have headΨ := act_renamed_head σ (C.inl (C.inr z)) args
      simp only [Renaming.extend_inl, Renaming.extend_inr] at headΨ
      rw [act_middle]
      erw [headΨ, act_middle]
      apply Eq.trans (act_interchange.aux (Θ := Θ ⋈ Ω) σ instantiatedArgs 1 (κ z))
      congr 1
      funext Λ i
      exact act_interchange.aux σ κ (Φ ⋈ Λ) (args i)
    case left =>
      head_cases z with w
      case right =>
        have headΩ := act_renamed_head σ (C.inl (C.inl (C.inr w))) instantiatedArgs
        have headΨ := act_renamed_head σ (C.inl (C.inl (C.inr w))) args
        simp only [Renaming.extend_inl, Renaming.extend_inr] at headΩ headΨ
        rw [act_left]
        erw [headΩ, headΨ, act_left]
        congr 1
        funext Λ i
        exact act_interchange.aux σ κ (Φ ⋈ Λ) (args i)
      case middle =>
        rw [act_left, ← C.inl_inl (Γ ⋈ Δ ⋈ Θ) Ω Φ, ← C.inl_inl (Γ ⋈ Δ) Θ (Ω ⋈ Φ),
          ← C.inl_inl (Γ ⋈ Δ ⋈ Θ) Ψ Φ, ← C.inl_inl (Γ ⋈ Δ) Θ (Ψ ⋈ Φ)]
        erw [act_middle, act_middle, act_interchange.subst (Γ := Γ ⋈ Ξ) (Θ := Θ) (Ω := Ω)
          (Φ := Φ) (Χ := 1) (pushforward (Ω := Θ ⋈ Ω) σ κ)
          (fun {Λ} i => σ.act (Θ ⋈ Ψ ⋈ Φ ⋈ Λ) (args i)) (σ w)]
        congr 1
        funext Λ i
        exact act_interchange.aux σ κ (Φ ⋈ Λ) (args i)
      case left =>
        have headΩ := act_renamed_head σ (C.inl (C.inl (C.inl w))) instantiatedArgs
        have headΨ := act_renamed_head σ (C.inl (C.inl (C.inl w))) args
        simp only [Renaming.extend_inl, Renaming.inl] at headΩ headΨ
        rw [act_left]
        erw [headΩ, headΨ, act_left]
        congr 1
        funext Λ i
        exact act_interchange.aux σ κ (Φ ⋈ Λ) (args i)
termination_by (s(Δ, Ψ), (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ))
decreasing_by
  · exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)
  · exact Prod.Lex.left _ _ (Sym2.GameAdd.snd ⟨z⟩)
  · exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)
  · exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)
  · exact Prod.Lex.left _ _ (Sym2.GameAdd.snd_fst ⟨w⟩)
  · exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)
  · exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)

end

end

/-- Acting by `κ` at depth `1` and then by `θ` at depth `Ω` equals acting by `θ` at
depth `Ψ` and then by `pushforward θ κ` at depth `1`. -/
theorem act_interchange
    {Γ Θ Ξ Ψ Ω : C.Arity} (θ : Subst Θ (Γ ⋈ Ξ))
    (κ : Subst Ψ (Γ ⋈ Θ ⋈ Ω)) (e : Expr (Γ ⋈ Θ ⋈ Ψ)) :
  θ.act Ω (κ.act 1 e) = Subst.act (pushforward θ κ) 1 (θ.act Ψ e)
  := by
  apply act_interchange.aux (Θ := 1) _ _ 1
