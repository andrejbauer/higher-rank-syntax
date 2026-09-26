import HigherRankSyntax.Instantiation
import HigherRankSyntax.Interchange
import Batteries.Tactic.Trans

/-!
# Monad laws for substitution

* `act_id`: the identity substitution acts as the identity.
* `act_η`: acting by `σ` on the η-expansion of a slot `x` gives `σ x`.
* `act_comp`: acting by `Subst.comp σ θ` is acting by `σ` and then by `θ`.
* `act_ofRenaming`: acting by `Subst.ofRenaming ρ` is renaming along `ρ`.

`Subst.lift σ Φ` extends `σ : Subst Γ Δ` to `Subst (Γ ⋈ Φ) (Δ ⋈ Φ)`, fixing the
slots of `Φ`.
-/

/-- The identity substitution acts as the identity. -/
theorem act_id (Γ Φ : C.Arity) (e : Expr (Γ ⋈ Φ)) :
  Subst.act (Subst.id Γ) (Γ := 1) Φ e = e
  := by
  apply act_idOfη (Γ := 1)
  intro β z
  rw [C.unit_left]
  rfl

/-- `σ` acting at depth `Θ` on the η-expansion of `x : Δ ∋ Θ` is `σ x`. -/
theorem act_η
    {Δ Ξ : C.Arity}
    (σ : Subst Δ Ξ) (Θ : C.Arity) (x : Δ ∋ Θ) :
  σ.act (Γ := 1) Θ (.η x) = σ x
  := by
  rw [Expr.η.eq_1]
  trans
  · convert act_middle (Γ := 1) σ Θ x (fun {_} i => Expr.η (C.inr i)) using 2
    rw [C.unit_left]
  · calc _
        = Subst.act (Subst.instId Ξ Θ) 1 (σ x) := by
          congr 1
          funext Ω i
          apply act_η_right
      _ = σ x := by apply act_inst_id

/-- `s` acting on `Expr.ap x args` is `s x` with its `α`-slots substituted by the
arguments acted on by `s`. -/
theorem act_ap
    {Γ Γ' : C.Arity} (s : Subst Γ Γ')
    {α : C.Arity} (x : Γ ∋ α) (args : Subst α Γ) :
  Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') s 1 (Expr.ap x args)
    = Subst.act (Γ := Γ') (Δ := α) (Ξ := 1)
        (fun ⦃Λ⦄ i => Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') s Λ (args i)) 1 (s x)
  := by
  convert act_middle (Γ := 1) s 1 x args using 2
  rw [C.unit_right, C.unit_left]

/-- If `s x` is the η-expansion of `y`, then `s` acting on `Expr.ap x args` is the
application of `y` to the arguments acted on by `s`. -/
theorem act_ap_eta
    {Γ Γ' : C.Arity} (s : Subst Γ Γ')
    {α : C.Arity} (x : Γ ∋ α) (y : Γ' ∋ α) (h : s x = Expr.η y) (args : Subst α Γ) :
  Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') s 1 (Expr.ap x args)
    = Expr.ap y (fun ⦃Λ⦄ i => Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') s Λ (args i))
  := by
  rw [act_ap, h, act_inst_η, C.unit_right]
  rfl

/-- On `Expr ((Δ ⋈ Ω) ⋈ Φ)`, acting at depth `Φ` by `Subst.copair (Subst.id Δ) σ`
equals acting at depth `Φ` by `σ` with prefix `Δ`. -/
theorem act_copair_prefix {Δ Ω : C.Arity} (σ : Subst Ω Δ) (Φ : C.Arity) :
  ∀ e : Expr ((Δ ⋈ Ω) ⋈ Φ),
    Subst.act (Γ := 1) (Δ := Δ ⋈ Ω) (Ξ := Δ) (Subst.copair (Subst.id Δ) σ) Φ e
      = Subst.act (Γ := Δ) (Δ := Ω) (Ξ := 1) σ Φ e
  | .ap x args => by
      head_cases x with z
      case right =>
        rw [act_right]
        trans
        · apply act_right (Γ := 1)
        · congr 1
          funext Λ i
          apply act_copair_prefix
      case middle =>
        rw [act_middle (Γ := Δ)]
        convert act_middle (Γ := 1) (Subst.copair (Subst.id Δ) σ) Φ (C.inr z) args using 2
        · rw [C.unit_left]
          rfl
        · rw [Subst.copair_inr]
          congr 1
          funext Λ i
          symm
          apply act_copair_prefix
      case left =>
        rw [act_left (Γ := Δ)]
        convert act_middle (Γ := 1) (Subst.copair (Subst.id Δ) σ) Φ (C.inl z) args using 2
        · rw [C.unit_left]
          rfl
        · rw [Subst.copair_inl, Subst.id]
          symm
          trans
          · apply act_inst_η
          · rw [C.unit_right]
            congr 1
            funext Λ i
            apply act_copair_prefix
termination_by e => (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args i

/-- `Subst.instId Γ α` acting at depth `Φ` on `e` renamed along
`(Renaming.inl Γ α ⇑ʳ α) ⇑ʳ Φ` gives back `e`. -/
theorem act_instId_weaken (Γ α : C.Arity) :
  ∀ {Φ : C.Arity} (e : Expr (Γ ⋈ α ⋈ Φ)),
    Subst.act (Γ := Γ ⋈ α) (Δ := α) (Ξ := 1) (Subst.instId Γ α) Φ
        (⟦ (Renaming.inl Γ α ⇑ʳ α) ⇑ʳ Φ ⟧ʳ e)
      = e
  | Φ, .ap (α := β) x args => by
      head_cases x with z
      case right =>
        rw [Renaming.act_ap, Renaming.extend_inr, act_right]
        congr 1
        funext Ω i
        rw [← Renaming.extend_assoc]
        apply act_instId_weaken
      case middle =>
        rw [Renaming.act_ap, Renaming.extend_inl, Renaming.extend_inr, act_middle,
          Subst.instId]
        trans
        · apply act_inst_η
        · congr 1
          funext Ω i
          rw [← Renaming.extend_assoc]
          apply act_instId_weaken
      case left =>
        rw [Renaming.act_ap, Renaming.extend_inl, Renaming.extend_inl, act_left]
        congr 1
        · rw [C.unit_right]
          rfl
        · funext Ω i
          rw [← Renaming.extend_assoc]
          apply act_instId_weaken
termination_by Φ e => (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args i

/-- Acting by `Subst.ofRenaming ρ` at depth `Φ` is renaming along `ρ ⇑ʳ Φ`. -/
theorem act_ofRenaming {Γ Δ Φ : C.Arity} (ρ : Γ →ʳ Δ) :
  ∀ e : Expr (Γ ⋈ Φ),
    Subst.act (Subst.ofRenaming ρ) (Γ := 1) Φ e = Renaming.act (ρ ⇑ʳ Φ) e
  | .ap (α := β) x args => by
      rcases C.cover Γ Φ x with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · rw [Renaming.act_ap, Renaming.extend_inl]
        trans
        · convert act_middle (Γ := 1) (Subst.ofRenaming ρ) Φ z args using 2
          rw [C.unit_left]
          rfl
        · rw [Subst.ofRenaming, act_inst_η]
          congr 1
          funext Ω i
          rw [← Renaming.extend_assoc]
          apply act_ofRenaming
      · rw [Renaming.act_ap, Renaming.extend_inr]
        trans
        · apply act_right (Γ := 1)
        · congr 1
          funext Ω i
          rw [← Renaming.extend_assoc]
          apply act_ofRenaming
termination_by e => (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args i

/-- With prefix `S`, the substitution `x ↦ Expr.η (C.inr (ρ x))` acting at depth
`Φ` is renaming along `Renaming.prefixed S ρ ⇑ʳ Φ`. -/
theorem act_ofRenaming_prefixed {S Γ Δ Φ : C.Arity} (ρ : Γ →ʳ Δ) :
  ∀ e : Expr (S ⋈ Γ ⋈ Φ),
    Subst.act (Γ := S) (fun ⦃_⦄ x => Expr.η (C.inr (ρ x))) Φ e
      = Renaming.act ((Renaming.prefixed S ρ) ⇑ʳ Φ) e
  | .ap x args => by
      head_cases x with z
      case right =>
        rw [act_right, Renaming.act_ap, Renaming.extend_inr]
        congr 1
        funext Ω i
        rw [← Renaming.extend_assoc]
        apply act_ofRenaming_prefixed
      case middle =>
        rw [act_middle, Renaming.act_ap, Renaming.extend_inl, Renaming.prefixed_inr, act_inst_η]
        congr 1
        funext Ω i
        rw [← Renaming.extend_assoc]
        apply act_ofRenaming_prefixed
      case left =>
        rw [act_left, Renaming.act_ap, Renaming.extend_inl, Renaming.prefixed_inl]
        congr 1
        funext Ω i
        rw [← Renaming.extend_assoc]
        apply act_ofRenaming_prefixed
termination_by e => (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args i

/-- The substitution `i ↦ ⟦ ρ ⇑ʳ Λ ⟧ʳ (σ i)` acting at depth `1` on
`⟦ ρ ⇑ʳ Θ ⟧ʳ e` is `σ` acting at depth `1` on `e`, renamed along `ρ`. -/
theorem act_rename
    (Γ Δ Θ : C.Arity) (ρ : Γ →ʳ Δ) (σ : Subst Θ Γ) (e : Expr (Γ ⋈ Θ)) :
  Subst.act (Γ := Δ) (Δ := Θ) (Ξ := 1)
      (fun ⦃Λ⦄ i => ⟦ ρ ⇑ʳ Λ ⟧ʳ (σ i)) 1 (⟦ ρ ⇑ʳ Θ ⟧ʳ e : Expr (Δ ⋈ Θ))
    = ⟦ ρ ⟧ʳ (Subst.act (Γ := Γ) (Δ := Θ) (Ξ := 1) σ 1 e)
  := by
  calc _
      = Subst.act (Γ := Δ) (pushforward (Γ := 1) (Ω := 1) (Subst.ofRenaming ρ) σ) 1
          ((Subst.ofRenaming ρ).act (Γ := 1) Θ e) := by
        congr 1
        · funext Λ i
          symm
          apply act_ofRenaming
        · symm
          apply act_ofRenaming
    _ = (Subst.ofRenaming ρ).act (Γ := 1) 1 (Subst.act (Γ := Γ) (Ξ := 1) σ 1 e) := by
        symm
        exact act_interchange (Γ := 1) (Ω := 1) _ σ e
    _ = _ := by
        convert act_ofRenaming (Φ := 1) ρ _ using 2
        rw [Renaming.extend_unit]
        rfl

/-- The substitution `i ↦ ⟦ ρ ⇑ʳ Λ ⟧ʳ (σ i)` acting at depth `Φ` on
`⟦ (ρ ⇑ʳ Θ) ⇑ʳ Φ ⟧ʳ e` is `σ` acting at depth `Φ` on `e`, renamed along
`ρ ⇑ʳ Φ`. -/
theorem act_rename_suffix
    (Γ Δ Θ : C.Arity) (ρ : Γ →ʳ Δ) (σ : Subst Θ Γ) (Φ : C.Arity)
    (e : Expr (Γ ⋈ Θ ⋈ Φ)) :
  Subst.act (Γ := Δ) (Δ := Θ) (Ξ := 1)
      (fun ⦃Λ⦄ i => ⟦ ρ ⇑ʳ Λ ⟧ʳ (σ i)) Φ (⟦ (ρ ⇑ʳ Θ) ⇑ʳ Φ ⟧ʳ e : Expr (Δ ⋈ Θ ⋈ Φ))
    = ⟦ ρ ⇑ʳ Φ ⟧ʳ (Subst.act (Γ := Γ) (Δ := Θ) (Ξ := 1) σ Φ e)
  := by
  calc _
      = Subst.act (Γ := Δ) (pushforward (Γ := 1) (Ω := 1) (Subst.ofRenaming ρ) σ) Φ
          ((Subst.ofRenaming ρ).act (Γ := 1) (Θ ⋈ Φ) e) := by
        congr 1
        · funext Λ i
          symm
          apply act_ofRenaming
        · rw [← Renaming.extend_assoc]
          symm
          apply act_ofRenaming
    _ = (Subst.ofRenaming ρ).act (Γ := 1) Φ (Subst.act (Γ := Γ) (Ξ := 1) σ Φ e) := by
        symm
        exact act_interchange.aux (Γ := 1) (Θ := 1) (Ω := 1) _ σ Φ e
    _ = _ := by apply act_ofRenaming

/-- Acting at depth `Φ` by `Subst.comp σ θ` is acting by `σ` and then by `θ`. -/
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
      apply act_comp
    case middle =>
      rw [act_middle, act_middle, act_interchange]
      congr 1
      funext Ω i
      apply act_comp
    case left =>
      rw [act_left, act_left, act_left]
      congr 1
      funext Ω i
      apply act_comp
termination_by (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args _

/-- Renaming the η-expansion of `x` along `ρ ⇑ʳ α` gives the η-expansion of
`ρ x`. -/
theorem Renaming.act_eta :
  ∀ {Γ Δ α : C.Arity} (ρ : Γ →ʳ Δ) (x : Γ ∋ α),
    (⟦ ρ ⇑ʳ α ⟧ʳ (Expr.η x) : Expr (Δ ⋈ α)) = Expr.η (ρ x)
  | _, _, α, ρ, x => by
      rw [Expr.η.eq_1, Renaming.act_ap, Expr.η.eq_1, extend_inl]
      congr 1
      funext Ω i
      rw [act_eta, extend_inr]
termination_by Γ Δ α _ _ => α
decreasing_by exact ⟨i⟩

/-- If `κ (ρ x)` is `κ' x` renamed along `ρ'` for every slot `x`, then `κ` acting
at depth `Φ` after renaming along `ρ ⇑ʳ Φ` is `κ'` acting at depth `Φ` followed by
renaming along `ρ' ⇑ʳ Φ`. -/
theorem act_square
    {Γ Γ' Δ Δ' : C.Arity} (ρ : Γ →ʳ Γ') (ρ' : Δ →ʳ Δ')
    (κ : Subst Γ' Δ') (κ' : Subst Γ Δ)
    (h : ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α), κ (ρ x) = ⟦ ρ' ⇑ʳ α ⟧ʳ (κ' x))
    (Φ : C.Arity) (e : Expr (Γ ⋈ Φ)) :
  Subst.act (Γ := 1) κ Φ (⟦ ρ ⇑ʳ Φ ⟧ʳ e) = ⟦ ρ' ⇑ʳ Φ ⟧ʳ (Subst.act (Γ := 1) κ' Φ e)
  := by
  calc _
      = Subst.act (Γ := 1) κ Φ (Subst.act (Γ := 1) (Subst.ofRenaming ρ) Φ e) := by
        rw [act_ofRenaming]
        rfl
    _ = Subst.act (Γ := 1) (Subst.comp (Subst.ofRenaming ρ) κ) Φ e := by
        rw [act_comp]
    _ = Subst.act (Γ := 1) (Subst.comp κ' (Subst.ofRenaming ρ')) Φ e := by
        congr 1
        funext α x
        rw [Subst.comp, Subst.comp, Subst.ofRenaming, act_η, h, act_ofRenaming]
    _ = _ := by rw [act_comp, act_ofRenaming]

namespace Subst

/-- The substitution `Subst (Γ ⋈ Φ) (Δ ⋈ Φ)` sending `x : Γ ⋈ Φ ∋ β` to `σ` acting
at depth `Φ ⋈ β` on the η-expansion of `x`. -/
def lift {Γ Δ : C.Arity} (σ : Subst Γ Δ) (Φ : C.Arity) :
    Subst (Γ ⋈ Φ) (Δ ⋈ Φ) :=
  pushforward (Γ := 1) (Ω := Φ) σ (id (Γ ⋈ Φ))

/-- Acting by `lift σ Φ` at depth `Ψ` is acting by `σ` at depth `Φ ⋈ Ψ`. -/
theorem act_lift
    {Γ Δ : C.Arity} (σ : Subst Γ Δ) (Φ Ψ : C.Arity)
    (e : Expr (Γ ⋈ Φ ⋈ Ψ)) :
  cast (congrArg (fun Ω => Expr Ω) (mul_assoc Δ Φ Ψ))
      (act (Γ := 1) (Ξ := Δ ⋈ Φ) (lift σ Φ) Ψ e)
    = act (Γ := 1) σ (Φ ⋈ Ψ) e
  := by
  symm
  convert act_interchange.subst (Γ := 1) (Θ := 1) (Φ := Φ) σ (id (Γ ⋈ Φ)) e using 2
  congr 1
  symm
  apply act_id

/-- Acting by `lift σ Φ` at depth `1` is acting by `σ` at depth `Φ`. -/
theorem act_lift_depth {Γ Δ Φ : C.Arity} (σ : Subst Γ Δ) (e : Expr (Γ ⋈ Φ)) :
  act (Γ := 1) (Δ := Γ ⋈ Φ) (Ξ := Δ ⋈ Φ) (lift σ Φ) 1 e
    = act (Γ := 1) (Δ := Γ) (Ξ := Δ) σ Φ e
  := by
  exact act_lift σ Φ 1 e

/-- Acting at depth `Λ` by `lift s Χ` and then by the substitution
`i ↦ s.act Λ' (τ i)` equals acting at depth `Λ` by `τ` and then by `s`. -/
theorem act_lift_fillers
    {Γ Γ' Χ Λ : C.Arity} (s : Subst Γ Γ') (τ : Subst Χ Γ)
    (e : Expr (Γ ⋈ Χ ⋈ Λ)) :
  act (Γ := Γ') (Δ := Χ) (Ξ := 1)
      (fun ⦃Λ'⦄ i => act (Γ := 1) (Δ := Γ) (Ξ := Γ') s Λ' (τ i)) Λ
      (act (Γ := 1) (Δ := Γ ⋈ Χ) (Ξ := Γ' ⋈ Χ) (lift s Χ) Λ e)
    = act (Γ := 1) (Δ := Γ) (Ξ := Γ') s Λ
        (act (Γ := Γ) (Δ := Χ) (Ξ := 1) τ Λ e)
  := by
  symm
  convert act_interchange.aux (Γ := 1) (Θ := 1) (Ω := 1) s τ Λ e using 2
  congr 1
  exact act_lift s Χ Λ e

/-- `lift (Subst.id Γ) Φ` is the identity substitution on `Γ ⋈ Φ`. -/
theorem lift_id (Γ Φ : C.Arity) :
  lift (id Γ) Φ = id (Γ ⋈ Φ)
  := by
  funext Λ x
  apply act_id

/-- `lift σ Φ x` is `σ` acting at depth `Φ ⋈ Λ` on the η-expansion of
`x : Γ ⋈ Φ ∋ Λ`. -/
theorem lift_apply
    {Γ Δ : C.Arity} (σ : Subst Γ Δ) (Φ : C.Arity)
    {Λ : C.Arity} (x : Γ ⋈ Φ ∋ Λ) :
  cast (congrArg (fun Ω => Expr Ω) (mul_assoc Δ Φ Λ)) (lift σ Φ x)
    = act (Γ := 1) σ (Φ ⋈ Λ) (Expr.η x : Expr (Γ ⋈ Φ ⋈ Λ))
  := by
  rfl

/-- `lift τ Φ` sends a slot `v` of `Φ` to the η-expansion of `C.inr v`. -/
theorem lift_inr {Γ Δ Φ : C.Arity} (τ : Subst Γ Δ) {β : C.Arity} (v : Φ ∋ β) :
  lift τ Φ (C.inr v) = Expr.η (C.inr v)
  := by
  apply act_η_right (Γ := 1)

/-- `lift τ Φ` sends `C.inl u` to `τ u` renamed along `Renaming.inl Δ Φ ⇑ʳ β`. -/
theorem lift_inl {Γ Δ Φ : C.Arity} (τ : Subst Γ Δ) {β : C.Arity} (u : Γ ∋ β) :
  lift τ Φ (C.inl u) = ⟦ Renaming.inl Δ Φ ⇑ʳ β ⟧ʳ (τ u)
  := by
  apply Eq.trans (lift_apply τ Φ (C.inl u))
  rw [Expr.η.eq_1]
  trans
  · convert act_middle (Γ := 1) τ (Φ ⋈ β) u (fun {_} i => Expr.η (C.inr (C.inr i))) using 2
    rw [← C.inl_inl]
    congr 1
    · rw [C.unit_left]
      rfl
    · funext Λ i
      rw [C.inr_inr]
      rfl
  · calc _
        = act (Γ := Δ) (Ξ := Φ ⋈ β) (fun ⦃Λ⦄ (i : β ∋ Λ) => Expr.η (C.inr (C.inr i))) 1
            (τ u) := by
          congr 1
          funext Λ i
          apply act_η_right
      _ = ⟦ Renaming.prefixed Δ (fun ⦃_⦄ (j : β ∋ _) => C.inr j) ⇑ʳ 1 ⟧ʳ (τ u) := by
          apply act_ofRenaming_prefixed
      _ = _ := by
          rw [Renaming.extend_unit]
          congr 1
          funext Λ y
          rcases C.cover Δ β y with ⟨z, rfl⟩ | ⟨z, rfl⟩
          · rw [Renaming.prefixed_inl, Renaming.extend_inl, Renaming.inl, C.inl_inl Δ Φ β z]
          · rw [Renaming.prefixed_inr, Renaming.extend_inr, C.inr_inr Δ Φ β z]

/-- `lift (Subst.ofRenaming ρ) Φ` is `Subst.ofRenaming (ρ ⇑ʳ Φ)`. -/
theorem lift_ofRenaming {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) (Φ : C.Arity) :
  lift (ofRenaming ρ) Φ = ofRenaming (ρ ⇑ʳ Φ)
  := by
  funext β x
  rcases C.cover Γ Φ x with ⟨u, rfl⟩ | ⟨v, rfl⟩
  · rw [lift_inl, ofRenaming, ofRenaming, Renaming.act_eta, Renaming.inl,
      Renaming.extend_inl]
  · rw [lift_inr, ofRenaming, Renaming.extend_inr]

/-- `lift (Subst.copair (Subst.id Δ) σ) Φ` sends `C.inl (C.inl w)`, for
`w : Δ ∋ β`, to the η-expansion of `C.inl w`. -/
theorem lift_copair_inl_inl
    {Δ Ω Φ : C.Arity} (σ : Subst Ω Δ)
    {β : C.Arity} (w : Δ ∋ β) :
  lift (copair (id Δ) σ) Φ (C.inl (C.inl w)) = Expr.η (C.inl w)
  := by
  rw [lift_inl, copair_inl, id, Renaming.act_eta, Renaming.inl]

/-- `lift (Subst.copair (Subst.id Δ) σ) Φ` sends `C.inl (C.inr y)`, for
`y : Ω ∋ β`, to `σ y` renamed along `Renaming.inl Δ Φ ⇑ʳ β`. -/
theorem lift_copair_inl_inr
    {Δ Ω Φ : C.Arity} (σ : Subst Ω Δ)
    {β : C.Arity} (y : Ω ∋ β) :
  lift (copair (id Δ) σ) Φ (C.inl (C.inr y))
    = ⟦ Renaming.inl Δ Φ ⇑ʳ β ⟧ʳ (σ y)
  := by
  rw [lift_inl, copair_inr]

/-- `lift σ 1` is `σ`. -/
theorem lift_one {Γ Δ : C.Arity} (σ : Subst Γ Δ) :
  lift σ 1 = σ
  := by
  funext α x
  apply Eq.trans (lift_apply σ 1 x)
  apply act_η

/-- Lifting by `Φ ⋈ Ψ` is lifting by `Φ` and then by `Ψ`. -/
theorem lift_assoc {Γ Δ : C.Arity} (σ : Subst Γ Δ) (Φ Ψ : C.Arity) :
  lift σ (Φ ⋈ Ψ) = lift (lift σ Φ) Ψ
  := by
  funext α x
  apply Eq.trans (lift_apply σ (Φ ⋈ Ψ) x)
  symm
  apply Eq.trans (lift_apply (lift σ Φ) Ψ x)
  exact act_lift σ Φ (Ψ ⋈ α) _

/-- `lift (Subst.comp σ θ) Φ` is `Subst.comp (lift σ Φ) (lift θ Φ)`. -/
theorem lift_comp
    {Γ Δ Ξ : C.Arity} (σ : Subst Γ Δ)
    (θ : Subst Δ Ξ) (Φ : C.Arity) :
  lift (comp (Γ := 1) (Ξ := Ξ) σ θ) Φ
    = comp (Γ := 1) (Θ := Δ ⋈ Φ) (Ξ := Ξ ⋈ Φ) (lift σ Φ) (lift θ Φ)
  := by
  funext Λ x
  apply Eq.trans (lift_apply (comp (Γ := 1) σ θ) Φ x)
  apply Eq.trans (act_comp (Γ := 1) σ θ (Φ ⋈ Λ) _)
  symm
  exact act_lift θ Φ Λ (lift σ Φ x)

end Subst

/-- If `κ (ρ x)` is `κ' x` renamed along `ρ'` for every slot `x`, then
`Subst.lift κ S ((ρ ⇑ʳ S) x)` is `Subst.lift κ' S x` renamed along
`(ρ' ⇑ʳ S) ⇑ʳ γ`. -/
theorem lift_square
    {Γ Γ' Δ Δ' : C.Arity} (ρ : Γ →ʳ Γ') (ρ' : Δ →ʳ Δ')
    (κ : Subst Γ' Δ') (κ' : Subst Γ Δ)
    (h : ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α), κ (ρ x) = ⟦ ρ' ⇑ʳ α ⟧ʳ (κ' x)) (S : C.Arity) :
  ∀ ⦃γ : C.Arity⦄ (x : (Γ ⋈ S) ∋ γ),
    Subst.lift κ S ((ρ ⇑ʳ S) x) = ⟦ (ρ' ⇑ʳ S) ⇑ʳ γ ⟧ʳ (Subst.lift κ' S x)
  := by
  intro γ x
  calc _
      = Subst.act (Γ := 1) κ (S ⋈ γ) (⟦ (ρ ⇑ʳ S) ⇑ʳ γ ⟧ʳ (Expr.η x)) := by
        symm
        apply congrArg
        apply Renaming.act_eta
    _ = _ := by
        rw [← Renaming.extend_assoc, ← Renaming.extend_assoc]
        apply act_square ρ ρ' κ κ' h

/-- If `κ (ρ x)` is the η-expansion of `ρ' x` for every slot `x`, then `κ` acting
at depth `Φ` after renaming along `ρ ⇑ʳ Φ` is renaming along `ρ' ⇑ʳ Φ`. -/
theorem act_rename_cancel
    {Γ Δ' Γ' : C.Arity} (ρ : Γ →ʳ Δ') (ρ' : Γ →ʳ Γ')
    (κ : Subst Δ' Γ') (h : ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α), κ (ρ x) = Expr.η (ρ' x))
    (Φ : C.Arity) (e : Expr (Γ ⋈ Φ)) :
  Subst.act (Γ := 1) κ Φ (⟦ ρ ⇑ʳ Φ ⟧ʳ e) = ⟦ ρ' ⇑ʳ Φ ⟧ʳ e
  := by
  rw [act_square ρ ρ' κ (Subst.id Γ), act_id]
  intro α x
  rw [h, Subst.id, Renaming.act_eta]

/-- Acting at depth `Φ` by `Subst.copair (Subst.id Γ') s` on `e` renamed along
`Renaming.inr Γ' Γ ⇑ʳ Φ` is acting at depth `Φ` by `s` on `e`. -/
theorem act_copair_inr
    {Γ Γ' : C.Arity} (s : Subst Γ Γ') (Φ : C.Arity)
    (e : Expr (Γ ⋈ Φ)) :
  Subst.act (Γ := 1) (Δ := Γ' ⋈ Γ) (Ξ := Γ') (Subst.copair (Subst.id Γ') s) Φ
      (⟦ Renaming.inr Γ' Γ ⇑ʳ Φ ⟧ʳ e)
    = Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') s Φ e
  := by
  apply Eq.trans
    (act_square (Renaming.inr Γ' Γ) (𝟙ʳ Γ') (Subst.copair (Subst.id Γ') s) s ?_ Φ e)
  · rw [Renaming.extend_id, Renaming.act_id]
  · intro α x
    rw [Renaming.inr, Subst.copair_inr, Renaming.extend_id, Renaming.act_id]
