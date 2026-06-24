import HigherRankSyntax.Dispatch
import Batteries.Tactic.Trans
import Mathlib.Tactic.Convert

universe u

/-!
# The substitution commuting square

`act_interchange.aux` is the general square: acting by `σ` commutes with
instantiating `κ` (pushed forward along `σ`).  `act_interchange` is its
`Θ = nil`, `Φ = nil` instance, used by `act_comp`.
-/

/-- Push `κ` forward along `σ`: `(pushforward σ κ) x = σ.act (κ x)` at the
passive depth determined by the filler. -/
abbrev pushforward {A : Type} {C : Carrier A} {Γ Δ Ξ Θ Ω : C.Arity}
    (σ : Subst Δ (Γ ⋈ Ξ)) (κ : Subst Θ (Γ ⋈ Δ ⋈ Ω)) :
    Subst Θ (Γ ⋈ Ξ ⋈ Ω) :=
  fun {β} x => σ.act (Ω ⋈ β) (κ x)

/-- `σ.act` on a head whose slot lies in a telescope `Φ` sitting in the depth
`Λ ⋈ Φ ⋈ Ρ` (injected past the prefix `Γ ⋈ Δ ⋈ Λ` and weakened past `Ρ`): the head is
rebuilt over the new codomain and the action descends into the arguments.  Generalizes
`act_right` (`Λ = Ρ = Shape.nil`). -/
theorem act_ap_depth {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Ξ)) (Λ Φ Ρ : C.Arity) {α} (z : Φ ∋ α)
    (args : Expr.Args (Γ ⋈ Δ ⋈ Λ ⋈ Φ ⋈ Ρ) α) :
  σ.act (Λ ⋈ Φ ⋈ Ρ)
      (Expr.ap (C.inr (Γ := Ρ) (C.inl (Δ := Λ * (Δ * Γ)) z)) args)
    =
  Expr.ap (C.inr (C.inl (Δ := Λ * (Ξ * Γ)) z))
    (fun {Ω} j => σ.act (Λ ⋈ Φ ⋈ Ρ ⋈ Ω) (args j))
  := by
  let p := C.inr (Γ := Ρ) (Δ := Φ * Λ) (C.inl z)
  have h {Τ : C.Arity} :
      (C.inr (C.inl z) : Ρ * (Φ * (Λ * Τ)) ∋ α) = (C.inl p) := by
    rw [C.inl_inl Φ Λ Τ z]
    exact C.inr_inl Ρ (Φ * Λ) Τ (C.inl z)
  rw [h]
  conv => rhs; rw [h]
  exact act_right σ (Λ ⋈ Φ ⋈ Ρ) p args

mutual

/-- Acting by `θ` commutes with applying `κ` when `θ` acts on variables that may
occur in the fillers of `κ`. -/
theorem act_interchange.subst {A : Type} {C : Carrier A} {Γ Λ Θ Ψ Ω Φ Χ : C.Arity}
    (θ : Subst Ψ (Γ ⋈ Θ ⋈ Ω)) (κ : Subst Λ (Γ ⋈ Θ ⋈ Ψ ⋈ Φ)) (e : Expr (Γ ⋈ Λ ⋈ Χ)) :
  θ.act (Φ ⋈ Χ) (Subst.act (Γ := Γ) (Ξ := Θ ⋈ Ψ ⋈ Φ) κ Χ e)
    =
  Subst.act (Γ := Γ) (Ξ := Θ ⋈ Ω ⋈ Φ) (pushforward (Γ := Γ ⋈ Θ) (Ω := Φ) θ κ) Χ e
  := by
  match e with
  | .ap (α := β) x args =>
    head_cases x with z
    case right =>
      rw [act_right]
      convert act_right θ (Φ ⋈ Χ) (C.inl z)
        (fun {_} j => Subst.act (Ξ := Θ ⋈ Ψ ⋈ Φ) κ (Χ ⋈ _) (args j)) using 2
      · congr 1 ; exact C.inl_inl Χ Φ (Ψ * (Θ * Γ)) z
      · rw [act_right]
        congr 1
        · exact C.inl_inl Χ Φ (Ω * (Θ * Γ)) z
        · funext Ω' i
          symm
          exact act_interchange.subst (Χ := Χ ⋈ Ω') θ κ (args i)
    case middle =>
      rw [act_left_right]
      convert act_interchange.aux θ
        (Subst.fromArgs (Γ ⋈ Θ ⋈ Ψ ⋈ Φ ⋈ Χ) β
          fun {_} i => Subst.act (Ξ := Θ ⋈ Ψ ⋈ Φ) κ (Χ ⋈ _) (args i))
        1 (κ z) using 2
      · rw [act_left_right]
        congr 1
        funext Ω' i
        symm
        exact act_interchange.subst (Χ := Χ ⋈ Ω') θ κ (args i)
    case left =>
      have h {S : C.Arity} :
          (C.inr (C.inr z) : Χ * ((Φ * (S * Θ)) * Γ) ∋ β) =
          (C.inr (C.inr (C.inr z)) : (Χ * Φ) * (S * (Θ * Γ)) ∋ β) := by
        exact (congrArg C.inr ((C.inr_inr Φ (S * Θ) Γ z).symm)).trans <|
          (congrArg C.inr (congrArg C.inr ((C.inr_inr S Θ Γ z).symm))).trans <|
            C.inr_inr Χ Φ (S * (Θ * Γ)) (C.inr (C.inr z))
      rw [act_left]
      convert act_left θ (Φ ⋈ Χ) (C.inr z)
        (fun {_} j => Subst.act (Γ := Γ) (Ξ := Θ ⋈ Ψ ⋈ Φ) κ (Χ ⋈ _) (args j)) using 2
      · congr 1
        exact h (S := Ψ)
      · rw [act_left]
        congr 1
        · exact h (S := Ω)
        · funext Ω' i
          symm
          exact act_interchange.subst (Χ := Χ ⋈ Ω') θ κ (args i)
termination_by (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args _

/-- Acting by `σ` commutes with instantiating `κ` (pushed forward along `σ`). -/
theorem act_interchange.aux {A : Type} {C : Carrier A} {Γ Δ Ξ Θ Ψ Ω : C.Arity}
    (σ : Subst Δ (Γ ⋈ Ξ)) (κ : Subst Ψ (Γ ⋈ Δ ⋈ Θ ⋈ Ω)) (Φ : C.Arity) (e : Expr (Γ ⋈ Δ ⋈ Θ ⋈ Ψ ⋈ Φ)) :
  σ.act (Θ ⋈ Ω ⋈ Φ) (κ.act Φ e)
    = Subst.act (Γ := Γ ⋈ Ξ ⋈ Θ) (Δ := Ψ) (Ξ := Ω)
        (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ (σ.act (Θ ⋈ Ψ ⋈ Φ) e)
  := by
  match e with
  | .ap (α := β) x args =>
    head_cases x with z
    case right =>
      rw [act_right]
      convert act_right σ (Θ ⋈ Ω ⋈ Φ) (C.inl z)
        (fun {_} j => κ.act (Φ ⋈ _) (args j)) using 2
      · congr 1
        exact C.inl_inl Φ (Ω * Θ) (Δ * Γ) z
      · convert (congrArg
          (Subst.act (Γ := Γ ⋈ Ξ ⋈ Θ) (Δ := Ψ) (Ξ := Ω)
            (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ)
          (act_right σ (Θ ⋈ Ψ ⋈ Φ) (C.inl z) args)) using 2
        · congr 1
          exact C.inl_inl Φ (Ψ * Θ) (Δ * Γ) z
        symm
        convert act_right (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω)
          (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ z _ using 2
        congr 1
        funext Ω' i
        exact act_interchange.aux σ κ (Φ ⋈ Ω') (args i)
    case middle => sorry
    case left => sorry
termination_by (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ)
decreasing_by all_goals exact Expr.Subterm.of_arg x args _
--   match e with
--   | .ap (α := β) x args =>
--     head_cases x with z
--     case right =>             -- z : Φ  (rebuild: both acts pass through)
--       rw [act_right]                              -- κ fires (head already matches)
--       convert act_ap_depth σ (Θ ⋈ Ω) Φ Shape.nil z _ using 2
--       convert congrArg _ (act_ap_depth σ (Θ ⋈ Ψ) Φ Shape.nil z args) using 2
--       symm
--       convert act_right (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω) (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ z _ using 2
--       congr 1
--       funext i
--       exact act_interchange.aux σ κ (Φ ∷ i.arity) (args i)
--     case middle =>             -- z : Ψ  (κ fires)
--       rw [act_left_right]       -- LHS = σ.act (Θ⋈Ω⋈Φ) (⟦argκ⟧ˢ (κ z))
--       convert act_interchange.aux (Θ := Θ ⋈ Ω) _
--         (Subst.fromArgs _ _ fun i => κ.act (Φ ∷ i.arity) (args i)) Shape.nil (κ z) using 2
--       convert congrArg _ (act_ap_depth σ _ _ _ z args) using 2
--       symm
--       convert act_left_right (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω)
--         (pushforward (Ω := Θ ⋈ Ω) σ κ) _ z
--         (fun i => σ.act (Θ ⋈ (Ψ ⋈ Φ ∷ i.arity)) (args i)) using 2
--       congr 1
--       · funext _ z
--         cases z with
--         | here i =>
--           convert act_interchange.aux σ κ (Φ ∷ i.arity) (args i) using 2
--           · apply Subst.act_irrel
--           · convert congrArg
--               (Subst.act (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω)
--                 (pushforward (Ω := Θ ⋈ Ω) σ κ) (Φ ∷ i.arity))
--               (Subst.act_irrel σ (Φ := Θ ⋈ Ψ ⋈ (Φ ∷ i.arity)) _ _ (args i)) using 2
--         | there q => nomatch q
--       · apply Subst.act_irrel
--     case left =>
--       head_cases z with w
--       case right =>            -- w : Θ  (rebuild: both acts pass through)
--         have cow := fun (i : C.Position β) => act_interchange.aux σ κ (Φ ∷ i.arity) (args i)
--         rw [act_left]
--         convert act_ap_depth σ Shape.nil Θ (Ω ⋈ Φ) w _ using 2
--         · apply Subsingleton.elim
--         · rw [← Proper.inl_inl Ψ Φ (Γ ⋈ Δ ⋈ Θ) (Proper.inr (Γ ⋈ Δ) w)]
--           convert congrArg
--             (Subst.act (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω) (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ)
--             (act_ap_depth σ Shape.nil Θ (Ψ ⋈ Φ) w args) using 2
--           · congr 1
--             apply Subst.act_irrel
--           · symm
--             convert act_left (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω)
--               (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ _ _ using 2
--             congr 1
--             funext i
--             convert act_interchange.aux σ κ (Φ ∷ i.arity) (args i) using 2
--             · apply Subsingleton.elim
--             · congr 1
--               apply Subst.act_irrel
--       case middle =>           -- w : Δ  (σ fires)
--         rw [act_left]
--         convert act_left_right σ (Θ ⋈ Ω ⋈ Φ) w _ using 2
--         convert congrArg
--           (Subst.act (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω) (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ)
--           (act_left_right σ (Θ ⋈ Ψ ⋈ Φ) w args) using 2
--         symm
--         convert (act_interchange.subst
--           (Γ := Γ ⋈ Ξ) (Λ := ⌊β⌋) (Θ := Θ) (Ψ := Ψ) (Ω := Ω) (Φ := Φ)
--           (Χ := Shape.nil)
--           (pushforward (Ω := Θ ⋈ Ω) σ κ : Subst Ψ (Γ ⋈ Ξ ⋈ Θ ⋈ Ω))
--           (Subst.fromArgs β _ (fun i => σ.act (Θ ⋈ Ψ ⋈ Φ ∷ i.arity) (args i)))
--           (σ w)) using 2
--         congr 1
--         funext _ q
--         cases q with
--         | here i =>
--           convert act_interchange.aux σ κ (Φ ∷ i.arity) (args i) using 2
--           · apply Subst.act_irrel
--           · unfold pushforward
--             congr 1
--             apply Subst.act_irrel
--         | there q => nomatch q
--       case left =>             -- w : Γ  (rebuild: both acts pass through)
--         rw [act_left]                                       -- κ
--         convert act_left σ (Θ ⋈ Ω ⋈ Φ) w _ using 2         -- σ LHS
--         convert congrArg _ (act_left σ (Θ ⋈ Ψ ⋈ Φ) w args) using 2   -- σ RHS inner
--         symm
--         convert act_left (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω) (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ _ _ using 2
--         funext i
--         convert act_interchange.aux σ κ (Φ ∷ i.arity) (args i) using 2
--         · apply Subsingleton.elim
--         · congr 1
--           apply Subst.act_irrel
-- termination_by
--   (ListArity.Pair.mk ⟨Δ.toList⟩ ⟨Ψ.toList⟩, (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ))
-- decreasing_by
--   · exact .right _ (.of_arg x args _)
--   · exact .right _ (.of_arg x args _)
--   · exact .left _ _ (ListArity.Pair.lt_right (.of_slot z))
--   · exact .right _ (.of_arg x args _)
--   · exact .right _ (.of_arg x args _)
--   · exact .right _ (.of_arg x args _)
--   · exact .left _ _ (ListArity.Pair.lt_swap (.of_slot w))
--   · exact .right _ (.of_arg x args _)

end


-- /-- Acting by `θ` commutes with instantiating `κ`: substituting `κ` then acting
-- by `θ` equals acting by `θ` then substituting the pushed-forward `κ`. -/
-- theorem act_interchange {C : Carrier} {Γ Θ Ξ Ψ Ω : Shape C}
--     [Proper Θ] [Proper Ξ] [Proper Ψ] [Proper Ω]
--     (θ : Subst Θ (Γ ⋈ Ξ)) (κ : Subst Ψ (Γ ⋈ Θ ⋈ Ω))
--     (e : Expr (Γ ⋈ Θ ⋈ Ψ)) :
--   θ.act Ω (κ.act Shape.nil e)
--     = Subst.act (pushforward θ κ) Shape.nil (θ.act Ψ e)
--   := by
--   convert act_interchange.aux (Θ := Shape.nil) θ κ Shape.nil e
--   · apply Subsingleton.elim
--   · congr <;> apply Subsingleton.elim
