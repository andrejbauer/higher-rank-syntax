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
abbrev pushforward {C : Carrier} {Γ Δ Ξ Θ Ω : Shape C}
    [Proper Δ] [Proper Ξ] [Proper Ω] [Proper Θ]
    (σ : Subst Δ (Γ ⋈ Ξ)) (κ : Subst Θ (Γ ⋈ Δ ⋈ Ω)) :
    Subst Θ (Γ ⋈ Ξ ⋈ Ω) :=
  fun {β} x => σ.act (Ω ∷ β) (κ x)

attribute [local instance] Proper.compose

/-- `Subst.act` does not depend on the chosen `Proper` witness for its depth. -/
theorem Subst.act_irrel {C : Carrier} {Γ Δ Ξ : Shape C} [Proper Δ] [Proper Ξ]
    (σ : Subst Δ (Γ ⋈ Ξ)) {Φ : Shape C} (i i' : Proper Φ) (e : Expr (Γ ⋈ Δ ⋈ Φ)) :
    @Subst.act C Γ Δ Ξ _ _ σ Φ i e = @Subst.act C Γ Δ Ξ _ _ σ Φ i' e
  := by
  haveI := Proper.subsingleton Φ
  rw [Subsingleton.elim i i']

/-- `σ.act` on a head whose slot lies in a telescope `Φ` sitting in the depth
`Λ ⋈ Φ ⋈ Ρ` (injected past the prefix `Γ ⋈ Δ ⋈ Λ` and weakened past `Ρ`): the head is
rebuilt over the new codomain and the action descends into the arguments.  Generalizes
`act_ap_right` (`Λ = Ρ = Shape.nil`). -/
theorem act_ap_depth {C : Carrier} {Γ Δ Ξ : Shape C} [Proper Δ] [Proper Ξ]
    (σ : Subst Δ (Γ ⋈ Ξ)) (Λ Φ Ρ : Shape C) [Proper Λ] [Proper Φ] [Proper Ρ]
    {α} (z : Φ ∋ α)
    (args : Expr.Args (Γ ⋈ Δ ⋈ Λ ⋈ Φ ⋈ Ρ) α) :
  σ.act (Λ ⋈ Φ ⋈ Ρ)
      (Expr.ap (Proper.inl (Γ ⋈ Δ ⋈ Λ ⋈ Φ) (Proper.inr (Γ ⋈ Δ ⋈ Λ) z)) args)
    = Expr.ap (Proper.inl (Γ ⋈ Ξ ⋈ Λ ⋈ Φ) (Proper.inr (Γ ⋈ Ξ ⋈ Λ) z))
        (fun j => σ.act (Λ ⋈ (Φ ⋈ Ρ ∷ j.arity)) (args j))
  := by
  convert act_ap_right σ (Λ ⋈ Φ ⋈ Ρ)
      (Proper.inl (Λ ⋈ Φ) (Proper.inr Λ z)) args using 2
  · congr 1
    convert (Proper.compose_inr_inl (Λ ⋈ Φ) Ρ (Γ ⋈ Δ) (Proper.inr Λ z)).symm using 1
    congr 1
    symm
    apply Proper.compose_inr_inr
  · congr 1
    · convert (Proper.compose_inr_inl (Λ ⋈ Φ) Ρ (Γ ⋈ Ξ) (Proper.inr Λ z)).symm using 1
      congr 1
      symm
      apply Proper.compose_inr_inr
    · funext j
      apply Subst.act_irrel

private structure InterchangeMeasure (C : Carrier) where
  fst : DomMeasure C
  snd : DomMeasure C

private inductive InterchangeMeasure.Lt {C : Carrier} :
    InterchangeMeasure C → InterchangeMeasure C → Prop where
  | right {a b b' : DomMeasure C}
      (h : WellFoundedRelation.rel b' b) :
      InterchangeMeasure.Lt ⟨a, b'⟩ ⟨a, b⟩
  | left_swap {a b a' : DomMeasure C}
      (h : WellFoundedRelation.rel a' a) :
      InterchangeMeasure.Lt ⟨b, a'⟩ ⟨a, b⟩

private instance {C : Carrier} : WellFoundedRelation (InterchangeMeasure C) where
  rel := InterchangeMeasure.Lt
  wf := by
    let wf : WellFounded
        (WellFoundedRelation.rel : DomMeasure C → DomMeasure C → Prop) :=
      WellFoundedRelation.wf
    refine ⟨fun f => ?_⟩
    cases f with
    | mk a b =>
        have accPair :
            Acc (InterchangeMeasure.Lt (C := C)) ⟨a, b⟩ ∧
              Acc (InterchangeMeasure.Lt (C := C)) ⟨b, a⟩ :=
          WellFounded.induction wf a (C := fun a =>
              ∀ b : DomMeasure C,
                Acc (InterchangeMeasure.Lt (C := C)) ⟨a, b⟩ ∧
                  Acc (InterchangeMeasure.Lt (C := C)) ⟨b, a⟩)
            (fun a IHa b =>
              WellFounded.induction wf b (C := fun b =>
                  Acc (InterchangeMeasure.Lt (C := C)) ⟨a, b⟩ ∧
                    Acc (InterchangeMeasure.Lt (C := C)) ⟨b, a⟩)
                (fun b IHb => by
                  constructor
                  · refine Acc.intro _ ?_
                    intro y hy
                    cases y with
                    | mk y₀ y₁ =>
                        cases hy with
                        | right h => exact (IHb y₁ h).1
                        | left_swap h => exact (IHa y₁ h b).2
                  · refine Acc.intro _ ?_
                    intro y hy
                    cases y with
                    | mk y₀ y₁ =>
                        cases hy with
                        | right h => exact (IHa y₁ h b).2
                        | left_swap h => exact (IHb y₁ h).1))
            b
        exact accPair.1

private inductive ExprMeasure (C : Carrier) where
  | mk {Γ : Shape C} : Expr Γ → ExprMeasure C

private inductive ExprMeasure.Lt {C : Carrier} : ExprMeasure C → ExprMeasure C → Prop where
  | of_arg {Γ : Shape C} {α : C.Arity} (x : Γ ∋ α)
      (args : Expr.Args Γ α) (i : C.Binder α) :
      ExprMeasure.Lt (.mk (args i)) (.mk (.ap x args))

private theorem ExprMeasure.Lt.wf {C : Carrier} : WellFounded (@ExprMeasure.Lt C) := by
  refine ⟨fun e => ?_⟩
  cases e with
  | mk e =>
      induction e with
      | ap x args ih =>
          refine Acc.intro _ ?_
          intro y h
          cases h
          exact ih _

private instance {C : Carrier} : WellFoundedRelation (ExprMeasure C) where
  rel := ExprMeasure.Lt
  wf := ExprMeasure.Lt.wf

private theorem shape_extList_assoc4
    {C : Carrier} {F : Shape C → Sort u} (Γ Ξ Θ Ω Φ : Shape C) :
  F (Γ ⋈ Ξ ⋈ (Θ ⋈ Ω ⋈ Φ)) = F (Γ ⋈ Ξ ⋈ Θ ⋈ Ω ⋈ Φ) := by
  apply congrArg
  rfl

mutual

/-- Acting by `θ` commutes with applying `κ` when `θ` acts on variables that may
occur in the fillers of `κ`. -/
theorem act_interchange.subst {C : Carrier} {Γ Λ Θ Ψ Ω Φ Χ : Shape C}
    [Proper Λ] [Proper Θ] [Proper Ψ] [Proper Ω] [Proper Φ] [Proper Χ]
    (θ : Subst Ψ (Γ ⋈ Θ ⋈ Ω))
    (κ : Subst Λ (Γ ⋈ Θ ⋈ Ψ ⋈ Φ))
    (e : Expr (Γ ⋈ Λ ⋈ Χ)) :
  θ.act (Φ ⋈ Χ) (Subst.act (Γ := Γ) (Ξ := Θ ⋈ Ψ ⋈ Φ) κ Χ e)
    =
  Subst.act
    (Γ := Γ) (Ξ := Θ ⋈ Ω ⋈ Φ)
    (pushforward (Γ := Γ ⋈ Θ) (Ω := Φ) θ κ) Χ e
  := by
  match e with
  | .ap (α := β) x args =>
    head_cases x with z
    case right =>
      rw [act_ap_right]
      convert act_ap_depth θ Φ Χ Shape.nil z _ using 2
      rw [act_ap_right]
      congr 1
      funext i
      symm
      convert act_interchange.subst (Χ := Χ ∷ i.arity) θ κ (args i) using 2
    case middle =>
      rw [act_ap_middle]
      convert act_interchange.aux
        (Γ := Γ ⋈ Θ) (Δ := Ψ) (Ξ := Ω) (Θ := Φ) (Ψ := ⌊β⌋) (Ω := Χ)
        θ
        (Subst.fromArgs β _ fun i =>
          Subst.act (Γ := Γ) (Ξ := Θ ⋈ Ψ ⋈ Φ) κ (Χ ∷ i.arity) (args i))
        Shape.nil
        (κ z) using 2
      · rw [act_ap_middle]
        unfold pushforward
        congr 1
        · funext _ q
          cases q with
          | here i =>
            symm
            convert act_interchange.subst (Χ := Χ ∷ i.arity) θ κ (args i) using 2
            apply Subst.act_irrel
          | there q => nomatch q
        · apply Subst.act_irrel
    case left =>
      rw [act_ap_left]
      convert act_ap_left θ (Φ ⋈ Χ) (Proper.inl Γ z) _ using 2
      rw [act_ap_left]
      congr 1
      funext i
      symm
      convert act_interchange.subst (Χ := Χ ∷ i.arity) θ κ (args i) using 2
      apply Subst.act_irrel
termination_by
  ((⟨⟨Ψ.toList⟩, ⟨Λ.toList⟩⟩ : InterchangeMeasure C), ExprMeasure.mk e)
decreasing_by
  all_goals
    subst_vars
    first
      | rfl
      | apply shape_extList_assoc4 Γ Ξ Θ Ω Φ
      | exact Prod.Lex.left _ _ (InterchangeMeasure.Lt.right (by
          obtain ⟨γ, hmem, hsub⟩ := SlotAt.subWitness z
          exact DomLt.step γ hmem _ hsub))
      | exact Prod.Lex.right _ (ExprMeasure.Lt.of_arg x args _)

/-- Acting by `σ` commutes with instantiating `κ` (pushed forward along `σ`). -/
theorem act_interchange.aux {C : Carrier} {Γ Δ Ξ Θ Ψ Ω : Shape C}
    [Proper Δ] [Proper Ξ] [Proper Θ] [Proper Ψ] [Proper Ω]
    (σ : Subst Δ (Γ ⋈ Ξ))
    (κ : Subst Ψ (Γ ⋈ Δ ⋈ Θ ⋈ Ω))
    (Φ : Shape C) [Proper Φ]
    (e : Expr (Γ ⋈ Δ ⋈ Θ ⋈ Ψ ⋈ Φ)) :
  σ.act (Θ ⋈ Ω ⋈ Φ) (κ.act Φ e)
    = Subst.act (Γ := Γ ⋈ Ξ ⋈ Θ) (Δ := Ψ) (Ξ := Ω)
        (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ (σ.act (Θ ⋈ Ψ ⋈ Φ) e)
  := by
  match e with
  | .ap (α := β) x args =>
    head_cases x with z
    case right =>             -- z : Φ  (rebuild: both acts pass through)
      rw [act_ap_right]                              -- κ fires (head already matches)
      convert act_ap_depth σ (Θ ⋈ Ω) Φ Shape.nil z _ using 2
      convert congrArg _ (act_ap_depth σ (Θ ⋈ Ψ) Φ Shape.nil z args) using 2
      symm
      convert act_ap_right (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω) (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ z _ using 2
      congr 1
      funext i
      exact act_interchange.aux σ κ (Φ ∷ i.arity) (args i)
    case middle =>             -- z : Ψ  (κ fires)
      rw [act_ap_middle]       -- LHS = σ.act (Θ⋈Ω⋈Φ) (⟦argκ⟧ˢ (κ z))
      convert act_interchange.aux (Θ := Θ ⋈ Ω) _
        (Subst.fromArgs _ _ fun i => κ.act (Φ ∷ i.arity) (args i)) Shape.nil (κ z) using 2
      convert congrArg _ (act_ap_depth σ _ _ _ z args) using 2
      symm
      convert act_ap_middle (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω)
        (pushforward (Ω := Θ ⋈ Ω) σ κ) _ z
        (fun i => σ.act (Θ ⋈ (Ψ ⋈ Φ ∷ i.arity)) (args i)) using 2
      congr 1
      · funext _ z
        cases z with
        | here i =>
          convert act_interchange.aux σ κ (Φ ∷ i.arity) (args i) using 2
          · apply Subst.act_irrel
          · convert congrArg
              (Subst.act (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω)
                (pushforward (Ω := Θ ⋈ Ω) σ κ) (Φ ∷ i.arity))
              (Subst.act_irrel σ (Φ := Θ ⋈ Ψ ⋈ (Φ ∷ i.arity)) _ _ (args i)) using 2
        | there q => nomatch q
      · apply Subst.act_irrel
    case left =>
      head_cases z with w
      case right =>            -- w : Θ  (rebuild: both acts pass through)
        have cow := fun (i : C.Binder β) => act_interchange.aux σ κ (Φ ∷ i.arity) (args i)
        rw [act_ap_left]
        convert act_ap_depth σ Shape.nil Θ (Ω ⋈ Φ) w _ using 2
        · apply Subsingleton.elim
        · rw [← Proper.compose_inl_inl Ψ Φ (Γ ⋈ Δ ⋈ Θ) (Proper.inr (Γ ⋈ Δ) w)]
          convert congrArg
            (Subst.act (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω) (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ)
            (act_ap_depth σ Shape.nil Θ (Ψ ⋈ Φ) w args) using 2
          · congr 1
            apply Subst.act_irrel
          · symm
            convert act_ap_left (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω)
              (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ _ _ using 2
            congr 1
            funext i
            convert act_interchange.aux σ κ (Φ ∷ i.arity) (args i) using 2
            · apply Subsingleton.elim
            · congr 1
              apply Subst.act_irrel
      case middle =>           -- w : Δ  (σ fires)
        rw [act_ap_left]
        convert act_ap_middle σ (Θ ⋈ Ω ⋈ Φ) w _ using 2
        convert congrArg
          (Subst.act (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω) (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ)
          (act_ap_middle σ (Θ ⋈ Ψ ⋈ Φ) w args) using 2
        symm
        convert (act_interchange.subst
          (Γ := Γ ⋈ Ξ) (Λ := ⌊β⌋) (Θ := Θ) (Ψ := Ψ) (Ω := Ω) (Φ := Φ)
          (Χ := Shape.nil)
          (pushforward (Ω := Θ ⋈ Ω) σ κ : Subst Ψ (Γ ⋈ Ξ ⋈ Θ ⋈ Ω))
          (Subst.fromArgs β _ (fun i => σ.act (Θ ⋈ Ψ ⋈ Φ ∷ i.arity) (args i)))
          (σ w)) using 2
        congr 1
        funext _ q
        cases q with
        | here i =>
          convert act_interchange.aux σ κ (Φ ∷ i.arity) (args i) using 2
          · apply Subst.act_irrel
          · unfold pushforward
            congr 1
            apply Subst.act_irrel
        | there q => nomatch q
      case left =>             -- w : Γ  (rebuild: both acts pass through)
        rw [act_ap_left]                                       -- κ
        convert act_ap_left σ (Θ ⋈ Ω ⋈ Φ) w _ using 2         -- σ LHS
        convert congrArg _ (act_ap_left σ (Θ ⋈ Ψ ⋈ Φ) w args) using 2   -- σ RHS inner
        symm
        convert act_ap_left (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω) (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ _ _ using 2
        funext i
        convert act_interchange.aux σ κ (Φ ∷ i.arity) (args i) using 2
        · apply Subsingleton.elim
        · congr 1
          apply Subst.act_irrel
termination_by
  ((⟨⟨Δ.toList⟩, ⟨Ψ.toList⟩⟩ : InterchangeMeasure C), ExprMeasure.mk e)
decreasing_by
  all_goals
    subst_vars
    first
      | rfl
      | exact Prod.Lex.left _ _ (InterchangeMeasure.Lt.right (by
          obtain ⟨γ, hmem, hsub⟩ := SlotAt.subWitness z
          exact DomLt.step γ hmem _ hsub))
      | exact Prod.Lex.left _ _ (InterchangeMeasure.Lt.left_swap (by
          obtain ⟨γ, hmem, hsub⟩ := SlotAt.subWitness w
          exact DomLt.step γ hmem _ hsub))
      | sorry

end

/-- Acting by `θ` commutes with instantiating `κ`: substituting `κ` then acting
by `θ` equals acting by `θ` then substituting the pushed-forward `κ`. -/
theorem act_interchange {C : Carrier} {Γ Θ Ξ Ψ Ω : Shape C}
    [Proper Θ] [Proper Ξ] [Proper Ψ] [Proper Ω]
    (θ : Subst Θ (Γ ⋈ Ξ)) (κ : Subst Ψ (Γ ⋈ Θ ⋈ Ω))
    (e : Expr (Γ ⋈ Θ ⋈ Ψ)) :
  θ.act Ω (κ.act Shape.nil e)
    = Subst.act (pushforward θ κ) Shape.nil (θ.act Ψ e)
  := by
  convert act_interchange.aux (Θ := Shape.nil) θ κ Shape.nil e
  · apply Subsingleton.elim
  · congr <;> apply Subsingleton.elim
