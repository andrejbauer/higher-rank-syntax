import HigherRankSyntax.Theory.Positive

/-!
# Examples

The signature of the syntax of the untyped λ-calculus, with slots `tm : sort`,
`app : [f a : of tm] of tm` and `lam : [b : [x : of tm] of tm] of tm`, and the theory over it
admitting the instances of `El tm`.
-/

open CategoryTheory

namespace Ctx

/-- The signature with slots `tm : sort`, `app : [f a : of tm] of tm` and
`lam : [b : [x : of tm] of tm] of tm`. -/
def untypedLambdaSyntax : Ctx where
  arity := C.single 1 ⋈ (C.single (C.single 1 ⋈ (C.single 1 ⋈ 1))
    ⋈ (C.single (C.single (C.single 1 ⋈ 1) ⋈ 1) ⋈ 1))
  ambient :=
    dTel.cons .nil .sort
      (dTel.cons
        (dTel.cons .nil (.of (.ap (C.inl (C.inr (C.singleSlot 1)))
            (fun ⦃_⦄ i => (C.unit_is_empty i).elim)))
          (dTel.cons .nil (.of (.ap (C.inl (C.inl (C.inr (C.singleSlot 1))))
            (fun ⦃_⦄ i => (C.unit_is_empty i).elim))) .nil))
        (.of (.ap (C.inl (C.inr (C.singleSlot 1))) (fun ⦃_⦄ i => (C.unit_is_empty i).elim)))
        (dTel.cons
          (dTel.cons
            (dTel.cons .nil (.of (.ap (C.inl (C.inl (C.inr (C.singleSlot 1))))
              (fun ⦃_⦄ i => (C.unit_is_empty i).elim))) .nil)
            (.of (.ap (C.inl (C.inl (C.inr (C.singleSlot 1))))
              (fun ⦃_⦄ i => (C.unit_is_empty i).elim)))
            .nil)
          (.of (.ap (C.inl (C.inl (C.inr (C.singleSlot 1))))
            (fun ⦃_⦄ i => (C.unit_is_empty i).elim)))
          .nil))
  wf := by
    apply Wf_t.cons Wf_t.nil Wf_bd.sort
    apply Wf_t.cons
    · apply Wf_t.cons Wf_t.nil
      · apply Wf_bd.of
        · apply Wf_e.ap
          · exact not_false
          · exact Wf_s.nil
        · exact Eq_bd.sort
      · apply Wf_t.cons Wf_t.nil _ Wf_t.nil
        apply Wf_bd.of
        · apply Wf_e.ap
          · exact not_false
          · exact Wf_s.nil
        · exact Eq_bd.sort
    · apply Wf_bd.of
      · apply Wf_e.ap
        · exact not_false
        · exact Wf_s.nil
      · exact Eq_bd.sort
    · apply Wf_t.cons _ _ Wf_t.nil
      · apply Wf_t.cons _ _ Wf_t.nil
        · apply Wf_t.cons Wf_t.nil _ Wf_t.nil
          apply Wf_bd.of
          · apply Wf_e.ap
            · exact not_false
            · exact Wf_s.nil
          · exact Eq_bd.sort
        · apply Wf_bd.of
          · apply Wf_e.ap
            · exact not_false
            · exact Wf_s.nil
          · exact Eq_bd.sort
      · apply Wf_bd.of
        · apply Wf_e.ap
          · exact not_false
          · exact Wf_s.nil
        · exact Eq_bd.sort

/-- The slot `tm` of `untypedLambdaSyntax`, as a sort over it. -/
def untypedLambdaSyntax.tm : Tm₁ untypedLambdaSyntax.toOb (U untypedLambdaSyntax.toOb) :=
  Tm₁.ofFill ⟨Subst.single (Expr.η (C.inl (C.singleSlot 1))), by
    constructor
    · apply Wf_t.cons Wf_t.nil Wf_bd.sort Wf_t.nil
    · apply Wf_s.eta_single untypedLambdaSyntax.wf (C.inl (C.singleSlot 1)) not_false⟩

end Ctx

namespace Theory

/-- The theory over `Ctx.untypedLambdaSyntax` admitting the instances of `El tm`. -/
def untypedLambdaSyntax : Theory :=
  ofSchemas Ctx.untypedLambdaSyntax
    (fun _ : Unit => ⟨Over.mk (𝟙 Ctx.untypedLambdaSyntax.toOb),
      Ctx.model.El Ctx.untypedLambdaSyntax.tm⟩)

theorem untypedLambdaSyntax_positive : untypedLambdaSyntax.Positive where
  slot := by
    intro α x
    induction x using slotCases with
    | head =>
      exact PositiveBinding.sort _
    | tail x =>
      induction x using slotCases with
      | head =>
        rw [Ctx.entry]
        erw [Ctx.mk_cons]
        apply PositiveBinding.bind
        · erw [Ctx.mk_of _ ⟨Subst.single _, Wf_t.sort_fill _⟩ rfl]
          apply PositiveEntry.el
        · sorry
      | tail x =>
        sorry
  admissible := sorry

end Theory
