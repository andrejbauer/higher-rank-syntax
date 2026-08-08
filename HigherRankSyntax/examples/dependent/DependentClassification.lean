import ListPrecedence
import HigherRankSyntax.Typing.DecoratedTelescopeMonoid

/-!
# Dependent classification data

The examples decorate `A : Type, x : A` and a term slot classified by a binary
type expression using an external type and a preceding type slot.
-/

namespace T1

open ListCarrier
open CategoryTheory

universe u

inductive RawClass where
  | ty
  | tm
deriving DecidableEq

abbrev depCarrier : Carrier (List (Entry RawClass)) :=
  listCarrier RawClass

def bd : RawClass → Option RawClass
  | .ty => none
  | .tm => some .ty

def nullary (υ : RawClass) : Entry RawClass :=
  .mk [] υ

def oneCtx (υ : RawClass) : depCarrier.Arity :=
  ofList [nullary υ]

def oneSlot (υ : RawClass) :
    oneCtx υ ∋[υ] (1 : depCarrier.Arity) :=
  ⟨⟨0, by simp [oneCtx]⟩, ⟨underlyingList_one.symm, rfl⟩⟩

theorem oneSlot_arity (υ : RawClass) {α : depCarrier.Arity} {ν : RawClass}
    (x : oneCtx υ ∋[ν] α) : α = 1 := by
  apply arity_ext
  have h : underlyingList α = [] := by
    symm
    simpa [oneCtx, nullary, List.get_eq_getElem,
      Entry.arity, Entry.result] using x.property.1
  rw [h]
  exact underlyingList_one.symm

theorem oneSlot_class (υ : RawClass) {α : depCarrier.Arity} {ν : RawClass}
    (x : oneCtx υ ∋[ν] α) : ν = υ := by
  simpa [oneCtx, nullary, List.get_eq_getElem,
    Entry.arity, Entry.result] using x.property.2.symm

def oneSlot_cases (υ : RawClass)
    {motive : ∀ {α : depCarrier.Arity} {ν : RawClass},
      oneCtx υ ∋[ν] α → Sort u}
    (slot : motive (oneSlot υ))
    {α : depCarrier.Arity} {ν : RawClass}
    (x : oneCtx υ ∋[ν] α) : motive x := by
  have hα := oneSlot_arity υ x
  have hν := oneSlot_class υ x
  subst α
  subst ν
  have hx : x = oneSlot υ := by
    apply Subtype.ext
    apply Fin.ext
    have hlt := x.val.isLt
    have hslot : (oneSlot υ).val.val = 0 := rfl
    have hlen : (underlyingList (oneCtx υ)).length = 1 := by
      simp [oneCtx]
    rw [hslot]
    omega
  rw [hx]
  exact slot

private theorem emptyPath {Φ α : depCarrier.Arity} {υ : RawClass} :
    DecorationPath (C := depCarrier) 1 Φ α υ → False
  | .here x => depCarrier.unit_is_empty x
  | .nested x _ => depCarrier.unit_is_empty x

def oneDec (Ω : depCarrier.Arity) (υ : RawClass)
    (a : ClassifierAt bd
      (Ω ⋈ Precedence.before (oneSlot υ)) υ) :
    Decoration bd Ω (oneCtx υ) := by
  intro Φ α ν p
  cases p with
  | here x =>
      apply oneSlot_cases υ (motive := fun {α} {ν} x =>
        ClassifierAt bd (Ω ⋈ Precedence.before x ⋈ α) ν)
      exact a
  | nested x p =>
    have hα := oneSlot_arity υ x
    cases hα
    exact False.elim (emptyPath p)

def tyDec (Ω : depCarrier.Arity) :
    Decoration bd Ω (oneCtx .ty) :=
  oneDec Ω .ty PUnit.unit

def tyVar :
    Expr (C := depCarrier)
      (oneCtx .ty ⋈ Precedence.before (oneSlot .tm) ⋈ 1) .ty :=
  Expr.η (Γ := oneCtx .ty) (α := 1) (oneSlot .ty)

def tmDec :
    Decoration bd (oneCtx .ty) (oneCtx .tm) :=
  oneDec (oneCtx .ty) .tm tyVar

/-- A small rooted signature: the second symbol is classified by the first. -/
def toySig :
    DecoratedSignature (C := depCarrier) bd where
  arity := oneCtx .ty ⋈ oneCtx .tm
  decoration := Decoration.concatenate (tyDec 1) tmDec

/-- The decorated context corresponding to `A : Type, x : A`. -/
def ctx : DecoratedTelescope (C := depCarrier) bd 1 :=
  DecoratedTelescope.concatenate
    ⟨oneCtx .ty, tyDec 1⟩
    ⟨oneCtx .tm, tmDec⟩

def binArgs : depCarrier.Arity :=
  ofList (List.replicate 2 (nullary .ty))

def binEntry : Entry RawClass :=
  .mk (underlyingList binArgs) .ty

def binSig : depCarrier.Arity :=
  ofList [binEntry]

def binSlot : binSig ∋[.ty] binArgs :=
  ⟨⟨0, by decide⟩, by
    simp [binSig, binEntry, slotPredicate, Entry.arity,
      Entry.result]⟩

def binArg (j : Fin 2) :
    binArgs ∋[.ty] (1 : depCarrier.Arity) :=
  (positionCongr (slotPredicate 1 .ty)
    (show List.replicate 2 (nullary .ty) = underlyingList binArgs by
      simp [binArgs]))
    ⟨⟨j, by simp⟩, by
      have hentry :
          (List.replicate 2 (nullary .ty)).get ⟨j, by simp⟩ =
            nullary .ty := by
        apply List.eq_of_mem_replicate
        exact List.get_mem _ _
      rw [slotPredicate, hentry]
      exact ⟨underlyingList_one.symm, rfl⟩⟩

def binArg_cases
    {motive : ∀ {α : depCarrier.Arity} {υ : RawClass},
      binArgs ∋[υ] α → Sort u}
    (left : motive (binArg ⟨0, by decide⟩))
    (right : motive (binArg ⟨1, by decide⟩))
    {α : depCarrier.Arity} {υ : RawClass}
    (x : binArgs ∋[υ] α) : motive x := by
  have hα : α = 1 := by
    apply arity_ext
    have hentry : (underlyingList binArgs).get x.val =
        nullary .ty := by
      apply List.eq_of_mem_replicate (n := 2)
      simpa only [binArgs, underlyingList_ofList] using
        List.get_mem (underlyingList binArgs) x.val
    have hx := x.property.1
    rw [hentry] at hx
    have h : underlyingList α = [] := by
      simpa [nullary, Entry.arity] using hx.symm
    rw [h]
    exact underlyingList_one.symm
  have hυ : υ = .ty := by
    have hentry : (underlyingList binArgs).get x.val =
        nullary .ty := by
      apply List.eq_of_mem_replicate (n := 2)
      simpa only [binArgs, underlyingList_ofList] using
        List.get_mem (underlyingList binArgs) x.val
    have hx := x.property.2
    rw [hentry] at hx
    simpa [nullary, Entry.result] using hx.symm
  subst α
  subst υ
  let j : Fin 2 := ⟨x.val.val, by
    have hlt := x.val.isLt
    simpa [binArgs] using hlt⟩
  have hx : x = binArg j := by
    apply Subtype.ext
    apply Fin.ext
    rfl
  rw [hx]
  refine Fin.cases left (fun j => Fin.cases right (fun j => Fin.elim0 j) j) j

def extPrior : depCarrier.Arity :=
  binSig ⋈ oneCtx .ty ⋈ oneCtx .ty

def extTy : Expr (C := depCarrier) extPrior .ty :=
  Expr.η (Γ := extPrior) (α := 1)
    (depCarrier.inl (depCarrier.inr (oneSlot .ty)))

def priorTy : Expr (C := depCarrier) extPrior .ty :=
  Expr.η (Γ := extPrior) (α := 1)
    (depCarrier.inr (oneSlot .ty))

def binTy : Expr (C := depCarrier) extPrior .ty :=
  .ap (depCarrier.inl (depCarrier.inl binSlot))
    (fun {_} {_} x =>
      binArg_cases
        (motive := fun {Δ} {υ} _ => Expr (extPrior ⋈ Δ) υ)
        extTy priorTy x)

def extPriorDec :
    Decoration bd extPrior (oneCtx .tm) :=
  oneDec extPrior .tm binTy

def weakenExtPrior :
    extPrior →ʳ extPrior ⋈ oneCtx .ty :=
  fun ⦃_⦄ ⦃_⦄ x => depCarrier.inl x

def replacementTy :
    Expr (C := depCarrier) (binSig ⋈ oneCtx .ty) .ty :=
  Expr.η (Γ := binSig ⋈ oneCtx .ty) (α := 1)
    (depCarrier.inr (oneSlot .ty))

def extSubst :
    Subst (oneCtx .ty) (binSig ⋈ oneCtx .ty) :=
  fun {_} {_} x =>
    oneSlot_cases .ty
      (motive := fun {Δ} {υ} _ =>
        Expr (binSig ⋈ oneCtx .ty ⋈ Δ) υ)
      replacementTy x

def termTel : DecoratedTelescope (C := depCarrier) bd (oneCtx .ty) :=
  ⟨oneCtx .tm, tmDec⟩

def typeTel : DecoratedTelescope (C := depCarrier) bd 1 :=
  ⟨oneCtx .ty, tyDec 1⟩

def tailTy :
    DecoratedTelescope (C := depCarrier) bd (oneCtx .ty ⋈ oneCtx .tm) :=
  ⟨oneCtx .ty, tyDec (oneCtx .ty ⋈ oneCtx .tm)⟩

def extPriorTel : DecoratedTelescope (C := depCarrier) bd extPrior :=
  ⟨oneCtx .tm, extPriorDec⟩

def actedTermTel :
    DecoratedTelescope (C := depCarrier) bd (binSig ⋈ oneCtx .ty) :=
  DecoratedTelescope.act extSubst termTel

example : ctx.arity = oneCtx .ty ⋈ oneCtx .tm := rfl

/-- The generic T1 construction is literally a Mathlib internal monoid. -/
example : CategoryTheory.Mon (ArityMod (SyntaxMonad depCarrier)) :=
  ArityMod.DTelMon bd

example :
    MonObj.one (X := (ArityMod.DTelMon (C := depCarrier) bd).X) =
      ArityMod.DTelOne (C := depCarrier) bd :=
  ArityMod.DTelMon_one (C := depCarrier) bd

example :
    MonObj.mul (X := (ArityMod.DTelMon (C := depCarrier) bd).X) =
      ArityMod.DTelMul (C := depCarrier) bd :=
  ArityMod.DTelMon_mul (C := depCarrier) bd

example :
    (ArityMod.DTelOne bd).left.app
      (RelativeMonad.Kleisli.of (SyntaxMonad depCarrier) 1) PUnit.unit =
      DecoratedTelescope.empty (C := depCarrier) bd 1 := rfl

example :
    (ArityMod.DTelMul bd).left.app
        (RelativeMonad.Kleisli.of (SyntaxMonad depCarrier) 1)
        ⟨typeTel, termTel⟩ =
      DecoratedTelescope.concatenate (C := depCarrier) typeTel termTel := rfl

example :
    DecoratedTelescope.concatenate ctx
        (DecoratedTelescope.empty bd (1 ⋈ ctx.arity)) = ctx :=
  DecoratedTelescope.concatenate_empty_right ctx

example :
    DecoratedTelescope.concatenate
        (DecoratedTelescope.concatenate typeTel termTel)
        (DecoratedTelescope.castBase
          (mul_assoc 1 typeTel.arity termTel.arity) tailTy) =
      DecoratedTelescope.concatenate typeTel
        (DecoratedTelescope.concatenate termTel tailTy) :=
  DecoratedTelescope.concatenate_assoc typeTel termTel tailTy

example :
    DecoratedTelescope.act extSubst
        (DecoratedTelescope.concatenate termTel tailTy) =
      DecoratedTelescope.concatenate
        (DecoratedTelescope.act extSubst termTel)
        (DecoratedTelescope.act (Subst.lift extSubst termTel.arity) tailTy) :=
  DecoratedTelescope.act_concatenate extSubst termTel tailTy

example : toySig.arity = oneCtx .ty ⋈ oneCtx .tm := rfl

example :
    Decoration.classifier toySig.decoration
      (depCarrier.inr (oneSlot .tm) :
        oneCtx .ty ⋈ oneCtx .tm ∋[.tm] 1) =
      ClassifierAt.cast
        (congrArg (fun Λ => 1 ⋈ Λ ⋈ 1)
          (Precedence.before_inr (C := depCarrier)
            (Γ := oneCtx .ty) (oneSlot .tm)).symm)
        (tmDec (.here (oneSlot .tm))) := by
  simpa only [toySig, Decoration.classifier] using
    Decoration.concatenate_here_inr (tyDec 1) tmDec (oneSlot .tm)

example :
    Decoration.classifier tmDec (oneSlot .tm) = tyVar := rfl

example :
    Decoration.classifier ctx.decoration
      (depCarrier.inr (oneSlot .tm) :
        oneCtx .ty ⋈ oneCtx .tm ∋[.tm] 1) =
      ClassifierAt.cast
        (congrArg (fun Λ => 1 ⋈ Λ ⋈ 1)
          (Precedence.before_inr (C := depCarrier)
            (Γ := oneCtx .ty) (oneSlot .tm)).symm)
        (tmDec (.here (oneSlot .tm))) := by
  simpa only [Decoration.classifier, ctx,
    DecoratedTelescope.concatenate] using
    Decoration.concatenate_here_inr (tyDec 1) tmDec (oneSlot .tm)

example :
    Decoration.classifier extPriorDec (oneSlot .tm) = binTy := rfl

example : Decoration.rename (𝟙ʳ extPrior) extPriorDec = extPriorDec :=
  Decoration.rename_id _

example :
    Decoration.classifier
      (Decoration.rename weakenExtPrior extPriorDec)
      (oneSlot .tm) =
    ClassifierAt.rename
      (C := depCarrier) (bd := bd) (τ := .tm)
      ((weakenExtPrior ⇑ʳ Precedence.before (oneSlot .tm)) ⇑ʳ 1)
      binTy := rfl

example :
    Decoration.classifier
      (Decoration.substitute (Φ := oneCtx .ty)
        extSubst extPriorDec)
      (oneSlot .tm) =
    ClassifierAt.substitute (Φ := oneCtx .ty ⋈
      Precedence.before (oneSlot .tm) ⋈ 1)
      (C := depCarrier) (bd := bd) (τ := .tm)
      extSubst binTy := rfl

example :
    termTel =
      (⟨oneCtx .tm, tmDec⟩ :
        (DTel (C := depCarrier) bd).obj
          (RelativeMonad.Kleisli.of (SyntaxMonad depCarrier) (oneCtx .ty))) :=
  rfl

example :
    (RelativeMonad.LeftModule.act (DTel (C := depCarrier) bd) extSubst)
        termTel = actedTermTel :=
  rfl

example :
    Decoration.classifier actedTermTel.decoration (oneSlot .tm) =
      replacementTy := by
  unfold actedTermTel DecoratedTelescope.act Decoration.act
  unfold Decoration.classifier Decoration.substitute ClassifierAt.substitute
  simp only [bd]
  apply act_η

example :
    (RelativeMonad.LeftModule.act (DTel (C := depCarrier) bd)
        (Subst.ofRenaming weakenExtPrior)) extPriorTel =
      DecoratedTelescope.rename weakenExtPrior extPriorTel :=
  DecoratedTelescope.act_ofRenaming weakenExtPrior extPriorTel

example :
    Decoration.classifier
      (Decoration.act (Subst.ofRenaming weakenExtPrior) extPriorDec)
      (oneSlot .tm) =
    ClassifierAt.rename
      (C := depCarrier) (bd := bd) (τ := .tm)
      ((weakenExtPrior ⇑ʳ Precedence.before (oneSlot .tm)) ⇑ʳ 1)
      binTy := by
  rw [Decoration.act_ofRenaming]
  rfl

end T1
