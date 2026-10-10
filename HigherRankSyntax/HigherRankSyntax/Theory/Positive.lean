import HigherRankSyntax.Ctx.Inversion
import HigherRankSyntax.Theory.Basic

/-!
# Positivity

`Theory.PositiveEntry T X a` says that the type `a` over `X.left` is positive: it is the type
of the elements of a sort, the equation between two elements of a sort, or `Bind a' c` for
`a'` admissible and positive over `X` and `c` positive over the extension of `X.left` by `a'`.

`Theory.PositiveBinding T X a` says that the binders of `a` are positive: `a` is `U`, the
type of the elements of a sort, the equation between two sorts or between two elements of a
sort, or `Bind a' c` for `a'` positive over `X` and `c` with positive binders over the
extension of `X.left` by `a'`.

A theory is positive when the type of every slot of its signature has positive binders and
every admissible type is positive.

`Theory.PositiveChain κ c` says that every type of the chain `c` over `Y` is positive over the
extension of `Y` by the types before it, mapped to the signature by the projections followed
by `κ`. In a positive theory, every chain of admissible types is a chain of positive types.
-/

open CategoryTheory

namespace Theory

/-- The positive types over `X.left`: the types of the elements of a sort, the equations
between two elements of a sort, and `Bind a c` for `a` admissible and positive over `X` and
`c` positive over the extension of `X.left` by `a`. -/
inductive PositiveEntry (T : Theory) : (X : Over T.signature.toOb) → Ctx.model.Ty X.left → Prop
  /-- The type of the elements of the sort `S`. -/
  | el (X : Over T.signature.toOb) (S : Ctx.model.Tm X.left (Ctx.model.U X.left)) :
      PositiveEntry T X (Ctx.model.El S)
  /-- The equation between two elements of a sort. -/
  | idElement (X : Over T.signature.toOb) {S : Ctx.model.Tm X.left (Ctx.model.U X.left)}
      (l r : Ctx.model.Tm X.left (Ctx.model.El S)) :
      PositiveEntry T X (Ctx.model.IdElement l r)
  /-- `c` bound over `a`. -/
  | bind (X : Over T.signature.toOb) {a : Ctx.model.Ty X.left}
      {c : Ctx.model.Ty (Ctx.model.extend X.left a)} :
      T.admissible X a → PositiveEntry T X a →
      PositiveEntry T (Over.mk (Ctx.model.projection a ≫ X.hom)) c →
      PositiveEntry T X (Ctx.model.Bind a c)

/-- The types over `X.left` whose binders are positive: `U`, the types of the elements of a
sort, the equations between two sorts or between two elements of a sort, and `Bind a c` for
`a` positive over `X` and `c` with positive binders over the extension of `X.left` by `a`. -/
inductive PositiveBinding (T : Theory) :
    (X : Over T.signature.toOb) → Ctx.model.Ty X.left → Prop
  /-- The type of sorts. -/
  | sort (X : Over T.signature.toOb) : PositiveBinding T X (Ctx.model.U X.left)
  /-- The type of the elements of the sort `S`. -/
  | el (X : Over T.signature.toOb) (S : Ctx.model.Tm X.left (Ctx.model.U X.left)) :
      PositiveBinding T X (Ctx.model.El S)
  /-- The equation between two sorts. -/
  | idSort (X : Over T.signature.toOb) (S S' : Ctx.model.Tm X.left (Ctx.model.U X.left)) :
      PositiveBinding T X (Ctx.model.IdSort S S')
  /-- The equation between two elements of a sort. -/
  | idElement (X : Over T.signature.toOb) {S : Ctx.model.Tm X.left (Ctx.model.U X.left)}
      (l r : Ctx.model.Tm X.left (Ctx.model.El S)) :
      PositiveBinding T X (Ctx.model.IdElement l r)
  /-- `c` bound over `a`. -/
  | bind (X : Over T.signature.toOb) {a : Ctx.model.Ty X.left}
      {c : Ctx.model.Ty (Ctx.model.extend X.left a)} :
      T.PositiveEntry X a → PositiveBinding T (Over.mk (Ctx.model.projection a ≫ X.hom)) c →
      PositiveBinding T X (Ctx.model.Bind a c)

/-- Every slot of the signature has positive binders, and every admissible type is
positive. -/
structure Positive (T : Theory) : Prop where
  /-- The type of every slot of the signature has positive binders. -/
  slot : ∀ ⦃α : C.Arity⦄ (x : T.signature.arity ∋ α),
    T.PositiveBinding (Over.mk (𝟙 T.signature.toOb)) (T.signature.entry x)
  /-- Every admissible type is positive. -/
  admissible : ∀ {X : Over T.signature.toOb} {a : Ctx.model.Ty X.left},
    T.admissible X a → T.PositiveEntry X a

/-- Every type of the chain `c` is positive over the extension of `Y` by the types before
it, mapped to the signature by the projections followed by `κ`. -/
def PositiveChain (T : Theory) : {Y : Ctx.Ob} → {Ω : C.Arity} →
    (Y ⟶ T.signature.toOb) → HrS.Chain Ctx.model Y Ω → Prop
  | _, _, _, .nil => True
  | _, _, κ, .cons a c => T.PositiveEntry (Over.mk κ) a ∧
      PositiveChain T (Ctx.model.projection a ≫ κ) c

/-- In a positive theory, every chain of admissible types is a chain of positive types. -/
theorem Positive.positiveChain {T : Theory} (hT : T.Positive) :
    ∀ {Y : Ctx.Ob} {Ω : C.Arity} {κ : Y ⟶ T.signature.toOb} {c : HrS.Chain Ctx.model Y Ω},
      T.AdmissibleChain κ c → T.PositiveChain κ c
  | _, _, _, .nil, _ => trivial
  | _, _, _, .cons _ _, h => ⟨hT.admissible h.1, Positive.positiveChain hT h.2⟩

/-- A positive type `Bind a c` binds a type `a` admissible and positive over `X` over a type
`c` positive over the extension of `X.left` by `a`. -/
theorem PositiveEntry.bind_inv {T : Theory} {X : Over T.signature.toOb}
    {a : Ctx.model.Ty X.left} {c : Ctx.model.Ty (Ctx.model.extend X.left a)}
    (h : T.PositiveEntry X (Ctx.model.Bind a c)) :
  T.admissible X a ∧ T.PositiveEntry X a ∧
    T.PositiveEntry (Over.mk (Ctx.model.projection a ≫ X.hom)) c
  := by
  generalize hb : Ctx.model.Bind a c = b at h
  cases h with
  | el _ S =>
    exact absurd hb (Ctx.Bind_ne_El a c S)
  | idElement _ l r =>
    exact absurd hb (Ctx.Bind_ne_IdElement a c l r)
  | bind _ ha hpa hpc =>
    obtain ⟨rfl, hc⟩ := Ctx.Bind_injective hb
    obtain rfl := eq_of_heq hc
    exact ⟨ha, hpa, hpc⟩

/-- A type `Bind a c` with positive binders binds a positive type `a` over a type `c` with
positive binders over the extension of `X.left` by `a`. -/
theorem PositiveBinding.bind_inv {T : Theory} {X : Over T.signature.toOb}
    {a : Ctx.model.Ty X.left} {c : Ctx.model.Ty (Ctx.model.extend X.left a)}
    (h : T.PositiveBinding X (Ctx.model.Bind a c)) :
  T.PositiveEntry X a ∧ T.PositiveBinding (Over.mk (Ctx.model.projection a ≫ X.hom)) c
  := by
  generalize hb : Ctx.model.Bind a c = b at h
  cases h with
  | sort _ =>
    exact absurd hb (Ctx.Bind_ne_U a c)
  | el _ S =>
    exact absurd hb (Ctx.Bind_ne_El a c S)
  | idSort _ S S' =>
    exact absurd hb (Ctx.Bind_ne_IdSort a c S S')
  | idElement _ l r =>
    exact absurd hb (Ctx.Bind_ne_IdElement a c l r)
  | bind _ hpa hpc =>
    obtain ⟨rfl, hc⟩ := Ctx.Bind_injective hb
    obtain rfl := eq_of_heq hc
    exact ⟨hpa, hpc⟩

/-- The type of sorts is not positive. -/
theorem PositiveEntry.not_U {T : Theory} {X : Over T.signature.toOb} :
  ¬ T.PositiveEntry X (Ctx.model.U X.left)
  := by
  intro h
  generalize hb : Ctx.model.U X.left = b at h
  cases h with
  | el _ S =>
    exact Ctx.U_ne_El S hb
  | idElement _ l r =>
    exact Ctx.U_ne_IdElement l r hb
  | bind _ _ _ _ =>
    apply Ctx.Bind_ne_U _ _
    symm
    exact hb

/-- An equation between two sorts is not positive. -/
theorem PositiveEntry.not_IdSort {T : Theory} {X : Over T.signature.toOb}
    {S S' : Ctx.model.Tm X.left (Ctx.model.U X.left)} :
  ¬ T.PositiveEntry X (Ctx.model.IdSort S S')
  := by
  intro h
  generalize hb : Ctx.model.IdSort S S' = b at h
  cases h with
  | el _ S'' =>
    exact Ctx.IdSort_ne_El S S' S'' hb
  | idElement _ l r =>
    exact Ctx.IdSort_ne_IdElement S S' l r hb
  | bind _ _ _ _ =>
    apply Ctx.Bind_ne_IdSort _ _ S S'
    symm
    exact hb

end Theory
