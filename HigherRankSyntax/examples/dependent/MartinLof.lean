import ListCarrier
import HigherRankSyntax.Typing.Decoration

/-!
# Dependent sums as a decorated telescope

The theory

```
ty   : [ ]                                                     sort
tm   : [ A : Ty ]                                              sort
Σ    : [ A : Ty, B : [x : Tm A] Ty ]                           Ty
pair : [ A : Ty, B : [x : Tm A] Ty, a : Tm A, b : Tm (B a) ]   Tm (Σ A B)
fst  : [ A : Ty, B : [x : Tm A] Ty, p : Tm (Σ A B) ]           Tm A
snd  : [ A : Ty, B : [x : Tm A] Ty, p : Tm (Σ A B) ]           Tm (B (fst A B p))
```

over the list carrier.  Each boundary is stated at the context its slot's path
determines: the unit base, the part of the theory preceding the slot, and the
slot's own binding arity.

Every expression is built over that context presented as a literal list.  For
literal lists `ofList ℓ * ofList m` and `ofList (ℓ ++ m)` have the same normal
form, so the two presentations are definitionally equal and the boundaries need
no transport.
-/

namespace ListCarrier

/-- The slot of `Γ` at a given position. -/
def slot (Γ : aritySubmonoid) (k : ℕ) (hk : k < (underlyingList Γ).length) :
    Slot Γ (ofList ((underlyingList Γ).get ⟨k, hk⟩).arity) :=
  ⟨⟨k, hk⟩, by simp [slotPredicate]⟩

/-- An argument family given by position. -/
def args {Ω Γ : aritySubmonoid}
    (f : (i : Fin (underlyingList Γ).length) →
      Expr (C := listCarrier) (Ω ⋈ ofList ((underlyingList Γ).get i).arity)) :
    Expr.Args (C := listCarrier) Ω Γ :=
  fun ⦃Δ⦄ i =>
    (arity_ext (by simpa [slotPredicate] using i.property) :
      ofList ((underlyingList Γ).get i.val).arity = Δ) ▸ f i.val

/-- The slot at a given position of an arity presented by a literal list. -/
def slotOf (Ω : aritySubmonoid) (ℓ : List Entry) (h : underlyingList Ω = ℓ)
    (k : Fin ℓ.length) : Slot Ω (ofList (ℓ.get k).arity) := by
  subst h; exact ⟨k, by simp [slotPredicate]⟩

/-- An argument family for a binding arity presented by a literal list. -/
def argsOf {Ω Γ : aritySubmonoid} (ℓ : List Entry) (h : underlyingList Γ = ℓ)
    (f : (k : Fin ℓ.length) →
      Expr (C := listCarrier) (Ω ⋈ ofList (ℓ.get k).arity)) :
    Expr.Args (C := listCarrier) Ω Γ := by
  subst h; exact args f

/-- Concatenation of listed arities. -/
theorem ofList_append (ℓ m : List Entry) : ofList ℓ * ofList m = ofList (ℓ ++ m) := by
  apply arity_ext
  simp [underlyingList_mul]

/-- A rank-0 argument sits in the arity extended by nothing. -/
def keepNil {ℓ : List Entry} (e : Expr (C := listCarrier) (ofList ℓ)) :
    Expr (C := listCarrier) (ofList (ℓ ++ [])) :=
  cast (congrArg (fun m => Expr (C := listCarrier) (ofList m)) (List.append_nil ℓ).symm) e

/-- Apply the symbol at a position of a listed arity, its arguments written in
the arity extended by each argument's own binding arity. -/
def applyAt (ℓ : List Entry) (k : Fin ℓ.length)
    (f : (j : Fin (ℓ.get k).arity.length) →
      Expr (C := listCarrier) (ofList (ℓ ++ ((ℓ.get k).arity.get j).arity))) :
    Expr (C := listCarrier) (ofList ℓ) :=
  .ap (slotOf (ofList ℓ) ℓ (by simp) k)
    (argsOf (ℓ.get k).arity (by simp) (fun j =>
      cast (congrArg (Expr (C := listCarrier)) (ofList_append ℓ _).symm) (f j)))

/-- The symbol at a position of empty binding arity. -/
def varAt (ℓ : List Entry) (k : Fin ℓ.length)
    (h : (ℓ.get k).arity.length = 0 := by rfl) :
    Expr (C := listCarrier) (ofList ℓ) :=
  applyAt ℓ k (fun j => absurd (h.symm ▸ Nat.not_lt_zero j.val) (fun hn => hn j.isLt))

end ListCarrier

namespace MartinLof

open ListCarrier

/-! ### The entries -/

/-- The empty binding arity. -/
abbrev nil : Entry := .mk []

/-- A binding arity with one variable of empty arity. -/
abbrev unary : Entry := .mk [nil]

abbrev tyEntry : Entry := .mk []
abbrev tmEntry : Entry := .mk [nil]
abbrev sigmaEntry : Entry := .mk [nil, unary]
abbrev pairEntry : Entry := .mk [nil, unary, nil, nil]
abbrev fstEntry : Entry := .mk [nil, unary, nil]
abbrev sndEntry : Entry := .mk [nil, unary, nil]

/-- The underlying list of the theory. -/
abbrev theoryList : List Entry :=
  [tyEntry, tmEntry, sigmaEntry, pairEntry, fstEntry, sndEntry]

/-- The theory's arity. -/
abbrev theory : aritySubmonoid := ofList theoryList

/-! ### The declared slots -/

abbrev tySlot : Slot theory (ofList []) := slot theory 0 (by decide)
abbrev tmSlot : Slot theory (ofList [nil]) := slot theory 1 (by decide)
abbrev sigmaSlot : Slot theory (ofList [nil, unary]) := slot theory 2 (by decide)
abbrev pairSlot : Slot theory (ofList [nil, unary, nil, nil]) := slot theory 3 (by decide)
abbrev fstSlot : Slot theory (ofList [nil, unary, nil]) := slot theory 4 (by decide)
abbrev sndSlot : Slot theory (ofList [nil, unary, nil]) := slot theory 5 (by decide)

/-! ### The symbols

The theory prefix is a prefix of every boundary's scope, so `ty` sits at `0`,
`tm` at `1`, `Σ` at `2` and `fst` at `4` in all of them.  Each symbol is
therefore defined once, polymorphic in the trailing part of the scope, which is
inferred from its arguments.
-/

/-- `Ty`, in any scope beginning with `ty`. -/
def Ty {rest : List Entry} : Expr (C := listCarrier) (ofList (tyEntry :: rest)) :=
  varAt (tyEntry :: rest) ⟨0, by simp⟩

/-- `Tm a`, in any scope beginning with `ty, tm`. -/
def Tm {rest : List Entry}
    (a : Expr (C := listCarrier) (ofList (tyEntry :: tmEntry :: rest))) :
    Expr (C := listCarrier) (ofList (tyEntry :: tmEntry :: rest)) :=
  applyAt (tyEntry :: tmEntry :: rest) ⟨1, by simp⟩ (fun j => match j with
    | ⟨0, _⟩ => keepNil a
    | ⟨_ + 1, h⟩ => absurd h (by simp [Entry.arity]))

/-- `Σ a b`, in any scope beginning with `ty, tm, Σ`.  The second argument binds
one variable, so it is written in the scope extended by it. -/
def Sigma {rest : List Entry}
    (a : Expr (C := listCarrier) (ofList (tyEntry :: tmEntry :: sigmaEntry :: rest)))
    (b : Expr (C := listCarrier)
      (ofList ((tyEntry :: tmEntry :: sigmaEntry :: rest) ++ [nil]))) :
    Expr (C := listCarrier) (ofList (tyEntry :: tmEntry :: sigmaEntry :: rest)) :=
  applyAt (tyEntry :: tmEntry :: sigmaEntry :: rest) ⟨2, by simp⟩ (fun j => match j with
    | ⟨0, _⟩ => keepNil a
    | ⟨1, _⟩ => b
    | ⟨_ + 2, h⟩ => absurd h (by simp [Entry.arity]))

/-- `fst a b p`, in any scope beginning with `ty, tm, Σ, pair, fst`. -/
def Fst {rest : List Entry}
    (a : Expr (C := listCarrier)
      (ofList (tyEntry :: tmEntry :: sigmaEntry :: pairEntry :: fstEntry :: rest)))
    (b : Expr (C := listCarrier)
      (ofList ((tyEntry :: tmEntry :: sigmaEntry :: pairEntry :: fstEntry :: rest) ++ [nil])))
    (p : Expr (C := listCarrier)
      (ofList (tyEntry :: tmEntry :: sigmaEntry :: pairEntry :: fstEntry :: rest))) :
    Expr (C := listCarrier)
      (ofList (tyEntry :: tmEntry :: sigmaEntry :: pairEntry :: fstEntry :: rest)) :=
  applyAt (tyEntry :: tmEntry :: sigmaEntry :: pairEntry :: fstEntry :: rest)
    ⟨4, by simp⟩ (fun j => match j with
      | ⟨0, _⟩ => keepNil a
      | ⟨1, _⟩ => b
      | ⟨2, _⟩ => keepNil p
      | ⟨_ + 3, h⟩ => absurd h (by simp [Entry.arity]))

/-! ### The boundaries -/

/-- `ty` is a sort. -/
def tyBoundary : Boundary (C := listCarrier) (before tySlot * ofList []) :=
  .sort

/-- `tm` is a sort. -/
def tmBoundary : Boundary (C := listCarrier) (before tmSlot * ofList [nil]) :=
  .sort

/-- The scope of `Σ`'s boundary: `ty, tm, A, B`. -/
abbrev sigmaList : List Entry := [tyEntry, tmEntry, nil, unary]

/-- `Σ` is a type. -/
def sigmaBoundary :
    Boundary (C := listCarrier) (before sigmaSlot * ofList [nil, unary]) :=
  .of (Ty (rest := [tmEntry, nil, unary]))

/-- The scope of `pair`'s boundary: `ty, tm, Σ, A, B, a, b`. -/
abbrev pairList : List Entry :=
  [tyEntry, tmEntry, sigmaEntry, nil, unary, nil, nil]

/-- `pair` is a term of type `Σ A B`. -/
def pairBoundary :
    Boundary (C := listCarrier) (before pairSlot * ofList [nil, unary, nil, nil]) :=
  let A := varAt pairList ⟨3, by decide⟩
  let Bx := applyAt (pairList ++ [nil]) ⟨4, by decide⟩ (fun j => match j with
    | ⟨0, _⟩ => keepNil (varAt (pairList ++ [nil]) ⟨7, by decide⟩)
    | ⟨_ + 1, h⟩ => absurd h (by simp [Entry.arity]))
  .of (Tm (Sigma A Bx))

/-- The scope of `fst`'s boundary: `ty, tm, Σ, pair, A, B, p`. -/
abbrev fstList : List Entry :=
  [tyEntry, tmEntry, sigmaEntry, pairEntry, nil, unary, nil]

/-- `fst` is a term of type `A`. -/
def fstBoundary :
    Boundary (C := listCarrier) (before fstSlot * ofList [nil, unary, nil]) :=
  let A := varAt fstList ⟨4, by decide⟩
  .of (Tm A)

/-- The scope of `snd`'s boundary: `ty, tm, Σ, pair, fst, A, B, p`. -/
abbrev sndList : List Entry :=
  [tyEntry, tmEntry, sigmaEntry, pairEntry, fstEntry, nil, unary, nil]

/-- `snd` is a term of type `B (fst A B p)`. -/
def sndBoundary :
    Boundary (C := listCarrier) (before sndSlot * ofList [nil, unary, nil]) :=
  let A := varAt sndList ⟨5, by decide⟩
  let p := varAt sndList ⟨7, by decide⟩
  let B : Expr (C := listCarrier) (ofList sndList) →
      Expr (C := listCarrier) (ofList sndList) :=
    fun e => applyAt sndList ⟨6, by decide⟩ (fun j => match j with
      | ⟨0, _⟩ => keepNil e
      | ⟨_ + 1, h⟩ => absurd h (by simp [Entry.arity]))
  let Bx := applyAt (sndList ++ [nil]) ⟨6, by decide⟩ (fun j => match j with
    | ⟨0, _⟩ => keepNil (varAt (sndList ++ [nil]) ⟨8, by decide⟩)
    | ⟨_ + 1, h⟩ => absurd h (by simp [Entry.arity]))
  .of (Tm (B (Fst A Bx p)))

end MartinLof
