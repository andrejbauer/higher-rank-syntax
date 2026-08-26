import ListCarrier
import HigherRankSyntax.Typing.DecoratedTelescopeMonoid

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

over the list carrier, first as six boundaries and then as a theory assembled by
dependent concatenation.

Every context is presented by a literal list.  For literal lists
`ofList ℓ * ofList m` and `ofList (ℓ ++ m)` have the same normal form, so the
two presentations are definitionally equal, no boundary needs a transport, and
a symbol's trailing scope is inferred rather than annotated.  Only variables
carry positions, since a variable's index genuinely depends on its scope.
-/

namespace ListCarrier

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

@[simp] theorem ofList_nil : ofList [] = (1 : aritySubmonoid) := rfl

@[simp] theorem carrier_before {Γ α : aritySubmonoid} (x : Slot Γ α) :
    listCarrier.before x = before x := rfl

@[simp] theorem underlyingList_before {Γ α : aritySubmonoid} (x : Slot Γ α) :
    underlyingList (before x) = (underlyingList Γ).take x.val.val := by
  simp [before]

/-- The decoration of a one-entry arity. -/
def singleDecoration {Ω : aritySubmonoid} (e : Entry)
    (bnd : Bd (C := listCarrier) (Ω ⋈ 1 ⋈ ofList e.arity))
    (nest : Decoration (C := listCarrier) (Ω ⋈ 1) (ofList e.arity)) :
    Decoration (C := listCarrier) Ω (ofList [e])
  | _, α, .here x => by
      have hα : ofList e.arity = α :=
        arity_ext (by simpa [slotPredicate] using x.property)
      exact Bd.cast (arity_ext (by
        simp [ListCarrier.before, ← hα]
        rfl)) bnd
  | _, α, .nested x q => by
      have hβ : ofList e.arity = _ :=
        arity_ext (by simpa [slotPredicate] using x.property)
      exact Bd.cast (arity_ext (by
        simp [ListCarrier.before]
        rfl)) (nest (hβ ▸ q))

/-- A decorated telescope whose base and whose own arity are both presented by
literal lists.  Every context a declaration mentions is then a literal list, so
the trailing scope of a symbol is inferred rather than annotated. -/
structure ListTelescope (base : List Entry) where
  /-- The slots, listed. -/
  list : List Entry
  /-- Their boundaries. -/
  decoration : Decoration (C := listCarrier) (ofList base) (ofList list)

namespace ListTelescope

/-- The empty telescope. -/
@[reducible] def empty (base : List Entry) : ListTelescope base where
  list := []
  decoration := Decoration.empty _

/-- A declaration: a decorated binding arity together with a boundary written
over it.  Its arguments are themselves declarations. -/
@[reducible] def decl {base : List Entry} (args : ListTelescope base)
    (bnd : Bd (C := listCarrier) (ofList (base ++ args.list))) :
    ListTelescope base where
  list := [.mk args.list]
  decoration :=
    singleDecoration (.mk args.list)
      (Bd.cast (ofList_append base args.list).symm bnd) args.decoration

/-- Two consecutive segments, the second written over the base extended by the
first. -/
@[reducible] def concat {base : List Entry} (Γ : ListTelescope base)
    (Δ : ListTelescope (base ++ Γ.list)) : ListTelescope base where
  list := Γ.list ++ Δ.list
  decoration :=
    cast (congrArg (fun Λ => Decoration (C := listCarrier) (ofList base) Λ)
        (ofList_append Γ.list Δ.list))
      (Decoration.concatenate Γ.decoration
        (cast (congrArg (fun Ω => Decoration (C := listCarrier) Ω (ofList Δ.list))
            (ofList_append base Γ.list).symm) Δ.decoration))

/-- The decorated telescope it presents. -/
def toTelescope {base : List Entry} (T : ListTelescope base) :
    dTel (C := listCarrier) (ofList base) where
  arity := ofList T.list
  decoration := T.decoration

end ListTelescope

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

/-! ### The scopes of the declarations' own boundaries -/

/-- The scope of `pair`'s boundary: `ty, tm, Σ, A, B, a, b`. -/
abbrev pairList : List Entry :=
  [tyEntry, tmEntry, sigmaEntry, nil, unary, nil, nil]

/-- The scope of `fst`'s boundary: `ty, tm, Σ, pair, A, B, p`. -/
abbrev fstList : List Entry :=
  [tyEntry, tmEntry, sigmaEntry, pairEntry, nil, unary, nil]

/-- The scope of `snd`'s boundary: `ty, tm, Σ, pair, fst, A, B, p`. -/
abbrev sndList : List Entry :=
  [tyEntry, tmEntry, sigmaEntry, pairEntry, fstEntry, nil, unary, nil]

/-! ### Declarations

A declaration is a one-entry decorated telescope over everything declared
before it: its own boundary, and a decoration of its binding arity giving the
boundary of each argument.  Declarations are glued by dependent concatenation,
so a theory is built exactly as it is written.
-/

/-- `ty : [ ] sort` -/
def tyDecl : ListTelescope [] :=
  .decl (.empty _) .sort

/-- `tm : [ A : Ty ] sort` -/
def tmDecl : ListTelescope [tyEntry] :=
  .decl (.decl (.empty _) (.of Ty)) .sort

/-- `Σ : [ A : Ty, B : [x : Tm A] Ty ] Ty` -/
def sigmaDecl : ListTelescope [tyEntry, tmEntry] :=
  let A := varAt [tyEntry, tmEntry, nil] ⟨2, by decide⟩
  .decl (.concat (.decl (.empty _) (.of Ty))
                 (.decl (.decl (.empty _) (.of (Tm A))) (.of Ty)))
        (.of Ty)

/-- `pair : [ A : Ty, B : [x : Tm A] Ty, a : Tm A, b : Tm (B a) ] Tm (Σ A B)` -/
def pairDecl : ListTelescope [tyEntry, tmEntry, sigmaEntry] :=
  let A₁ := varAt [tyEntry, tmEntry, sigmaEntry, nil] ⟨3, by decide⟩
  let A₂ := varAt [tyEntry, tmEntry, sigmaEntry, nil, unary] ⟨3, by decide⟩
  let Ba := applyAt [tyEntry, tmEntry, sigmaEntry, nil, unary, nil] ⟨4, by decide⟩
    (fun j => match j with
      | ⟨0, _⟩ => keepNil (varAt [tyEntry, tmEntry, sigmaEntry, nil, unary, nil]
          ⟨5, by decide⟩)
      | ⟨_ + 1, h⟩ => absurd h (by simp [Entry.arity]))
  let A₃ := varAt pairList ⟨3, by decide⟩
  let Bx := applyAt (pairList ++ [nil]) ⟨4, by decide⟩ (fun j => match j with
    | ⟨0, _⟩ => keepNil (varAt (pairList ++ [nil]) ⟨7, by decide⟩)
    | ⟨_ + 1, h⟩ => absurd h (by simp [Entry.arity]))
  .decl (.concat (.decl (.empty _) (.of Ty))
        (.concat (.decl (.decl (.empty _) (.of (Tm A₁))) (.of Ty))
        (.concat (.decl (.empty _) (.of (Tm A₂)))
                 (.decl (.empty _) (.of (Tm Ba))))))
        (.of (Tm (Sigma A₃ Bx)))

/-- `fst : [ A : Ty, B : [x : Tm A] Ty, p : Tm (Σ A B) ] Tm A` -/
def fstDecl : ListTelescope [tyEntry, tmEntry, sigmaEntry, pairEntry] :=
  let A₁ := varAt [tyEntry, tmEntry, sigmaEntry, pairEntry, nil] ⟨4, by decide⟩
  let A₂ := varAt [tyEntry, tmEntry, sigmaEntry, pairEntry, nil, unary] ⟨4, by decide⟩
  let Bx := applyAt [tyEntry, tmEntry, sigmaEntry, pairEntry, nil, unary, nil]
    ⟨5, by decide⟩ (fun j => match j with
      | ⟨0, _⟩ => keepNil (varAt [tyEntry, tmEntry, sigmaEntry, pairEntry, nil, unary, nil]
          ⟨6, by decide⟩)
      | ⟨_ + 1, h⟩ => absurd h (by simp [Entry.arity]))
  .decl (.concat (.decl (.empty _) (.of Ty))
        (.concat (.decl (.decl (.empty _) (.of (Tm A₁))) (.of Ty))
                 (.decl (.empty _) (.of (Tm (Sigma A₂ Bx))))))
        (.of (Tm (varAt fstList ⟨4, by decide⟩)))

/-- `snd : [ A : Ty, B : [x : Tm A] Ty, p : Tm (Σ A B) ] Tm (B (fst A B p))` -/
def sndDecl : ListTelescope [tyEntry, tmEntry, sigmaEntry, pairEntry, fstEntry] :=
  let A₁ := varAt [tyEntry, tmEntry, sigmaEntry, pairEntry, fstEntry, nil] ⟨5, by decide⟩
  let A₂ := varAt [tyEntry, tmEntry, sigmaEntry, pairEntry, fstEntry, nil, unary]
    ⟨5, by decide⟩
  let Bx := applyAt [tyEntry, tmEntry, sigmaEntry, pairEntry, fstEntry, nil, unary, nil]
    ⟨6, by decide⟩ (fun j => match j with
      | ⟨0, _⟩ => keepNil (varAt
          [tyEntry, tmEntry, sigmaEntry, pairEntry, fstEntry, nil, unary, nil]
          ⟨7, by decide⟩)
      | ⟨_ + 1, h⟩ => absurd h (by simp [Entry.arity]))
  let A₃ := varAt sndList ⟨5, by decide⟩
  let p := varAt sndList ⟨7, by decide⟩
  let B : Expr (C := listCarrier) (ofList sndList) →
      Expr (C := listCarrier) (ofList sndList) :=
    fun e => applyAt sndList ⟨6, by decide⟩ (fun j => match j with
      | ⟨0, _⟩ => keepNil e
      | ⟨_ + 1, h⟩ => absurd h (by simp [Entry.arity]))
  let Bxx := applyAt (sndList ++ [nil]) ⟨6, by decide⟩ (fun j => match j with
    | ⟨0, _⟩ => keepNil (varAt (sndList ++ [nil]) ⟨8, by decide⟩)
    | ⟨_ + 1, h⟩ => absurd h (by simp [Entry.arity]))
  .decl (.concat (.decl (.empty _) (.of Ty))
        (.concat (.decl (.decl (.empty _) (.of (Tm A₁))) (.of Ty))
                 (.decl (.empty _) (.of (Tm (Sigma A₂ Bx))))))
        (.of (Tm (B (Fst A₃ Bxx p))))

/-- The theory of dependent sums, assembled by dependent concatenation. -/
def sigmaTheory : Ambient listCarrier :=
  (ListTelescope.concat tyDecl
    (.concat tmDecl
      (.concat sigmaDecl
        (.concat pairDecl
          (.concat fstDecl sndDecl))))).toTelescope

/-- Each declaration builds the entry it is named for, and the assembled theory
is the flat one. -/
example : tyDecl.list = [tyEntry] := rfl
example : tmDecl.list = [tmEntry] := rfl
example : sigmaDecl.list = [sigmaEntry] := rfl
example : pairDecl.list = [pairEntry] := rfl
example : fstDecl.list = [fstEntry] := rfl
example : sndDecl.list = [sndEntry] := rfl
example : sigmaTheory.arity = theory := rfl

end MartinLof
