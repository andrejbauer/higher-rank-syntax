import MagmaSignature

/-!
# Classical magma terms

`MagmaTerm n` is the ordinary binary-tree syntax in `n` variables.
-/

namespace Magmas

/-- Raw terms over one binary operation and `n` variables. -/
inductive MagmaTerm (n : ℕ) where
  | variable : Fin n → MagmaTerm n
  | multiplication : MagmaTerm n → MagmaTerm n → MagmaTerm n

/-- Simultaneous substitution of magma terms. -/
def magmaSubstitution {n m : ℕ}
    (σ : Fin n → MagmaTerm m) : MagmaTerm n → MagmaTerm m
  | .variable j => σ j
  | .multiplication e f => .multiplication (magmaSubstitution σ e) (magmaSubstitution σ f)

/-- There are no closed terms in a magma signature without constants. -/
private def noClosedMagmaTerm : MagmaTerm 0 → Empty
  | .variable j => Fin.elim0 j
  | .multiplication e _ => noClosedMagmaTerm e

instance magmaTermZeroIsEmpty : IsEmpty (MagmaTerm 0) where
  false e := (noClosedMagmaTerm e).elim

end Magmas
