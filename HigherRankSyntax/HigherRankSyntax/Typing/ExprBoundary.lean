import HigherRankSyntax.Typing.DecorationModule

/-!
# The boundary of an expression

Over an ambient, every expression has a boundary: the declaration of its head,
weakened into the whole ambient and instantiated by the head's arguments.  This
is not a recursion — only the head is inspected — and it is total, a decoration
giving a boundary to every slot.
-/

variable {A : Type} {C : Carrier A}

namespace dTel

/-- The boundary of an expression over an ambient. -/
def boundaryOf (Ξ : Ambient C) : Expr Ξ.arity → Bd Ξ.arity
  | .ap (α := α) x args =>
      Bd.instantiate args (Bd.rename (Ξ.inclusion x ⇑ʳ α) (Ξ.boundary x))

@[simp] theorem boundaryOf_ap (Ξ : Ambient C) {α : C.Arity}
    (x : Ξ.arity ∋ α) (args : Subst α Ξ.arity) :
  Ξ.boundaryOf (.ap x args)
    = Bd.instantiate args (Bd.rename (Ξ.inclusion x ⇑ʳ α) (Ξ.boundary x))
  := rfl

section SmokeTests

/-- The arguments of an application are a substitution filling the telescope its
head binds, weakened into the ambient. -/
example (Ξ : Ambient C) {α : C.Arity} (x : Ξ.arity ∋ α) (args : Subst α Ξ.arity) :
    Subst ((Ξ.binding x).rename (Ξ.inclusion x)).arity Ξ.arity :=
  args

end SmokeTests

end dTel
