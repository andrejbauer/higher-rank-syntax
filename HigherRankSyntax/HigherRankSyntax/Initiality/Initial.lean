import HigherRankSyntax.Initiality.Morphism
import HigherRankSyntax.Initiality.Uniqueness

/-!
# Initiality

For every model `M` there is exactly one morphism from `Ctx.model` to `M`, namely
`initialMorphism M`.
-/

universe v

namespace HrS

/-- The morphisms from `Ctx.model` to `M` are exactly `initialMorphism M`. -/
@[reducible]
def initial (M : Structure.{v}) : Unique (Morphism Ctx.model M) where
  default := initialMorphism M
  uniq F := Morphism.eq_of_ctx F _

end HrS
