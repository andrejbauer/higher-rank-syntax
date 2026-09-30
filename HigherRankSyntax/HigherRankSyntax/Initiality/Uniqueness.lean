import HigherRankSyntax.Ctx.Generation

/-!
# Uniqueness

Any two morphisms from `Ctx.model` to a model are equal.
-/

universe v

namespace HrS.Morphism

/-- Any two morphisms from `Ctx.model` to `M` are equal. -/
theorem eq_of_ctx {M : Structure.{v}} (F G : Morphism Ctx.model M) :
  F = G
  := by
  obtain ⟨hOb, hSub, hTy, hTm⟩ := Ctx.generated (agree_closed F G)
  apply ext hOb hSub hTy hTm

end HrS.Morphism
