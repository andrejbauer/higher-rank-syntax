import HigherRankSyntax.Carrier
import HigherRankSyntax.Renaming
import HigherRankSyntax.Expr
import HigherRankSyntax.Subst
import HigherRankSyntax.RelativeMonad.Basic
import HigherRankSyntax.RelativeMonad.Kleisli
import HigherRankSyntax.RelativeMonad.Module
import HigherRankSyntax.RelativeMonad.ArityModule
import HigherRankSyntax.RelativeMonad.ArityModuleTensor
import HigherRankSyntax.SyntaxMonad
import HigherRankSyntax.Typing.Boundary
import HigherRankSyntax.Typing.Telescope
import HigherRankSyntax.Typing.Rules
import HigherRankSyntax.Typing.Weakening
import HigherRankSyntax.Typing.Eta
import HigherRankSyntax.Typing.SubstitutionLemma
import HigherRankSyntax.Typing.Invariance

#print axioms ListCarrier.aritySubmonoid
#print axioms ListCarrier.positionWellOrder
#print axioms ListCarrier.positionEmbedding
#print axioms ListCarrier.slotAppend
#print axioms ListCarrier.before_after
#print axioms ListCarrier.localized
#print axioms ListCarrier.reinject
#print axioms ListCarrier.before_inl
#print axioms ListCarrier.after_inl
#print axioms ListCarrier.before_inr
#print axioms ListCarrier.after_inr
#print axioms ListCarrier.before_of_lt
#print axioms ListCarrier.sub_sizeOf
#print axioms ListCarrier.sizeOf_take_lt
