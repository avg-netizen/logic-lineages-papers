module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedMultisetNumeric
open OriginalHereditaryAgendaDefinitions OriginalHereditarySettledObserverDefinitions
open OriginalHereditaryExpectedDefinitions
def Deterministic : Prop := ∀ n (arity : Fin n → Nat) R c a v w,
 Expected arity R c a v → Expected arity R c a w → v = w
def ArgumentsJointDepth : Prop := ∀ R n (arity : Fin n → Nat) (Gamma types : List Ty)
 c (args : AuxArguments (Fin n) arity Gamma types) depth,
 argumentDepth args ≤ depth →
 OriginalRootObservation.argumentValues (OriginalHereditaryFiniteObserver.family R depth) c args =
 argumentValues R c args
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedTargets
