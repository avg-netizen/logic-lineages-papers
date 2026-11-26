module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationSourceUniformityTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayer
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
/-- One finite observation layer only. No recursion or selected source tuple changes. -/
def layer (R Q : Program 2) : Program 2 :=
  pairOf (OriginalRootObservation.rootObservation R)
    (pairOf (OriginalRootObservation.rootObservation Q) (OriginalHereditaryDeletionRows.rows Q))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayer
