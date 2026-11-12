module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionSelectionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalDefinitions
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal all-position observed minimum on the pre-minimum structural key. -/
def minimumInputs (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) :=
  OriginalClassContextAllPositionSelection.inputs
    (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P

/-- Same unchanged rank/transparent/variable refinement, now on that actual minimum. -/
def refined (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) :=
  OriginalFinalGuardedRank.refined (minimumInputs p H G W P) H G W

def observer (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :=
  OriginalClassContextAllPositionObserver.positionObservation
    (OriginalStructuralClassKeyDefinitions.key p H G W)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalDefinitions
