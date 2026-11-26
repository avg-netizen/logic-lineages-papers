module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildContentDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open SixSol20261112.Context.ScheduledDeletionDefinitions
/-- A proof-side observation of actual annotated jobs. Role zero computes Q
at the unchanged packed type/raw and stored parameter. Nonzero roles compute
the original argument-list observation on the unchanged raw/parameter. This
is not asserted to be the value of a completed runtime without further proof. -/
def observationFromJob (Q : Program 2) : Program 1 :=
  InternalAcceptance.branch (leftOf (.projection 0)) (scalarFromJob Q)
    (.composition (OriginalTypedArgumentObservations.argumentObservations Q) ![jobRaw,jobParameter])
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildContentDefinitions
