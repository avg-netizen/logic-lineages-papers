module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensional
open FirstOrder Language InternalCalculus InternalClosedPrograms
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedArgumentObservationsCongruence
/-- All runtime parameters, then all packed inputs and both actual outputs.
This deliberately exceeds fixed-parameter agreement because lambda uses a
queried extended child parameter. No source or native semantics are assumed. -/
def GlobalAgreement {alpha : Type} (R S : Program 2) : Formula alpha :=
 allBlock (Agreement R S (.var (.inr (0 : Fin 1))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensional
