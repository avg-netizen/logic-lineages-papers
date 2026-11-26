module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationEncodingTargets
open OriginalRootObservation
/-- Native injectivity only, fixed symbol type; retains multiplicity and ordered extras. -/
def ExactEncoding : Prop := Function.Injective typedNumber ∧
 Function.Injective multisetNumber ∧
 ∀ n : Nat, Function.Injective (@signatureNumber n)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationEncodingTargets
