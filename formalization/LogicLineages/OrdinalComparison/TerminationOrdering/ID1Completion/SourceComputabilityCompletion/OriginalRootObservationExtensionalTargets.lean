module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedArgumentObservationsCongruence OriginalRootObservationExtensional OriginalRootObservation
/-- Actual AST extensionality on every arithmetic input, including malformed
branches, under the explicit internally quantified all-parameter hypothesis. -/
def RootExtensionality : Prop := ∀ (R S : Program 2) (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (parameter : OTerm alpha),
 Nonempty (Derivation body Delta ((GlobalAgreement R S).imp
   (Agreement (rootObservation R) (rootObservation S) parameter)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalTargets
