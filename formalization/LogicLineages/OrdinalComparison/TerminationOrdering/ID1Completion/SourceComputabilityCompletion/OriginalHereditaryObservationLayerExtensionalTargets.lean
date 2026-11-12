module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerExtensionalTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedArgumentObservationsCongruence OriginalRootObservationExtensional
/-- Same actual input and parameter. No source or context covariance. -/
def RowsExtensionality : Prop := ∀ (Q T : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (parameter : OTerm alpha),
 Nonempty (Derivation body Delta ((GlobalAgreement Q T).imp
  (Agreement (OriginalHereditaryDeletionRows.rows Q) (OriginalHereditaryDeletionRows.rows T) parameter)))
def LayerExtensionality : Prop := ∀ (R S Q T : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (parameter : OTerm alpha),
 Nonempty (Derivation body Delta ((GlobalAgreement R S ⊓ GlobalAgreement Q T).imp
  (Agreement (OriginalHereditaryObservationLayer.layer R Q) (OriginalHereditaryObservationLayer.layer S T) parameter)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerExtensionalTargets
