module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerExtensionalRowsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerExtensionalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalRootObservationExtensionalProof OriginalRootObservationExtensionalValuesProof
open OriginalHereditaryObservationLayerExtensionalRowsProof

theorem exactLayer : OriginalHereditaryObservationLayerExtensionalTargets.LayerExtensionality := by
 intro R S Q T body alpha Delta parameter
 let A : Formula alpha := OriginalRootObservationExtensional.GlobalAgreement R S ⊓ OriginalRootObservationExtensional.GlobalAgreement Q T
 have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hR := rootAgreement R S parameter (andLeft ha)
 have hQ := rootAgreement Q T parameter (andRight ha)
 have hRows := rowsAgreement Q T parameter (andRight ha)
 obtain ⟨h⟩ := pairAgreement _ _ _ _ parameter hR (pairAgreement _ _ _ _ parameter hQ hRows)
 exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerExtensionalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerExtensionalProof
