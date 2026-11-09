module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportMatrixProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportCalibrationProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportProof

/-- Correlated Boolean transport for the actual original row compiler.
The separate congruence residue pass and the uniform closed existential
solver remain downstream obligations, not assumptions hidden by this package. -/
theorem fullOutcomeTransport : OutcomeTransportTargets.FullOutcomeTransport :=
  ⟨exactCorrelatedBody,bodySyntaxAndDomains,literalCodeCalibration,
    exactActualMatrix,OutcomeTransportPrograms.actualNumericPrograms⟩

#print axioms fullOutcomeTransport

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportProof
