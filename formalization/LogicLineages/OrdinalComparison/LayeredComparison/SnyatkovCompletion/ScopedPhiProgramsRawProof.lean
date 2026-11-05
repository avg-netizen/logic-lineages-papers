module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsFormulaCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiParametersSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecRoundtripProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsProof

theorem actualRawDecision : ScopedPhiProgramsTargets.ActualRawDecision := by
  intro values code
  have h := literalDecision values (SourceFormulaCodec.decode code)
  rw [SourceFormulaCodecProof.codeRoundtrip] at h
  rw [h]
  exact ⟨ScopedPhiParametersProof.exactDecisionDomain values _, ScopedPhiParametersProof.actualDecision values _⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsProof
