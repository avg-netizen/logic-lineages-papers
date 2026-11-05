module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BooleanSourceBlocksSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BooleanSourceBlocksCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecRoundtripProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BooleanSourceBlocksProof
open BooleanSourceBlocks

theorem actualRawDecision : BooleanSourceBlocksTargets.ActualRawDecision := by
  intro values code
  have h := literalCodeDecision values (SourceFormulaCodec.decode code)
  rw [SourceFormulaCodecProof.codeRoundtrip] at h
  rw [h]
  exact ⟨exactDecisionDomain values _, actualDecision values _⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BooleanSourceBlocksProof
