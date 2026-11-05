module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecRoundtripProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceProof
open HomogeneousSource

theorem raw_calibration (values : List Nat) (code : Nat) :
    Code.decide values code = decide values (SourceFormulaCodec.decode code) := by
  simpa only [SourceFormulaCodecProof.codeRoundtrip code] using
    decide_calibration values (SourceFormulaCodec.decode code)

theorem actualRawDecision : HomogeneousSourceTargets.ActualRawDecision := by
  intro values code
  rw [raw_calibration]
  exact ⟨exactDecisionDomain values (SourceFormulaCodec.decode code),
    fun hp b => actualDecision values (SourceFormulaCodec.decode code) hp b⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceProof
