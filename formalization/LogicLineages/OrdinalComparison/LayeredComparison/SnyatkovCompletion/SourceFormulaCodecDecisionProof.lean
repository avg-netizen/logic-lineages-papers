module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecRoundtripProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecProof
open SourceFormulaCodec

theorem literalRawPayload : SourceFormulaCodecTargets.LiteralRawPayload := by
  intro code
  simpa only [codeRoundtrip code] using SourceBooleanProgramsProof.literalPayload (decode code)

theorem exists_calibration (xs values : List Nat) (code : Nat) :
    SourceParameterDecision.Code.decideExists xs values code =
      SourceParameterDecision.decideExists xs values (decode code) := by
  simpa only [codeRoundtrip code] using SourceParameterDecisionProof.decideExists_calibration xs values (decode code)

theorem forall_calibration (xs values : List Nat) (code : Nat) :
    SourceParameterDecision.Code.decideForall xs values code =
      SourceParameterDecision.decideForall xs values (decode code) := by
  simpa only [codeRoundtrip code] using SourceParameterDecisionProof.decideForall_calibration xs values (decode code)

theorem exactRawDecisionDomain : SourceFormulaCodecTargets.ExactRawDecisionDomain := by
  intro xs values code
  rw [exists_calibration, forall_calibration]
  exact SourceParameterDecisionProof.exactDecisionDomain xs values (decode code)

theorem actualRawDecisions : SourceFormulaCodecTargets.ActualRawDecisions := by
  intro xs values code hp b
  rw [exists_calibration, forall_calibration]
  exact SourceParameterDecisionProof.actualSourceDecisions xs values (decode code) hp b

theorem actualRawNumericPrograms : SourceFormulaCodecTargets.ActualRawNumericPrograms :=
  ⟨SourceParameterDecisionProof.decideExists_primitive, SourceParameterDecisionProof.decideForall_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecProof
