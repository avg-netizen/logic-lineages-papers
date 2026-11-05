module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionProof
open CommonLayerSyntax SourceParameterDecision

theorem literalWitnesses : SourceParameterDecisionTargets.LiteralWitnesses := by
  intro p
  rw [Code.witnesses, SourceBooleanProgramsProof.start_calibration,
    SourceBooleanProgramsProof.forest_calibration, SourceBooleanProgramsProof.count_calibration]
  rfl

theorem decideExists_calibration (xs values : List Nat) (p : SourceFormula) :
    Code.decideExists xs values p.encode = decideExists xs values p := by
  rw [Code.decideExists, SourceBooleanProgramsProof.test_calibration,
    literalWitnesses, SourceBooleanProgramsProof.compile_calibration,
    PlainParameterDecisionProof.decideExists_calibration]
  rfl

theorem decideForall_calibration (xs values : List Nat) (p : SourceFormula) :
    Code.decideForall xs values p.encode = decideForall xs values p := by
  change (Code.decideExists xs values (SourceFormula.negative p).encode).map Bool.not = _
  rw [decideExists_calibration]
  rfl

theorem literalDecisions : SourceParameterDecisionTargets.LiteralDecisions :=
  fun xs values p => ⟨decideExists_calibration xs values p, decideForall_calibration xs values p⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionProof
