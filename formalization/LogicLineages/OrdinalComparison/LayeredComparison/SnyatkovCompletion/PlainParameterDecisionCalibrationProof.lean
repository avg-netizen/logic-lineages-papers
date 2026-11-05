module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProgramsCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionProof
open NormalForm PlainParameterDecision

theorem fixedNames_calibration (xs : List Nat) (p : Formula) :
    Code.fixedNames xs p.encode = fixedNames xs p := by
  rw [Code.fixedNames, MaximalPlainBranchProgramsProof.variables_calibration]
  rfl

theorem pin_calibration (i n : Nat) : Code.pin i n = (pin i n).encode := by
  rw [Code.pin, ← SourceTermGraphCodeProof.numeralRow_data, SourceTermGraphCodeProof.equation_calibration]
  rfl

private theorem pins_calibration (names values : List Nat) :
    names.foldr (fun i rest => SourceTermGraph.Code.conjunction (Code.pin i (values.getD i 0)) rest) 0 =
      (names.foldr (fun i rest => Formula.conjunction (pin i (valuation values i)) rest) .truth).encode := by
  induction names with
  | nil => rfl
  | cons i names ih =>
      simp only [List.foldr_cons]
      rw [ih, pin_calibration]
      rfl

theorem frame_calibration (xs values : List Nat) (p : Formula) :
    Code.frame xs values p.encode = (frame xs values p).encode := by
  rw [Code.frame, fixedNames_calibration, pins_calibration]
  rfl

theorem decideExists_calibration (xs values : List Nat) (p : Formula) :
    Code.decideExists xs values p.encode = decideExists xs values p := by
  rw [Code.decideExists, MaximalPlainBranchProgramsProof.isPlain_calibration,
    frame_calibration, PlainFrontierProgramsProof.answer_calibration]
  rfl

theorem decideForall_calibration (xs values : List Nat) (p : Formula) :
    Code.decideForall xs values p.encode = decideForall xs values p := by
  change (Code.decideExists xs values (Formula.negative p).encode).map Bool.not = _
  rw [decideExists_calibration]
  rfl

theorem literalCodeData : PlainParameterDecisionTargets.LiteralCodeData :=
  fun xs values p => ⟨frame_calibration xs values p, decideExists_calibration xs values p,
    decideForall_calibration xs values p⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionProof
