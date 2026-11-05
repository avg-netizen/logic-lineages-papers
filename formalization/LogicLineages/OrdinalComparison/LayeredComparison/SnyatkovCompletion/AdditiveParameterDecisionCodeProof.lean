module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveParameterDecisionTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveSourceCodeCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveSourceCodeProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveParameterDecisionProof
open AdditiveParameterDecision

theorem literalCodeDecision : AdditiveParameterDecisionTargets.LiteralCodeDecision := by
  intro values p
  unfold Code.decide AdditiveParameterDecision.decide
  rw [AdditiveSourceProof.test_calibration, AdditiveSourceProof.eliminate_calibration,
    PlainParameterDecisionProof.decideExists_calibration]

theorem actualNumericProgram : AdditiveParameterDecisionTargets.ActualNumericProgram := by
  let A := List Nat × Nat
  have ht : PrimrecPred (fun p : A => AdditiveSource.Code.test p.2 = true) :=
    Primrec.eq.comp (AdditiveSourceProof.test_primitive.comp Primrec.snd) (Primrec.const true)
  have he : Primrec (fun p : A => AdditiveSource.Code.eliminate p.2) :=
    AdditiveSourceProof.eliminate_primitive.comp Primrec.snd
  have hy := PlainParameterDecisionProof.decideExists_primitive.comp
    ((Primrec.const ([] : List Nat)).pair (Primrec.fst.pair he))
  exact Primrec.ite ht hy (Primrec.const none)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveParameterDecisionProof
