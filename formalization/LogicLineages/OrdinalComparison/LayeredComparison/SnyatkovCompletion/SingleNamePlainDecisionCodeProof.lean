module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainDecisionTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainCodeProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainDecisionProof
open NormalForm (Formula)
open SingleNamePlainDecision
attribute [local irreducible] Nat.sqrt Nat.unpair

theorem literalCodeCalibration : SingleNamePlainDecisionTargets.LiteralCodeCalibration := by
  intro i p
  constructor
  · simp only [Code.existsDecision, existsDecision, SingleNamePlainProof.admissible_calibration,
      SingleNamePlainProof.existsEliminate_calibration, ZeroValuationProof.evaluate_calibration]
  · simp only [Code.forallDecision, forallDecision, SingleNamePlainProof.admissible_calibration,
      SingleNamePlainProof.forallEliminate_calibration, ZeroValuationProof.evaluate_calibration]

attribute [local irreducible] SingleNamePlain.Code.admissible
  SingleNamePlain.Code.existsEliminate SingleNamePlain.Code.forallEliminate ZeroValuation.Code.evaluate

theorem existsDecision_primitive : Primrec₂ Code.existsDecision :=
  Primrec.ite (Primrec.eq.comp SingleNamePlainProof.admissible_primitive (Primrec.const true))
    (Primrec.option_some.comp (ZeroValuationProof.evaluate_primitive.comp SingleNamePlainProof.existsEliminate_primitive))
    (Primrec.const none)

theorem forallDecision_primitive : Primrec₂ Code.forallDecision :=
  Primrec.ite (Primrec.eq.comp SingleNamePlainProof.admissible_primitive (Primrec.const true))
    (Primrec.option_some.comp (ZeroValuationProof.evaluate_primitive.comp SingleNamePlainProof.forallEliminate_primitive))
    (Primrec.const none)

theorem actualNumericPrograms : SingleNamePlainDecisionTargets.ActualNumericPrograms :=
  ⟨existsDecision_primitive, forallDecision_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainDecisionProof
