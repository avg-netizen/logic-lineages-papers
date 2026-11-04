module
public import LogicLineages.OrdinalComparison.ParametricPrimitiveFiniteCalibrationProof
public import LogicLineages.OrdinalComparison.ParametricPrimitiveFiniteRenamingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPrimitiveFinite.Proof

theorem actualGammaExpressions : Targets.ActualGammaExpressions := by
  intro b
  have h := ParametricCoefficientOne.Proof.actualGammaCoefficientOne b
  exact exactExpressionCalibration _ h.1 h.2.1
end LogicLineages.OrdinalComparison.Source.ParametricPrimitiveFinite.Proof
