module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteScalarTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteScalarProof
open SemanticFiniteScalar Source.ForwardTranslation CommonLayerSyntax

theorem literalNumericCalibration : SemanticFiniteScalarTargets.LiteralNumericCalibration := by
  intro ι index s
  induction s with
  | one => simp [Code.compile, scalarSyntaxCode, compile, BaseTerm.encode]
  | var i =>
    rw [scalarSyntaxCode, Code.compile]
    simp [Nat.add_mod, Nat.mul_mod_right, Nat.add_div, compile, BaseTerm.encode]
  | add a b iha ihb =>
    rw [scalarSyntaxCode, Code.compile]
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add]
    have hd : (4 * Nat.pair (scalarSyntaxCode index a) (scalarSyntaxCode index b) + 2) / 4 =
      Nat.pair (scalarSyntaxCode index a) (scalarSyntaxCode index b) := by omega
    rw [hd]
    simp only [Nat.unpair_pair]
    rw [iha, ihb]
    cases ha : compile index a <;> cases hb : compile index b <;> simp [compile, ha, hb, BaseTerm.encode]
  | shift c a ih =>
    rw [scalarSyntaxCode, Code.compile]
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add]
    have hd : (4 * Nat.pair (closedPositiveCode c) (scalarSyntaxCode index a) + 3) / 4 =
      Nat.pair (closedPositiveCode c) (scalarSyntaxCode index a) := by omega
    rw [hd]
    simp only [Nat.unpair_pair]
    rw [ih]
    cases hc : SemanticCoefficient.Code.recognize (closedPositiveCode c) <;> cases ha : compile index a <;> simp [compile, hc, ha, FiniteCoefficientBaseProof.expand_calibration]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteScalarProof
