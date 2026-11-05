module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedFirstOrderSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariablesCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecRoundtripProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedFirstOrderProof
open BalancedFirstOrder

theorem literalCodeCalibration : BalancedFirstOrderTargets.LiteralCodeCalibration := by
  intro p
  induction p with
  | compare Γ C E F d =>
    rw [Formula.encode, Code.translate]
    simp only [Nat.mul_mod_right, Nat.mul_div_right _ (by decide : 0 < 4),
      if_true, Code.atom, Encodable.encodek, Option.getD_some]
    change BaseBooleanSource.Code.compile (BalancedExactVariables.formulaCode Γ
      (BalancedEvaluation.encodeCertificate Γ C) (BalancedEvaluation.encodeSyntax Γ E)
      (BalancedEvaluation.encodeSyntax Γ F) d) = _
    rw [BalancedExactVariables.Proof.exactTypedCodeCalibration Γ C E F d,
      BaseBooleanSourceProof.literalCompiler]
    rfl
  | negative p ih =>
    rw [Formula.encode, Code.translate]
    simp [Nat.add_mod, Nat.mul_mod_right, Nat.add_div, ih, translate, SourceFormula.encode]
  | conjunction p q ihp ihq =>
    rw [Formula.encode, Code.translate]
    simp [Nat.add_mod, Nat.mul_mod_right, Nat.add_div, ihp, ihq, translate, SourceFormula.encode]
  | existsPositive i p ih =>
    rw [Formula.encode, Code.translate]
    simp [Nat.add_mod, Nat.mul_mod_right, Nat.add_div, ih, translate, SourceFormula.encode,
      CommonHeadFirstOrder.Code.positiveGuard, CommonLayerSyntax.BaseTerm.encode]

theorem actualSourceCode : BalancedFirstOrderTargets.ActualSourceCode := by
  intro p hp ν hν
  rw [literalCodeCalibration, SourceFormulaCodecProof.sourceRoundtrip]
  exact actualSourceTranslation p hp ν hν

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedFirstOrderProof
