module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadFirstOrderSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecRoundtripProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadFirstOrderProof
open CommonHeadFirstOrder

theorem literalCodeCalibration : CommonHeadFirstOrderTargets.LiteralCodeCalibration := by
  intro p
  induction p with
  | compare heads E F d =>
    rw [Formula.encode, Code.translate]
    simp only [Nat.mul_mod_right, Nat.mul_div_right _ (by decide : 0 < 5),
      if_true, Code.atom, Encodable.encodek, Option.getD_some]
    rw [CommonHeadExactVariablesProof.literalCodeCalibration, BaseBooleanSourceProof.literalCompiler]
    rfl
  | negative p ih =>
    rw [Formula.encode, Code.translate]
    simp [Nat.add_mod, Nat.mul_mod_right, Nat.add_div, ih, translate, SourceFormula.encode]
  | conjunction p q ihp ihq =>
    rw [Formula.encode, Code.translate]
    simp [Nat.add_mod, Nat.mul_mod_right, Nat.add_div, ihp, ihq, translate, SourceFormula.encode]
  | existsNat i p ih =>
    rw [Formula.encode, Code.translate]
    simp [Nat.add_mod, Nat.mul_mod_right, Nat.add_div, ih, translate, SourceFormula.encode]
  | existsPositive i p ih =>
    rw [Formula.encode, Code.translate]
    simp [Nat.add_mod, Nat.mul_mod_right, Nat.add_div, ih, translate, SourceFormula.encode,
      Code.positiveGuard, CommonLayerSyntax.BaseTerm.encode]

theorem actualSourceCode : CommonHeadFirstOrderTargets.ActualSourceCode := by
  intro p hp ν
  rw [literalCodeCalibration, SourceFormulaCodecProof.sourceRoundtrip]
  exact actualSourceTranslation p hp ν

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadFirstOrderProof
