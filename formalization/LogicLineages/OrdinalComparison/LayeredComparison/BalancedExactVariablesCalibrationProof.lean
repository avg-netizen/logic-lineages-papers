module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariablesTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedTypedCompilerCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormulaLiteralProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariables.Proof
open BalancedSyntax BalancedEvaluation

theorem variables_code (support : List Nat) :
    variablesCode support = (variablesFormula support).encode := by
  unfold variablesCode variablesFormula
  rw [← BalancedBoxFormula.Proof.conjunction_code]
  simp only [List.map_map]
  rfl

theorem raw_support_calibration (Γ : List Nat) (C : Certificate Γ)
    (E F : Syntax Γ) :
    rawSupport Γ (encodeCertificate Γ C) (encodeSyntax Γ E) (encodeSyntax Γ F) =
      sourceSupport Γ C E F := by
  unfold rawSupport sourceSupport
  rw [(BalancedBoxEvaluation.Proof.actualSourceCalibration Γ C E []).2,
    (BalancedBoxEvaluation.Proof.actualSourceCalibration Γ C F []).2]

theorem exactTypedCodeCalibration : Targets.ExactTypedCodeCalibration := by
  intro Γ C E F desired
  unfold formulaCode
  rw [BalancedTypedCompiler.Proof.exactTypedCodeCalibration Γ C E F desired,
    raw_support_calibration, variables_code]
  rfl

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariables.Proof
