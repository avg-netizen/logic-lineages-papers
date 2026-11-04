module
public import LogicLineages.OrdinalComparison.ParametricOmegaFreeEvaluatorProgramsProof
public import LogicLineages.OrdinalComparison.ParametricOmegaFreeEvaluatorCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricOmegaFreeEvaluator.Proof

theorem typedComponentCalibration : Targets.TypedComponentCalibration := by
  intro Γ t H i env ρ ht he
  exact omegaFreeCalibration (OrdinalComponent Γ) OrdinalSyntax.componentCode t H i env ρ ht he
end LogicLineages.OrdinalComparison.Source.ParametricOmegaFreeEvaluator.Proof
