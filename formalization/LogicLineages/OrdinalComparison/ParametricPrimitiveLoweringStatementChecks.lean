module
public import LogicLineages.OrdinalComparison.ParametricPrimitiveLoweringTargets
public import LogicLineages.OrdinalComparison.ParametricPrimitiveLoweringProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPrimitiveLowering.StatementChecks
theorem shared_inputs_and_syntax : Targets.SharedInputsAndSyntax := Proof.sharedInputsAndSyntax
theorem exact_supported_lowering : Targets.ExactSupportedLowering := Proof.exactSupportedLowering
theorem actual_gamma_lowering : Targets.ActualGammaLowering := Proof.actualGammaLowering
theorem exact_size : Targets.ExactSize := Proof.exactSize
end LogicLineages.OrdinalComparison.Source.ParametricPrimitiveLowering.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.ParametricPrimitiveLowering
