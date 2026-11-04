module
public import LogicLineages.OrdinalComparison.ParametricSourceSuccessorTargets
public import LogicLineages.OrdinalComparison.ParametricSourceSuccessorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricSourceSuccessor.StatementChecks
theorem phi_calibration : Targets.PhiCalibration := Proof.phiCalibration
theorem exact_substitution : Targets.ExactSubstitution := Proof.exactSubstitution
theorem generic_source_graph : Targets.GenericSourceGraph := Proof.genericSourceGraph
theorem actual_gamma_graph : Targets.ActualGammaGraph := Proof.actualGammaGraph
end LogicLineages.OrdinalComparison.Source.ParametricSourceSuccessor.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.ParametricSourceSuccessor
