module
public import LogicLineages.OrdinalComparison.ParametricPairWorklistTargets
public import LogicLineages.OrdinalComparison.ParametricPairWorklistProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairWorklist.StatementChecks
theorem exact_children : Targets.ExactChildren := Proof.exactChildren
theorem continuation_calibration : Targets.ContinuationCalibration := Proof.continuationCalibration
theorem exact_success : Targets.ExactSuccess := Proof.exactSuccess
end LogicLineages.OrdinalComparison.Source.ParametricPairWorklist.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.ParametricPairWorklist
