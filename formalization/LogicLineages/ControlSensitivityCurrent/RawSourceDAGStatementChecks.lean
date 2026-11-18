module
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGEffectiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.StatementChecks
theorem fixed_references : RawSourceDAGTargets.References := references
theorem fixed_typed_roundtrip : RawSourceDAGTargets.TypedRoundtrip := typedRoundtrip
theorem fixed_validation : RawSourceDAGTargets.Validation := validation
theorem fixed_effective : RawSourceDAGTargets.Effective := effective
#print axioms fixed_references
#print axioms fixed_typed_roundtrip
#print axioms fixed_validation
#print axioms fixed_effective
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.StatementChecks
