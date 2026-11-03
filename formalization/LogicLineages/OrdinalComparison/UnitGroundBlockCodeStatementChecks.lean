module
public import LogicLineages.OrdinalComparison.UnitGroundBlockCodeTargets
public import LogicLineages.OrdinalComparison.UnitGroundBlockCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitGroundBlockCode.StatementChecks
theorem exact_probe_codes : Targets.ExactProbeCodes := Proof.exactProbeCodes
theorem exact_ground_block : Targets.ExactGroundBlock := Proof.exactGroundBlock
theorem effective_algorithms : Targets.EffectiveAlgorithms := Proof.effectiveAlgorithms
theorem actual_anchor_calibration : Targets.ActualAnchorCalibration := Proof.actualAnchorCalibration
end LogicLineages.OrdinalComparison.Source.UnitGroundBlockCode.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.UnitGroundBlockCode
