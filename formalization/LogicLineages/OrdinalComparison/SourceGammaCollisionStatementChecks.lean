module
public import LogicLineages.OrdinalComparison.SourceGammaCollisionTargets
public import LogicLineages.OrdinalComparison.SourceGammaCollisionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaCollision.StatementChecks
theorem actual_control_gap : Targets.ActualControlGap := Proof.actualControlGap
theorem numeric_collision : Targets.NumericCollision := Proof.numericCollision
theorem actual_source_collision : Targets.ActualSourceCollision := Proof.actualSourceCollision
end LogicLineages.OrdinalComparison.Source.SourceGammaCollision.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SourceGammaCollision
