module
public import LogicLineages.OrdinalComparison.HeadFiniteSurplusTargets
public import LogicLineages.OrdinalComparison.HeadFiniteSurplusProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.HeadFiniteSurplus.StatementChecks
theorem exact_head_partial : Targets.ExactHeadPartial := Proof.exactHeadPartial
theorem surplus_bounds : Targets.SurplusBounds := Proof.surplusBounds
theorem actual_source_surplus : Targets.ActualSourceSurplus := Proof.actualSourceSurplus
end LogicLineages.OrdinalComparison.Source.HeadFiniteSurplus.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.HeadFiniteSurplus
