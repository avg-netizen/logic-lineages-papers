module
public import LogicLineages.OrdinalComparison.ControlHierarchyGrowthProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_fullFastControlHierarchyGrowth : Targets.FullFastControlHierarchyGrowth :=
  fullFastControlHierarchyGrowth

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
