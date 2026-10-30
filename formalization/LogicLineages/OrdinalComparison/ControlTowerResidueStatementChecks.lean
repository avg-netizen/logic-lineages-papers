module
public import LogicLineages.OrdinalComparison.ControlTowerResidueProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_exponentTowerResidueStability : Targets.ExponentTowerResidueStability :=
  exponentTowerResidueStability

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
