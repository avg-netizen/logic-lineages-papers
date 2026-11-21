module
public import LogicLineages.PermittedControl.FieldComparisonTargets
import LogicLineages.PermittedControl.FieldComparisonProof

public section
namespace LogicLineages.PermittedControl.StatementChecks

/-- Current17 `lem:field-comparison` at its frozen target. -/
theorem fixed_fullFieldComparison : FieldComparison.FullFieldComparison :=
  FieldComparison.fullFieldComparison

#print axioms fixed_fullFieldComparison
end LogicLineages.PermittedControl.StatementChecks
