module
public import LogicLineages.ControlSensitivityCurrent.InputNormalizationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.InputNormalization.StatementChecks
theorem fixed_reference : InputNormalizationTargets.ReferenceNaturality := referenceNaturality
theorem fixed_wires : InputNormalizationTargets.WireCorrect := wireCorrect
theorem fixed_normalization : InputNormalizationTargets.Normalization := normalization
theorem fixed_budgets : InputNormalizationTargets.Budgets := budgets
#print axioms fixed_reference
#print axioms fixed_wires
#print axioms fixed_normalization
#print axioms fixed_budgets
end LogicLineages.ControlSensitivityCurrent.InputNormalization.StatementChecks
