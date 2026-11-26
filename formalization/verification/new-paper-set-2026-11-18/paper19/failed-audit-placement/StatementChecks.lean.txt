module
public import LogicLineages.ControlSensitivityCurrent.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.StatementChecks

theorem fixed_fullPerturbedControl : Targets.FullPerturbedControl :=
  Proof.fullPerturbedControl

#print axioms fixed_fullPerturbedControl
#audit_namespace LogicLineages.ControlSensitivityCurrent.Proof
#audit_namespace LogicLineages.ControlSensitivityCurrent.StatementChecks
end LogicLineages.ControlSensitivityCurrent.StatementChecks
