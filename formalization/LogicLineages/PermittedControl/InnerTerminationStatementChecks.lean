module
public import LogicLineages.PermittedControl.InnerTerminationTargets
import LogicLineages.PermittedControl.InnerTerminationProof

public section
namespace LogicLineages.PermittedControl.StatementChecks

/-- Current17 `lem:inner-termination` at its frozen target. -/
theorem fixed_fullInnerTermination : InnerTerminationTargets.FullInnerTermination :=
  InnerTerminationProof.fullInnerTermination

#print axioms fixed_fullInnerTermination
end LogicLineages.PermittedControl.StatementChecks
