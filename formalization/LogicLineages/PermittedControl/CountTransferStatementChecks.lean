module
public import LogicLineages.PermittedControl.CountTransferTargets
import LogicLineages.PermittedControl.CountTransferProof

public section
namespace LogicLineages.PermittedControl.StatementChecks

/-- Current17 `lem:count-transfer` at its frozen target. -/
theorem fixed_fullCountTransfer : Targets.FullCountTransfer := fullCountTransfer

#print axioms fixed_fullCountTransfer
end LogicLineages.PermittedControl.StatementChecks
