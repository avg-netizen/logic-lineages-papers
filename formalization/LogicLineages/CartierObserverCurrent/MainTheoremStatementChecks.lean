module
public import LogicLineages.CartierObserverCurrent.MainTheoremTargets
import LogicLineages.CartierObserverCurrent.MainTheoremProof
public meta import LogicLineages.Audit

public section
universe u v
namespace LogicLineages.CartierObserverCurrent.MainTheorem.StatementChecks

theorem fixed_completeMain : Targets.CompleteMain.{u, v} := completeMain.{u, v}

#audit_namespace LogicLineages.CartierObserverCurrent.MainTheorem.StatementChecks
end LogicLineages.CartierObserverCurrent.MainTheorem.StatementChecks
