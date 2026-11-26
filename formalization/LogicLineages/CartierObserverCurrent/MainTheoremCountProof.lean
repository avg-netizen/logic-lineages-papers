module
public import LogicLineages.CartierObserverCurrent.FullBudgetTransferTargets
import LogicLineages.CartierObserverCurrent.FullBudgetTransferStatementChecks
public meta import LogicLineages.Audit

public section
namespace LogicLineages.CartierObserverCurrent.MainTheorem.Count

/-- Item 1 of current20 thm:main: the accepted thm:transfer comparator. -/
theorem countTransfer : FullBudgetTransfer.Targets.CompleteTransfer :=
  FullBudgetTransfer.StatementChecks.fixed_completeTransfer

#audit_namespace LogicLineages.CartierObserverCurrent.MainTheorem.Count
end LogicLineages.CartierObserverCurrent.MainTheorem.Count
