module
public import LogicLineages.CartierObserverCurrent.PeriodTupleFactsTargets
import LogicLineages.CartierObserverCurrent.PeriodTupleExistenceProof
import LogicLineages.CartierObserverCurrent.PeriodTupleUpperProof
import LogicLineages.CartierObserverCurrent.PeriodTupleSmallProof
import LogicLineages.CartierObserverCurrent.PeriodTupleExactProof
public meta import LogicLineages.Audit
public section
namespace LogicLineages.CartierObserverCurrent.PeriodTupleFacts.StatementChecks
theorem fixed_rootExists : Targets.RootExists := rootExists
theorem fixed_actualIterate : Targets.ActualIterate := actualIterate
theorem fixed_actualUpper : Targets.ActualUpper := actualUpper
theorem fixed_actualMidpoint : Targets.ActualMidpoint := actualMidpoint
theorem fixed_actualSmall : Targets.ActualSmall := actualSmall
theorem fixed_actualExact : Targets.ActualExact := actualExact
#audit_namespace LogicLineages.CartierObserverCurrent.PeriodTupleFacts.StatementChecks
end LogicLineages.CartierObserverCurrent.PeriodTupleFacts.StatementChecks
