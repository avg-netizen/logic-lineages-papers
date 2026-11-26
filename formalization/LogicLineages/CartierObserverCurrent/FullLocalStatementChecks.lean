module
public import LogicLineages.CartierObserverCurrent.FullLocalProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.FullLocal.StatementChecks

theorem fixed_localRule : Targets.LocalRule.{u} := FullLocal.localRule

#audit_namespace LogicLineages.CartierObserverCurrent.FullLocal.StatementChecks
end LogicLineages.CartierObserverCurrent.FullLocal.StatementChecks
