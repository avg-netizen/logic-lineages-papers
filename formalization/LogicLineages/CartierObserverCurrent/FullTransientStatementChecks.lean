module
public import LogicLineages.CartierObserverCurrent.FullTransientProof
public meta import LogicLineages.Audit

@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.FullTransient.StatementChecks

theorem fixed_binaryTransient : Targets.BinaryTransient.{u,v} := FullTransient.binaryTransient

#audit_namespace LogicLineages.CartierObserverCurrent.FullTransient.StatementChecks
end LogicLineages.CartierObserverCurrent.FullTransient.StatementChecks
