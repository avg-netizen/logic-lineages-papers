module
public import LogicLineages.CartierObserverCurrent.CanonicalExtensionProof
public meta import LogicLineages.Audit

@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.CanonicalExtension.StatementChecks

theorem fixed_denominatorMap : Targets.DenominatorMap.{u,v} :=
  LogicLineages.CartierObserverCurrent.CanonicalExtension.denominatorMap

theorem fixed_numeratorMap : Targets.NumeratorMap.{u,v} :=
  LogicLineages.CartierObserverCurrent.CanonicalExtension.numeratorMap

theorem fixed_properMap : Targets.ProperMap.{u,v} :=
  LogicLineages.CartierObserverCurrent.CanonicalExtension.properMap

#audit_namespace LogicLineages.CartierObserverCurrent.CanonicalExtension.StatementChecks
end LogicLineages.CartierObserverCurrent.CanonicalExtension.StatementChecks
