module
public import LogicLineages.CartierObserverCurrent.L0Proof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.StatementChecks

theorem fixed_evenSelectorIdentity : Targets.EvenSelectorIdentity.{u} :=
  Proof.evenSelectorIdentity

theorem fixed_evenSelectorLocalPowers : Targets.EvenSelectorLocalPowers.{u} :=
  Proof.evenSelectorLocalPowers

#audit_namespace LogicLineages.CartierObserverCurrent.StatementChecks
end LogicLineages.CartierObserverCurrent.StatementChecks
