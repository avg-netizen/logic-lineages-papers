module
public import LogicLineages.CartierObserverCurrent.NaturalityProof
public meta import LogicLineages.Audit

@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.Naturality.StatementChecks

theorem fixed_extensionInjective : Targets.ExtensionInjective.{u,v} :=
  LogicLineages.CartierObserverCurrent.Naturality.extensionInjective

theorem fixed_extensionPolynomial : Targets.ExtensionPolynomial.{u,v} :=
  LogicLineages.CartierObserverCurrent.Naturality.extensionPolynomial

theorem fixed_extensionStep : Targets.ExtensionStep.{u,v} :=
  LogicLineages.CartierObserverCurrent.Naturality.extensionStep

theorem fixed_extensionWord : Targets.ExtensionWord.{u,v} :=
  LogicLineages.CartierObserverCurrent.Naturality.extensionWord

#audit_namespace LogicLineages.CartierObserverCurrent.Naturality.StatementChecks
end LogicLineages.CartierObserverCurrent.Naturality.StatementChecks
