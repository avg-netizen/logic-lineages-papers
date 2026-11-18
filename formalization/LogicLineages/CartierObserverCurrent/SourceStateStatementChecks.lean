module
public import LogicLineages.CartierObserverCurrent.SourceStateProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.SourceState.StatementChecks

theorem fixed_wordDenominator : Targets.WordDenominator.{u} :=
  LogicLineages.CartierObserverCurrent.SourceState.wordDenominator

theorem fixed_sourceDenominator : Targets.SourceDenominator :=
  LogicLineages.CartierObserverCurrent.SourceState.sourceDenominator

theorem fixed_transientState : Targets.TransientState :=
  LogicLineages.CartierObserverCurrent.SourceState.transientState

#audit_namespace LogicLineages.CartierObserverCurrent.SourceState.StatementChecks
end LogicLineages.CartierObserverCurrent.SourceState.StatementChecks
