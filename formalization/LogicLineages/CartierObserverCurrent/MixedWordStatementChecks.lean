module
public import LogicLineages.CartierObserverCurrent.MixedWordProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.MixedWord.StatementChecks

theorem fixed_wordProper : Targets.WordProper.{u} :=
  LogicLineages.CartierObserverCurrent.MixedWord.wordProper

theorem fixed_wordOrderBound : Targets.WordOrderBound.{u} :=
  LogicLineages.CartierObserverCurrent.MixedWord.wordOrderBound

theorem fixed_wordNoNewPole : Targets.WordNoNewPole.{u} :=
  LogicLineages.CartierObserverCurrent.MixedWord.wordNoNewPole

#audit_namespace LogicLineages.CartierObserverCurrent.MixedWord.StatementChecks
end LogicLineages.CartierObserverCurrent.MixedWord.StatementChecks
