module
public import LogicLineages.CartierObserverCurrent.SourceBudgetProof
public meta import LogicLineages.Audit

@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.SourceBudget.StatementChecks

theorem fixed_sourceConstant : Targets.SourceConstant.{u} :=
  LogicLineages.CartierObserverCurrent.SourceBudget.sourceConstant

theorem fixed_sourceMap : Targets.SourceMap.{u,v} :=
  LogicLineages.CartierObserverCurrent.SourceBudget.sourceMap

theorem fixed_binomialMultiplicity : Targets.BinomialMultiplicity.{u} :=
  LogicLineages.CartierObserverCurrent.SourceBudget.binomialMultiplicity

theorem fixed_sourceMultiplicity : Targets.SourceMultiplicity.{u} :=
  LogicLineages.CartierObserverCurrent.SourceBudget.sourceMultiplicity

theorem fixed_positiveBudgetTransient : Targets.PositiveBudgetTransient :=
  LogicLineages.CartierObserverCurrent.SourceBudget.positiveBudgetTransient

theorem fixed_mappedProperInput : Targets.MappedProperInput.{u,v} :=
  LogicLineages.CartierObserverCurrent.SourceBudget.mappedProperInput

#audit_namespace LogicLineages.CartierObserverCurrent.SourceBudget.StatementChecks
end LogicLineages.CartierObserverCurrent.SourceBudget.StatementChecks
