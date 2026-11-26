module
public import LogicLineages.CartierObserverCurrent.ProfileOutputProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.ProfileOutput.StatementChecks

theorem fixed_productRegular : Targets.ProductRegular :=
  LogicLineages.CartierObserverCurrent.ProfileOutput.productRegular

theorem fixed_numeratorRatio : Targets.NumeratorRatio :=
  LogicLineages.CartierObserverCurrent.ProfileOutput.numeratorRatio

theorem fixed_actualSeriesOutput : Targets.ActualSeriesOutput :=
  LogicLineages.CartierObserverCurrent.ProfileOutput.actualSeriesOutput

theorem fixed_outputDescent : Targets.OutputDescent :=
  LogicLineages.CartierObserverCurrent.ProfileOutput.outputDescent

theorem fixed_actualBaseOutput : Targets.ActualBaseOutput :=
  LogicLineages.CartierObserverCurrent.ProfileOutput.actualBaseOutput

#audit_namespace LogicLineages.CartierObserverCurrent.ProfileOutput.StatementChecks
end LogicLineages.CartierObserverCurrent.ProfileOutput.StatementChecks
