module
public import LogicLineages.OrdinalComparison.SeriesContinuationProof
public meta import LogicLineages.Audit

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualBinarySeriesWordSelection : Targets.ActualBinarySeriesWordSelection.{u} := actualBinarySeriesWordSelection
theorem fixed_actualBinaryDigitsValueAndBound : Targets.ActualBinaryDigitsValueAndBound := actualBinaryDigitsValueAndBound
theorem fixed_actualSeriesBoundedContinuation : Targets.ActualSeriesBoundedContinuation.{u} := actualSeriesBoundedContinuation

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
