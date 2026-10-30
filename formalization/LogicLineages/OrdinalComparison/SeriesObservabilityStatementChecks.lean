module
public import LogicLineages.OrdinalComparison.SeriesObservabilityProof
public meta import LogicLineages.Audit

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualSeriesQuotientIdentity : Targets.ActualSeriesQuotientIdentity.{u} := actualSeriesQuotientIdentity
theorem fixed_actualInitialSeriesCoefficientReconstruction : Targets.ActualInitialSeriesCoefficientReconstruction.{u} :=
  actualInitialSeriesCoefficientReconstruction
theorem fixed_actualPolynomialNumeratorObservability : Targets.ActualPolynomialNumeratorObservability.{u} :=
  actualPolynomialNumeratorObservability

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
