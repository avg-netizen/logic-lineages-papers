module
public import LogicLineages.CartierObserverCurrent.FullBinaryMatrixTargets
public import LogicLineages.CartierObserverCurrent.FullSelectedCoefficientTargets
public import LogicLineages.CartierObserverCurrent.FullObservabilityTargets
public import LogicLineages.OrdinalComparison.BinarySourceTargets
import LogicLineages.CartierObserverCurrent.FullBinaryMatrixStatementChecks
import LogicLineages.CartierObserverCurrent.FullSelectedCoefficientStatementChecks
import LogicLineages.CartierObserverCurrent.FullObservabilityStatementChecks
import LogicLineages.OrdinalComparison.BinarySourceProof
public meta import LogicLineages.Audit

public section
universe u
namespace LogicLineages.CartierObserverCurrent.MainTheorem.Observer

/-- Item 2 of current20 thm:main: lem:matrix, thm:observer, lem:observable and
the observability clause at the actual source denominator. -/
theorem binaryObserver :
    FullBinaryMatrix.Targets.CompleteStateUpdate ∧
    FullSelectedCoefficient.Targets.CompleteSelectedCoefficient ∧
    FullObservability.Targets.CompleteObservability.{u} ∧
    LogicLineages.OrdinalComparison.Targets.ActualSourceBinaryObservability.{u} :=
  ⟨FullBinaryMatrix.StatementChecks.fixed_completeStateUpdate,
    FullSelectedCoefficient.StatementChecks.fixed_completeSelectedCoefficient,
    FullObservability.StatementChecks.fixed_completeObservability.{u},
    LogicLineages.OrdinalComparison.actualSourceBinaryObservability.{u}⟩

#audit_namespace LogicLineages.CartierObserverCurrent.MainTheorem.Observer
end LogicLineages.CartierObserverCurrent.MainTheorem.Observer
