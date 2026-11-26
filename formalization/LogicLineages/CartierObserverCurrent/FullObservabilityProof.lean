module
public import LogicLineages.CartierObserverCurrent.FullObservabilityTargets
public import LogicLineages.OrdinalComparison.BinaryMatrixProof
public meta import LogicLineages.Audit
@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.FullObservability
open LogicLineages.OrdinalComparison

theorem completeObservability : Targets.CompleteObservability.{u} := by
  exact ⟨actualPolynomialNumeratorObservability,
    actualBinaryPolynomialBoundedContinuation, actualBinaryMatrixBoundedContinuation⟩

#audit_namespace LogicLineages.CartierObserverCurrent.FullObservability
end LogicLineages.CartierObserverCurrent.FullObservability
