module
public import LogicLineages.CartierObserverCurrent.FullBinaryMatrixTargets
public import LogicLineages.OrdinalComparison.BinaryMatrixProof
public import LogicLineages.OrdinalComparison.BinaryDenominatorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullBinaryMatrix
open LogicLineages.OrdinalComparison

theorem completeStateUpdate : Targets.CompleteStateUpdate := by
  intro d
  have hdeg := actualBinarySourceDenominatorDegree d
  refine ⟨hdeg, ?_⟩
  intro U hU b
  refine ⟨actualBinaryQuotientTransport _ U (actualBinarySourceDenominatorConstant d) b,
    actualBinaryPolynomialStepDegree (ZMod 2) _ U _ hdeg.le hU b,
    actualBinaryMatrixStep (ZMod 2) _ _ U hU b, ?_⟩
  intro i j
  rfl

#audit_namespace LogicLineages.CartierObserverCurrent.FullBinaryMatrix
end LogicLineages.CartierObserverCurrent.FullBinaryMatrix
