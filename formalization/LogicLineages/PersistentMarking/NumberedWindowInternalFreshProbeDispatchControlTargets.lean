module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalProbeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchDefinitions
@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlTargets
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open NumberedWindowInternalFreshProbeDispatchProgram
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- AST identity, not effectivity, semantic indistinguishability, or
an arithmetic theorem about opaque natural-number functions. -/
def ExactDispatchControlAST : Prop :=
  (∀ n, zeroAt n = InternalAcceptance.constantZero n) ∧
  (∀ n k, literal n k = InternalFixedWindowVertexDispatch.constant n k) ∧
  predOne = InternalEqualityTest.predecessor ∧
  compareNumbers = InternalEqualityTest.equalityTest ∧
  (∀ n (p a b : Program n), chooseBranch p a b = InternalAcceptance.branch p a b) ∧
  (∀ n (p q : Program n), bothOne p q = InternalAcceptance.conjunction p q)

def ExactDispatchObjectTypeCode : Prop :=
  ∀ τ, NumberedWindowProbeCode.code τ = NumberedWindowInternalProbeTargets.typeCode τ

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlTargets
