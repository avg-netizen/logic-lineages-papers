module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (nodeArity)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverHeaderFieldsTargets

theorem exact_CoverHeaderUnpackNode : ExactCoverHeaderUnpackNode := by
  intro tag arity raw
  unfold header
  have lit : run (literal 1 tag) raw = tag := literalEvaluation 1 tag (raw ::ᵥ nil)
  exact nodeArity (literal 1 tag) arity raw tag lit

#print axioms exact_CoverHeaderUnpackNode

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsNumericProof
