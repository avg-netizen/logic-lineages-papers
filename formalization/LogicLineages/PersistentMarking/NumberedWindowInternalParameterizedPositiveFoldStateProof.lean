module
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFold
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldStateEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFold
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalListCodec (consCode)
open InternalListCodecEvaluationProof (consEvaluation)
open InternalEqualityTestEvaluationProof (vectorTwo)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePositiveFold (scratchCurrent onCursor)
open NumberedWindowInternalSparsePositiveFoldTargets (encodeScratch)
open NumberedWindowInternalSparsePositiveFoldStateEvaluationProof
  (eval6 vectorFour currentValue onCursorValue)

def evalPhysicalAdvance (A : Program 4) (c ty current hop : Nat) : Nat :=
  evaluate A (c ::ᵥ ty ::ᵥ current ::ᵥ hop ::ᵥ nil)

/-- The physical A receives the actual context, type, previous optional-state
code, and physical parser's head, in the original order. -/
theorem exact_ParameterizedAdvanceValue (A : Program 4) (k cursor current c ty start orig : Nat) :
    eval6 (advanceAt A) k (encodeScratch cursor current) c ty start orig =
      evalPhysicalAdvance A c ty current (run cellHead cursor) := by
  unfold advanceAt eval6
  rw [evaluate,vectorFour]
  change evalPhysicalAdvance A c ty
    (eval6 scratchCurrent k (encodeScratch cursor current) c ty start orig)
    (eval6 (onCursor cellHead) k (encodeScratch cursor current) c ty start orig) = _
  rw [currentValue,onCursorValue]

theorem exact_ParameterizedUpdateValue (A : Program 4) (k cursor current c ty start orig : Nat) :
    eval6 (updateAt A) k (encodeScratch cursor current) c ty start orig =
      encodeScratch (run cellTail cursor) (evalPhysicalAdvance A c ty current (run cellHead cursor)) := by
  unfold updateAt eval6
  rw [evaluate,vectorTwo]
  change evaluate consCode
    (eval6 (onCursor cellTail) k (encodeScratch cursor current) c ty start orig ::ᵥ
     eval6 (advanceAt A) k (encodeScratch cursor current) c ty start orig ::ᵥ nil) = _
  rw [onCursorValue,exact_ParameterizedAdvanceValue,consEvaluation] <;> rfl

#print axioms exact_ParameterizedAdvanceValue
#print axioms exact_ParameterizedUpdateValue

end LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFold
