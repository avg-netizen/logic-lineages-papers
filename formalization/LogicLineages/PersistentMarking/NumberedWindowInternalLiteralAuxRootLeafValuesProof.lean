module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericASTProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafValuesProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalEqualityTestEvaluationProof (exactEqualityEvaluation vectorOne vectorTwo)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux)
open NumberedWindowInternalLiteralAuxRootLeaf
open NumberedWindowInternalSparseRawFunctionFrame (onRaw termShape frameSlot)
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (tape atSlot)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (termOne termFields)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead)
open NumberedWindowInternalSparsePathEnvelope (run field nodeGood)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (bothAccept)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt flagOfCell headTailOfCell)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo literalEvaluation)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowFieldAlgorithm (pack packNode unpackNode)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)

theorem auxValue (q w r : Nat) :
    evaluate sourceIsAux (tape q w r) = 0 ∨
      (evaluate sourceIsAux (tape q w r) = 1 ∧
        ∃ d c f a, unpackNode q = some (6,[d,c,f,a])) := by
  rw [sourceIsAux,atSlot]
  change run termShape q = 0 ∨ (run termShape q = 1 ∧ _)
  rw [← termOne q,and_self]
  unfold termShape run nodeGood
  rw [conjunctionEvaluation]
  split <;> simp

theorem lambdaHeaderOf (f : Nat) (fs : List Nat) (h : unpackNode f = some (2,fs)) :
    run lambdaHeader f = 1 := by
  have cell := cellAt 2 (pack fs)
  have hit := codeOfNode h
  have key : run cellGood f = 1 := by
    rw [hit]
    exact flagOfCell cell
  have head : run cellHead f = 2 := by
    rw [hit]
    exact (headTailOfCell cell).1
  unfold lambdaHeader
  rw [bothAccept]
  refine ⟨key,?_⟩
  unfold run
  rw [evaluate,vectorTwo]
  change evaluate InternalEqualityTest.equalityTest
    (evaluate cellHead (f ::ᵥ nil) ::ᵥ
      evaluate (NumberedWindowInternalFreshProbeDispatchProgram.literal 1 2) (f ::ᵥ nil) ::ᵥ nil) = 1
  have hv := literalEvaluation 1 2 (f ::ᵥ nil)
  change evaluate cellHead (f ::ᵥ nil) = 2 at head
  rw [head,hv,exactEqualityEvaluation]
  rfl

theorem functionHeaderOf (q w r d c f a : Nat) (fs : List Nat)
    (hq : unpackNode q = some (6,[d,c,f,a])) (hf : unpackNode f = some (2,fs)) :
    evaluate functionLambdaHeader (tape q w r) = 1 := by
  change evaluate lambdaHeader (List.Vector.ofFn (fun i : Fin 1 =>
    evaluate ((![frameSlot 2 0] : Fin 1 → Program 3) i) (tape q w r))) = 1
  rw [vectorOne]
  change run lambdaHeader (evaluate (frameSlot 2 0) (tape q w r)) = 1
  rw [frameSlot,atSlot]
  change run lambdaHeader (run (field 2) q) = 1
  rw [(termFields hq).2.2.1]
  exact lambdaHeaderOf f fs hf

private theorem consEval (p q : Program 3) (v : List.Vector Nat 3) :
    evaluate (consOf p q) v = pair (evaluate p v) (evaluate q v) + 1 := by
  rw [consOf,compositeTwo]
  exact NumberedWindowInternalSparsePairEvaluationProof.consValue _ _

theorem expectedValue (q w r d c f a : Nat) (hq : unpackNode q = some (6,[d,c,f,a])) :
    evaluate expectedBottom (tape q w r) = packNode 3 [c] := by
  rw [expectedBottom,consEval,consEval,literalEvaluation,frameSlot,atSlot]
  change pair 3 (pair (run (field 1) q) (evaluate (constantZero 3) (tape q w r)) + 1) + 1 = _
  rw [(termFields hq).2.1]
  rfl

theorem targetValue (q w r d c f a : Nat) (hq : unpackNode q = some (6,[d,c,f,a]))
    (same : r = packNode 3 [c]) : evaluate targetBottom (tape q w r) = 1 := by
  unfold targetBottom
  rw [evaluate,vectorTwo]
  change evaluate InternalEqualityTest.equalityTest (r ::ᵥ evaluate expectedBottom (tape q w r) ::ᵥ nil) = _
  rw [expectedValue q w r d c f a hq,← same,exactEqualityEvaluation,if_pos rfl]

#print axioms auxValue
#print axioms functionHeaderOf
#print axioms targetValue
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafValuesProof
