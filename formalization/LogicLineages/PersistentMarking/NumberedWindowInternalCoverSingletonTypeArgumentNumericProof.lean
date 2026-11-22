module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeArgumentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserRawPairProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesBoundsTableProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeArgumentNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (conjunction constantZero)
open InternalAcceptanceCalibrationProof (evalBranch evalZeroTest actualConjunctionEvaluation)
open InternalPairing (pairing)
open InternalPairingEvaluationProof (exactPairingEvaluation)
open NumberedWindowPairAlgorithm (decode pair)
open NumberedWindowCoverBoundsAlgorithm (bounds argsNext table termMeasure)
open NumberedWindowInternalSparseFieldCell (chosenCell cellGood cellHead cellTail)
open NumberedWindowInternalSparseFieldParserRawPairProof (encodedPair)
open NumberedWindowInternalSparsePathEnvelope (run applyUnary)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (codeOfCell)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverHeaderFieldsNumericProof (exact_CoverHeaderUnpackNode)
open NumberedWindowRawExchangeVerticesBoundsTableProof (termBounds previous)
open NumberedWindowRawExchangeVerticesCodecProof (decoded)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo literalEvaluation)
open NumberedWindowInternalCoverSingletonTypeArgumentTargets

private theorem pairValue (a : Nat) :
    run singletonPair20 a = Encodable.encode ((2,0) : Nat × Nat) := by
  change evaluate (.composition pairing (Fin.cons (literal 1 2) (Fin.cons (constantZero 1) Fin.elim0)))
    (a ::ᵥ nil) = Encodable.encode ((2,0) : Nat × Nat)
  rw [compositeTwo,literalEvaluation]
  have zero : evaluate (constantZero 1) (a ::ᵥ nil) = 0 := rfl
  rw [zero,exactPairingEvaluation] <;> simp only [Encodable.encode_prod_val,Encodable.encode_nat]

private theorem sourcePair {q : Nat} (head : run (header 3 1) q = 1) :
    (bounds (pair q 0 + 1)).2 = ((2,0) : Nat × Nat) := by
  obtain ⟨fields,read,_⟩ := (exact_CoverHeaderUnpackNode 3 1 q).mp head
  have leaf : (bounds q).1 = ((1,0) : Nat × Nat) := by
    rw [termBounds read]
    rfl
  let n := pair q 0
  have split : decode n = some (q,0) := encodedPair q 0
  obtain ⟨_, hq, hz⟩ := decoded split
  change (argsNext (n+1) (table (n+1))) = _
  unfold argsNext
  rw [split]
  change (((table (n+1)).getD q default).1.1+1+((table (n+1)).getD 0 default).2.1,
    max ((table (n+1)).getD q default).1.2 ((table (n+1)).getD 0 default).2.2) = _
  rw [previous (Nat.lt_succ_of_le hq),previous (Nat.lt_succ_of_le hz),leaf]
  rfl

private theorem guard (a : Nat) :
    run singletonTypeGuard a =
      if run cellGood a = 1 ∧ run (header 3 1) (run cellHead a) = 1 ∧ run cellTail a = 0
      then 1 else 0 := by
  unfold singletonTypeGuard
  have outer (p q : Program 1) :
      run (conjunction p q) a = if run p a = 1 ∧ run q a = 1 then 1 else 0 :=
    actualConjunctionEvaluation 1 p q (a ::ᵥ nil)
  rw [outer,outer,applyValue,applyValue]
  have tailZero : run GorbowPRInternalControl.zeroTest (run cellTail a) =
    if run cellTail a = 0 then 1 else 0 := evalZeroTest _
  rw [tailZero]
  by_cases c : run cellGood a = 1 <;>
    by_cases h : run (header 3 1) (run cellHead a) = 1 <;>
    by_cases t : run cellTail a = 0 <;> simp [c,h,t]

theorem exact_CoverSingletonTypeArgs : ExactCoverSingletonTypeArgs := by
  intro A calibrated a
  change run (singletonTypeArgs A) a = Encodable.encode (bounds a).2
  unfold singletonTypeArgs run
  rw [evalBranch]
  change (if run singletonTypeGuard a = 0 then run A a else run singletonPair20 a) = _
  rw [guard]
  by_cases yes : run cellGood a = 1 ∧ run (header 3 1) (run cellHead a) = 1 ∧ run cellTail a = 0
  · rw [if_pos yes,if_neg (by decide),pairValue]
    have read : chosenCell a = some (run cellHead a,0) := by
      change (if run cellGood a = 1 then some (run cellHead a,run cellTail a) else none) = _
      rw [if_pos yes.1,yes.2.2]
    rw [codeOfCell read,sourcePair yes.2.1]
  · rw [if_neg yes,if_pos rfl]
    exact calibrated a

#print axioms exact_CoverSingletonTypeArgs

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeArgumentNumericProof
