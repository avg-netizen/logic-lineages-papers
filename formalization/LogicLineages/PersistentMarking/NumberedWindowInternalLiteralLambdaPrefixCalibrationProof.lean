module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixStepNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixLoopNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixCalibrationProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathAdvanceTargets (packedRaw)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorOne)
open NumberedWindowInternalLiteralLambdaLexicalGateNumericProof (typedTape)
open NumberedWindowInternalLiteralLambdaPrefixMachineProof
open NumberedWindowInternalLiteralLambdaPrefixStateNumericProof
open NumberedWindowInternalLiteralLambdaPrefixStepNumericProof
open NumberedWindowInternalLiteralLambdaTypedChildNumericProof

open NumberedWindowInternalLiteralLambdaPrefixLoopNumericProof
open NumberedWindowInternalLiteralTickNumericProof (numericIter)

attribute [local irreducible] packedRaw prefixTick prefixLive prefixOwn isLambdaPrefix typedFrameCode typedStateCode

set_option maxHeartbeats 230000 in
theorem exact_LambdaPrefixBounded (W : Program 3) (s : Settings) (fit : ActualPackedWindow s W)
    (xs : Entries) (w fuel c t q r : Nat) (bound : w ≤ fuel)
    (accepted : packedRaw xs s c t q w r = true) :
    run cellHead (prefixIter W fuel (typedStateCode 1 (typedFrameCode c t q w r))) = 1 := by
  induction w using Nat.strongRecOn generalizing fuel c t q r with
  | ind w ih =>
    cases fuel with
    | zero => exact stateHeadValue 1 _
    | succ n =>
      rw [prefixIter,numericIter,evalPrefixTickOnFrame]
      rcases evalLambdaPrefixBit c t q w r with zero | one
      · rw [evalLambdaPrefixLiveStop W c t q w r zero]
        change run cellHead (prefixIter W n (typedStateCode 1 0)) = 1
        rw [prefixIterTerminal,stateHeadValue]
      · obtain ⟨child,wtag⟩ := evalLambdaPrefixWitness c t q w r one
        obtain ⟨d,k,a,b,src,dst,ty,below,left,right,next⟩ :=
          exact_OriginalNumericLambdaTypedChild xs s c t q w r child wtag accepted
        rw [evalLambdaPrefixLiveGood W s fit c t q w r d a child b k one src dst wtag ty left right]
        exact ih child below n _ _ _ _ (by omega) next

/-- Adding the physical prefix guard cannot reject a single numerically
accepted original typed raw step, at any context or raw endpoint. -/
theorem exact_LambdaPrefixCalibrated (W : Program 3) (s : Settings) (fit : ActualPackedWindow s W)
    (xs : Entries) (c t q w r : Nat) (accepted : packedRaw xs s c t q w r = true) :
    evaluate (prefixOwn W) (typedTape c t q w r) = 1 := by
  rw [evalPrefixOwn]
  exact exact_LambdaPrefixBounded W s fit xs w w c t q r (Nat.le_refl w) accepted

#print axioms exact_LambdaPrefixBounded
#print axioms exact_LambdaPrefixCalibrated
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixCalibrationProof
