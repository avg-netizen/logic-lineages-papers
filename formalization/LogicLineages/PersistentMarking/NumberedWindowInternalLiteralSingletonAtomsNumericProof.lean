module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonDepthNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericASTProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonAtomsNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (conjunction branch constantZero)
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorOne)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (tape atSlot)
open NumberedWindowInternalLiteralAtomicRawGuardProof (freeTest bottomTest freeCode bottomCode)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)
open NumberedWindowInternalLiteralSingletonDepthNumericProof
open NumberedWindowInternalSparsePathEnvelope (run nodeGood)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowAtomicRawStepFieldProof (freeView bottomView)
open NumberedWindowSyntaxAlgorithm (syntaxBits)

def singletonSyntax (V : Program 1) : Program 3 := conjunction (onRaw V 0) (onRaw V 2)

def retainSingleton : Program 3 := .composition .succ (fun _ : Fin 1 => .projection 2)

def singletonAtomicDispatch (U : Program 3) : Program 3 :=
  branch (onRaw freeTest 2) (branch (onRaw bottomTest 2) U retainSingleton) retainSingleton

/-- A transparent singleton interface. Its atom branches operate
literally on the original tape; all remaining constructors still use
the original all-input-calibrated singleton. -/
def singletonAtoms (V : Program 1) (U : Program 3) : Program 3 :=
  branch (singletonSyntax V) (constantZero 3) (singletonAtomicDispatch U)

private theorem boolNode (tag arity q : Nat) :
    run (nodeGood (literal 1 tag) arity) q = 0 ∨ run (nodeGood (literal 1 tag) arity) q = 1 := by
  unfold run nodeGood
  rw [actualConjunctionEvaluation]
  split <;> simp

private theorem retainValue (a d q : Nat) :
    evaluate retainSingleton (tape a d q) = q + 1 := by
  rw [retainSingleton,evaluate,vectorOne]
  rfl

theorem exact_LiteralSingletonSyntaxBit (V : Program 1) (fit : ActualRawSyntax V) (a d q : Nat) :
    evaluate (singletonSyntax V) (tape a d q) = ((syntaxBits a).1 && (syntaxBits q).1).toNat := by
  rw [singletonSyntax,actualConjunctionEvaluation,atSlot,atSlot]
  change (if evaluate V (a ::ᵥ nil) = 1 ∧
    evaluate V (q ::ᵥ nil) = 1 then 1 else 0) = _
  rw [fit,fit]
  cases (syntaxBits a).1 <;> cases (syntaxBits q).1 <;> rfl

theorem exact_LiteralSingletonAtomsCalibration (V : Program 1) (U : Program 3)
    (vFit : ActualRawSyntax V) (uFit : DepthInstanceFit U) : DepthInstanceFit (singletonAtoms V U) := by
  intro a d q
  change evaluate (singletonAtoms V U) (tape a d q) = _
  rw [singletonAtoms,evalBranch,exact_LiteralSingletonSyntaxBit V vFit]
  cases s : ((syntaxBits a).1 && (syntaxBits q).1) with
  | false =>
    simp only [Bool.toNat_false,if_pos rfl]
    simp only [depthInstanceValue,NumberedWindowSingletonAlgorithm.output,s,if_false,Option.map_none,Option.getD_none]
    rfl
  | true =>
    simp only [Bool.toNat_true,show (1 : Nat) ≠ 0 by decide,if_false]
    rw [singletonAtomicDispatch,evalBranch,atSlot]
    change (if run freeTest q = 0 then evaluate (branch (onRaw bottomTest 2) U retainSingleton) (tape a d q)
      else evaluate retainSingleton (tape a d q)) = _
    rcases boolNode 0 2 q with off | atom
    · have no : run freeTest q = 0 := off
      rw [no,if_pos rfl,evalBranch,atSlot]
      change (if run bottomTest q = 0 then evaluate U (tape a d q) else evaluate retainSingleton (tape a d q)) = _
      rcases boolNode 3 1 q with off | bottom
      · have no : run bottomTest q = 0 := off
        rw [no,if_pos rfl]
        exact uFit a d q
      · have yes : run bottomTest q = 1 := bottom
        obtain ⟨ty,rfl⟩ := (bottomCode q).mp yes
        have node := bottomView ty
        have qSyntax : (syntaxBits (NumberedWindowAtomicRawStep.bottomRaw ty)).1 = NumberedWindowAddressAlgorithm.typeBit ty := by
          simp only [syntaxBits,NumberedWindowSyntaxAlgorithm.termNext,node,Option.any_some,
            NumberedWindowSyntaxAlgorithm.termParts]
        rw [qSyntax] at s
        rw [yes,if_neg (by decide : (1 : Nat) ≠ 0),retainValue,depthInstanceValue,
          exact_OriginalSingletonBottom a d _ ty node,s]
        rfl
    · have yes : run freeTest q = 1 := atom
      obtain ⟨ty,n,rfl⟩ := (freeCode q).mp yes
      have node := freeView ty n
      have qSyntax : (syntaxBits (NumberedWindowAtomicRawStep.freeRaw ty n)).1 = NumberedWindowAddressAlgorithm.typeBit ty := by
        simp only [syntaxBits,NumberedWindowSyntaxAlgorithm.termNext,node,Option.any_some,
          NumberedWindowSyntaxAlgorithm.termParts]
      rw [qSyntax] at s
      rw [yes,if_neg (by decide : (1 : Nat) ≠ 0),retainValue,depthInstanceValue,
        exact_OriginalSingletonFree a d _ ty n node,s]
      rfl

#print axioms singletonAtoms
#print axioms exact_LiteralSingletonSyntaxBit
#print axioms exact_LiteralSingletonAtomsCalibration
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonAtomsNumericProof
