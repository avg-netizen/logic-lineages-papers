module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitMachineProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitAtomsMachineProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch)
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorOne)
open NumberedWindowInternalSparsePathEnvelope (run nodeGood)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (tape atSlot)
open NumberedWindowInternalLiteralLambdaLexicalGateNumericProof
  (evalBinaryComposition evalTernaryComposition)
open NumberedWindowInternalLiteralAtomicRawGuardProof (freeTest bottomTest freeCode bottomCode)
open NumberedWindowInternalLiteralSingletonAtomsNumericProof
  (singletonSyntax retainSingleton singletonAtomicDispatch exact_LiteralSingletonSyntaxBit)
open NumberedWindowInternalLiteralSingletonBoundMachineProof
open NumberedWindowInternalLiteralSingletonShiftHitMachineProof
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)
open NumberedWindowAtomicRawStepFieldProof (freeView bottomView codeOfNode)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowFieldAlgorithm (unpackNode packNode)
open NumberedWindowShiftAlgorithm (output)

/-- On the tape `[a,d,a]`: the syntax guard on the replacement, then the
original free/bottom atom dispatch, whose retain branch returns the
replacement plus one. Guard failure and every non-atom shape go to the
supplied program on `[a,d]`. -/
def shiftAtomDispatch (V : Program 1) (H : Program 2) : Program 3 :=
  branch (singletonSyntax V) (shiftHitFallback H)
    (singletonAtomicDispatch (shiftHitFallback H))

def shiftHitAtoms (V : Program 1) (H : Program 2) : Program 2 :=
  .composition (shiftAtomDispatch V H) ![.projection 0,.projection 1,.projection 0]

/-- One front for all three literal rows: bound literals are raised by
the saved bound front, free and bottom literals are retained, and the
supplied `H` is reached only by invalid codes and the remaining tags
(2, 4, 5, 6), whose rows read the course-of-values table. -/
def shiftHitLiterals (V : Program 1) (H : Program 2) : Program 2 :=
  shiftHitBound V (shiftHitAtoms V H)

private theorem atomBit (tag arity q : Nat) :
    run (nodeGood (literal 1 tag) arity) q = 0 ∨ run (nodeGood (literal 1 tag) arity) q = 1 := by
  unfold run nodeGood
  rw [actualConjunctionEvaluation]
  split <;> simp

/-- Tags 0 and 3 of the original shift step return the node unchanged,
for any payload and without consulting the recursion table. The syntax
premise is necessary: without it the original value is `1`. -/
theorem exact_ShiftHitAtomLiteral (a d tag : Nat) (fs : List Nat)
    (well : (syntaxBits a).1 = true) (shaped : unpackNode a = some (tag,fs))
    (atom : tag = 0 ∨ tag = 3) : shiftHitValue a d = a + 1 := by
  have first : (output d 0 a).1 = some (NumberedWindowShiftAlgorithm.computed d 0 a a 0).1 := by
    change (if (syntaxBits a).1 = true then
      some (NumberedWindowShiftAlgorithm.computed d 0 a a 0).1 else none) = _
    rw [if_pos well]
  have row : (NumberedWindowShiftAlgorithm.computed d 0 a a 0).1 = a := by
    have code : a = packNode tag fs := codeOfNode shaped
    change ((unpackNode a).map (fun p => NumberedWindowShiftAlgorithm.termParts
      (NumberedWindowShiftAlgorithm.table d 0 a a) d 0 0 p.1 p.2)).getD 0 = _
    rw [shaped]
    rcases atom with rfl | rfl
    · first
        | exact code.symm
        | simpa [NumberedWindowShiftAlgorithm.termParts] using code.symm
    · first
        | exact code.symm
        | simpa [NumberedWindowShiftAlgorithm.termParts] using code.symm
  rw [shiftHitValue,first,row,Option.getD_some]

/-- The atom front preserves the exact installed contract at every input. -/
theorem exact_ShiftHitAtomsFit (V : Program 1) (H : Program 2)
    (vFit : ActualRawSyntax V) (hFit : ShiftHitFit H) : ShiftHitFit (shiftHitAtoms V H) := by
  intro a d
  have fallback : evaluate (shiftHitFallback H) (tape a d a) = shiftHitValue a d := by
    rw [shiftHitFallback,evalBinaryComposition]
    exact hFit a d
  have retained : evaluate retainSingleton (tape a d a) = a + 1 := by
    rw [retainSingleton,evaluate,vectorOne]
    rfl
  rw [shiftHitAtoms,evalTernaryComposition]
  change evaluate (shiftAtomDispatch V H) (tape a d a) = _
  rw [shiftAtomDispatch,evalBranch,exact_LiteralSingletonSyntaxBit V vFit]
  cases both : ((syntaxBits a).1 && (syntaxBits a).1) with
  | false =>
    rw [Bool.toNat_false,if_pos rfl]
    exact fallback
  | true =>
    simp only [Bool.and_eq_true] at both
    obtain ⟨well,_⟩ := both
    simp only [Bool.toNat_true,show (1 : Nat) ≠ 0 by decide,if_false]
    rw [singletonAtomicDispatch,evalBranch,atSlot]
    change (if run freeTest a = 0 then
        evaluate (branch (onRaw bottomTest 2) (shiftHitFallback H) retainSingleton) (tape a d a)
      else evaluate retainSingleton (tape a d a)) = _
    rcases atomBit 0 2 a with off | atom
    · have no : run freeTest a = 0 := off
      rw [no,if_pos rfl,evalBranch,atSlot]
      change (if run bottomTest a = 0 then evaluate (shiftHitFallback H) (tape a d a)
        else evaluate retainSingleton (tape a d a)) = _
      rcases atomBit 3 1 a with off | bottom
      · have no : run bottomTest a = 0 := off
        rw [no,if_pos rfl]
        exact fallback
      · have yes : run bottomTest a = 1 := bottom
        obtain ⟨ty,code⟩ := (bottomCode a).mp yes
        have shaped : unpackNode a = some (3,[ty]) := by
          rw [code]
          exact bottomView ty
        rw [yes,if_neg (by decide : (1 : Nat) ≠ 0),retained,
          exact_ShiftHitAtomLiteral a d 3 [ty] well shaped (Or.inr rfl)]
    · have yes : run freeTest a = 1 := atom
      obtain ⟨ty,n,code⟩ := (freeCode a).mp yes
      have shaped : unpackNode a = some (0,[ty,n]) := by
        rw [code]
        exact freeView ty n
      rw [yes,if_neg (by decide : (1 : Nat) ≠ 0),retained,
        exact_ShiftHitAtomLiteral a d 0 [ty,n] well shaped (Or.inl rfl)]

/-- The unified front keeps the contract: the saved bound fit applied to
the atom front as its fallback. -/
theorem exact_ShiftHitLiteralsFit (V : Program 1) (H : Program 2)
    (vFit : ActualRawSyntax V) (hFit : ShiftHitFit H) : ShiftHitFit (shiftHitLiterals V H) :=
  exact_ShiftHitBoundFit V (shiftHitAtoms V H) vFit (exact_ShiftHitAtomsFit V H vFit hFit)

theorem exact_PhysicalShiftHitLiterals (V : Program 1) (vFit : ActualRawSyntax V) :
    ∃ H : Program 2, ShiftHitFit (shiftHitLiterals V H) := by
  obtain ⟨H,fit⟩ := exact_LiteralShiftHit
  exact ⟨H,exact_ShiftHitLiteralsFit V H vFit fit⟩

#print axioms shiftHitLiterals
#print axioms exact_ShiftHitAtomLiteral
#print axioms exact_ShiftHitAtomsFit
#print axioms exact_ShiftHitLiteralsFit
#print axioms exact_PhysicalShiftHitLiterals
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitAtomsMachineProof
