module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundMachineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundRowsNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitMachineProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch constantZero)
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalEqualityTestEvaluationProof (vectorOne)
open InternalArithmeticPrograms (addition)
open InternalArithmeticProgramsEvaluationProof (exactAdditionEvaluation)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalSparsePathEnvelope (run field)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (tape atSlot)
open NumberedWindowInternalLiteralLambdaLexicalGateNumericProof
  (evalConsOf evalBinaryComposition evalTernaryComposition)
open NumberedWindowInternalLiteralSingletonAtomsNumericProof
  (singletonSyntax exact_LiteralSingletonSyntaxBit)
open NumberedWindowInternalLiteralSingletonBoundMachineProof
open NumberedWindowInternalLiteralSingletonBoundRowsNumericProof
  (exact_LiteralBoundShapeBit exact_LiteralBoundShape exact_LiteralBoundFields)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowFieldAlgorithm (unpackNode packNode)
open NumberedWindowShiftAlgorithm (output)

/-- Index of the replacement node (tape slot 2) plus the depth (slot 1). -/
def shiftRaisedIndex : Program 3 := .composition addition ![boundIndex,.projection 1]

def shiftBoundCode : Program 3 :=
  consOf (literal 3 1) (consOf boundType (consOf shiftRaisedIndex (constantZero 3)))

def shiftBoundRaised : Program 3 := .composition .succ (fun _ : Fin 1 => shiftBoundCode)

def shiftHitFallback (H : Program 2) : Program 3 :=
  .composition H ![.projection 0,.projection 1]

/-- On the tape `[a,d,a]`: the syntax guard on the replacement, then the
bound-literal shape test, then the physical raised node. Every other
input is sent to the supplied program on `[a,d]`. -/
def shiftHitDispatch (V : Program 1) (H : Program 2) : Program 3 :=
  branch (singletonSyntax V) (shiftHitFallback H)
    (branch (onRaw boundShape 2) (shiftHitFallback H) shiftBoundRaised)

/-- The shift-hit program with a physical bound-literal row. The supplied
`H` remains the fallback for all remaining replacement shapes. -/
def shiftHitBound (V : Program 1) (H : Program 2) : Program 2 :=
  .composition (shiftHitDispatch V H) ![.projection 0,.projection 1,.projection 0]

/-- Tag 1 of the original shift step at cutoff and offset zero: the row
does not consult the recursion table. -/
theorem exact_ShiftHitBoundLiteral (a d ty i : Nat) (well : (syntaxBits a).1 = true)
    (shaped : unpackNode a = some (1,[ty,i])) :
    shiftHitValue a d = packNode 1 [ty,i+d] + 1 := by
  have first : (output d 0 a).1 = some (NumberedWindowShiftAlgorithm.computed d 0 a a 0).1 := by
    change (if (syntaxBits a).1 = true then
      some (NumberedWindowShiftAlgorithm.computed d 0 a a 0).1 else none) = _
    rw [if_pos well]
  have row : (NumberedWindowShiftAlgorithm.computed d 0 a a 0).1 = packNode 1 [ty,i+d] := by
    change ((unpackNode a).map (fun p => NumberedWindowShiftAlgorithm.termParts
      (NumberedWindowShiftAlgorithm.table d 0 a a) d 0 0 p.1 p.2)).getD 0 = _
    rw [shaped]
    simp [NumberedWindowShiftAlgorithm.termParts]
  rw [shiftHitValue,first,row,Option.getD_some]

theorem exact_LiteralShiftBoundRaised (a d ty i : Nat) (h : unpackNode a = some (1,[ty,i])) :
    evaluate shiftBoundRaised (tape a d a) = packNode 1 [ty,i+d] + 1 := by
  obtain ⟨t,x⟩ := exact_LiteralBoundFields a ty i h
  have sum : evaluate addition (i ::ᵥ d ::ᵥ nil) = i + d := exactAdditionEvaluation i d
  rw [shiftBoundRaised,evaluate,vectorOne]
  change evaluate shiftBoundCode (tape a d a) + 1 = _
  rw [shiftBoundCode,evalConsOf,evalConsOf,evalConsOf,literalEvaluation,boundType,atSlot,
    shiftRaisedIndex,evalBinaryComposition,boundIndex,atSlot]
  change NumberedWindowPairAlgorithm.pair 1
    (NumberedWindowPairAlgorithm.pair (run (field 0) a)
      (NumberedWindowPairAlgorithm.pair
        (evaluate addition (run (field 1) a ::ᵥ d ::ᵥ nil)) 0 + 1) + 1) + 1 + 1 = _
  rw [t,x,sum]
  rfl

/-- The physical row preserves the exact installed contract. -/
theorem exact_ShiftHitBoundFit (V : Program 1) (H : Program 2)
    (vFit : ActualRawSyntax V) (hFit : ShiftHitFit H) : ShiftHitFit (shiftHitBound V H) := by
  intro a d
  have fallback : evaluate (shiftHitFallback H) (tape a d a) = shiftHitValue a d := by
    rw [shiftHitFallback,evalBinaryComposition]
    exact hFit a d
  rw [shiftHitBound,evalTernaryComposition]
  change evaluate (shiftHitDispatch V H) (tape a d a) = _
  rw [shiftHitDispatch,evalBranch,exact_LiteralSingletonSyntaxBit V vFit]
  cases both : ((syntaxBits a).1 && (syntaxBits a).1) with
  | false =>
    rw [Bool.toNat_false,if_pos rfl]
    exact fallback
  | true =>
    simp only [Bool.and_eq_true] at both
    obtain ⟨well,_⟩ := both
    simp only [Bool.toNat_true,show (1 : Nat) ≠ 0 by decide,if_false]
    rw [evalBranch,atSlot]
    change (if run boundShape a = 0 then evaluate (shiftHitFallback H) (tape a d a)
      else evaluate shiftBoundRaised (tape a d a)) = _
    rcases exact_LiteralBoundShapeBit a with no | yes
    · rw [no,if_pos rfl]
      exact fallback
    · rw [yes,if_neg (by decide : (1 : Nat) ≠ 0)]
      obtain ⟨ty,idx,shaped⟩ := (exact_LiteralBoundShape a).mp yes
      rw [exact_LiteralShiftBoundRaised a d ty idx shaped,
        exact_ShiftHitBoundLiteral a d ty idx well shaped]

/-- An installable shift-hit program whose bound-literal row is physical. -/
theorem exact_PhysicalShiftHit (V : Program 1) (vFit : ActualRawSyntax V) :
    ∃ H : Program 2, ShiftHitFit (shiftHitBound V H) := by
  obtain ⟨H,fit⟩ := exact_LiteralShiftHit
  exact ⟨H,exact_ShiftHitBoundFit V H vFit fit⟩

#print axioms shiftHitBound
#print axioms exact_ShiftHitBoundLiteral
#print axioms exact_LiteralShiftBoundRaised
#print axioms exact_ShiftHitBoundFit
#print axioms exact_PhysicalShiftHit
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitMachineProof
