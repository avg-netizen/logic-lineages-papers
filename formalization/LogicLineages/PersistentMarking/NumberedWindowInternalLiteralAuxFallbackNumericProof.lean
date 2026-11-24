module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFallbackDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickNumericASTProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericThinChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFallbackNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowRawContextAlgorithm (context next Frame)
open NumberedWindowInternalSparsePathEnvelope (run nodeGood)
open NumberedWindowInternalSparseRawFunctionFrame
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (tape atSlot)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (termOne)
open NumberedWindowInternalSparseRawFunctionFrameNumericThinChecks (exact_AllRawFunctionFrame)
open NumberedWindowInternalSparseRawTick (fallbackValue tagFiveTest)
open NumberedWindowInternalSparseRawTickTargets (ActualFallback)
open NumberedWindowInternalSparseRawTickNumericASTProof (tagFiveOne tagFiveZero)
open NumberedWindowInternalLiteralAuxFallback

private theorem excludedContext (tag : Nat) (fields : List Nat) (dst : Nat × List Nat)
    (d c f a : Nat) (notFive : ¬ ∃ w, (tag,fields) = (5,[w])) :
    context tag fields (6,[d,c,f,a]) dst = none := by
  unfold context
  split
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · exact False.elim (notFive ⟨_,rfl⟩)
  · rfl

private theorem fallbackWithoutFive {q w r d c f a : Nat}
    (shape : unpackNode q = some (6,[d,c,f,a]))
    (absent : ¬ ∃ child, unpackNode w = some (5,[child])) :
    fallbackValue q w r = none := by
  cases hw : unpackNode w with
  | none => simp [fallbackValue,hw]
  | some n =>
    obtain ⟨tag,fields⟩ := n
    cases hd : unpackNode r with
    | none => simp [fallbackValue,next,hw,shape,hd]
    | some dest =>
      have no : ¬ ∃ child, (tag,fields) = (5,[child]) := by
        rintro ⟨child,h⟩
        exact absent ⟨child,hw.trans (congrArg some h)⟩
      simpa only [fallbackValue,hw,next,shape,hd,Option.bind_eq_bind,Option.bind_some] using
        excludedContext tag fields dest d c f a no

private theorem auxBit (q w r : Nat) :
    evaluate sourceIsAux (tape q w r) = 0 ∨ evaluate sourceIsAux (tape q w r) = 1 := by
  rw [sourceIsAux,atSlot]
  change run termShape q = 0 ∨ run termShape q = 1
  unfold termShape run nodeGood
  rw [conjunctionEvaluation]
  split <;> simp

/-- Every ordered raw input, including malformed witnesses, has exactly
the same contextual fallback value after exposing the aux-source branch.
This allows selection of this actual AST in the original typed checker. -/
theorem exact_AuxiliaryFallback (other : Program 3) (old : ActualFallback other) :
    ActualFallback (auxiliaryFallback other) := by
  intro q w r
  change evaluate (auxiliaryFallback other) (tape q w r) = _
  rw [auxiliaryFallback,evalBranch]
  rcases auxBit q w r with test | test
  · rw [test,if_pos rfl]
    exact old q w r
  · have seen : run termShape q = 1 := by
      rw [sourceIsAux,atSlot] at test
      exact test
    obtain ⟨d,c,f,a,shape⟩ := (termOne q).mp seen
    rw [test,if_neg (by decide : (1 : Nat) ≠ 0),evalBranch]
    by_cases five : ∃ child, unpackNode w = some (5,[child])
    · obtain ⟨child,hw⟩ := five
      rw [(tagFiveOne q w r).mpr ⟨child,hw⟩,if_neg (by decide : (1 : Nat) ≠ 0),exact_AllRawFunctionFrame]
      simp [tagFiveNext,fallbackValue,hw]
    · rw [tagFiveZero q w r five,if_pos rfl,fallbackWithoutFive shape five]
      rfl

#print axioms exact_AuxiliaryFallback
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFallbackNumericProof
