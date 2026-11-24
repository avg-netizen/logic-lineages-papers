module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBoundedFallbackDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowRawContextOwnFuelProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBoundedFallbackNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalLessThanEvaluationProof (exactLessThanEvaluation)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo)
open NumberedWindowRawContextAlgorithm (Frame next)
open NumberedWindowFieldAlgorithm (pack unpackNode unpack)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowInternalSparsePathEnvelope (run exactBody)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue bodyArity)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
  (cellAt headTailOfCell emptyUnpack splitUnpack)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (predEvaluation)
open NumberedWindowInternalSparseRawFunctionFrame (encodeFrame)
open NumberedWindowInternalSparseRawTick (fallbackValue)
open NumberedWindowInternalSparseRawTickTargets (ActualFallback)
open NumberedWindowRawContextOwnFuelProof (exact_ContextWitnessDescends)
open NumberedWindowInternalLiteralBoundedFallback

private theorem unpackPacked (xs : List Nat) : unpack (pack xs) = some xs := by
  induction xs with
  | nil => exact emptyUnpack
  | cons x xs ih =>
    change unpack (pair x (pack xs) + 1) = _
    rw [splitUnpack (cellAt x (pack xs)),ih]
    rfl

private theorem candidateValue (p : Program 1) (c w : Nat) :
    evaluate (atCandidate p) (c ::ᵥ w ::ᵥ nil) = run p c := by
  unfold atCandidate run
  rw [evaluate,vectorOne]
  rfl

private theorem ltValue (c w : Nat) :
    evaluate descends (c ::ᵥ w ::ᵥ nil) = if run childSelector c < w then 1 else 0 := by
  unfold descends
  rw [evaluate,vectorTwo]
  change evaluate InternalLessThan.ltTest
    (evaluate (atCandidate childSelector) (c ::ᵥ w ::ᵥ nil) ::ᵥ w ::ᵥ nil) = _
  rw [candidateValue,exactLessThanEvaluation]

private theorem shapeValue (c : Nat) :
    run frameShape c = 1 ↔ ∃ xs, unpack c.pred = some xs ∧ xs.length = 3 := by
  rw [frameShape,applyValue]
  have pr : run NumberedWindowInternalFreshProbeDispatchProgram.predOne c = c.pred := predEvaluation c
  rw [pr,bodyArity]

private theorem childValue (q w r : Nat) : run childSelector (encodeFrame (some (q,w,r))) = w := by
  unfold childSelector
  rw [applyValue,applyValue]
  have pr : run NumberedWindowInternalFreshProbeDispatchProgram.predOne (encodeFrame (some (q,w,r))) =
      pack [q,w,r] := predEvaluation _
  rw [pr]
  have x : run NumberedWindowInternalSparseFieldCell.cellTail (pack [q,w,r]) = pack [w,r] :=
    (headTailOfCell (cellAt q (pack [w,r]))).2
  have y : run NumberedWindowInternalSparseFieldCell.cellHead (pack [w,r]) = w :=
    (headTailOfCell (cellAt w (pack [r]))).1
  rw [x,y]

theorem exact_ClipNone (w : Nat) : evaluate clip (0 ::ᵥ w ::ᵥ nil) = 0 := by
  rw [clip,evalBranch,admitted,conjunctionEvaluation,candidateValue]
  have notShape : run frameShape 0 ≠ 1 := by
    intro h
    obtain ⟨xs,parsed,arity⟩ := (shapeValue 0).mp h
    change unpack 0 = some xs at parsed
    rw [emptyUnpack] at parsed
    cases parsed
    cases arity
  simp [notShape] <;> rfl

theorem exact_ClipSmaller (q w r parent : Nat) (smaller : w < parent) :
    evaluate clip (encodeFrame (some (q,w,r)) ::ᵥ parent ::ᵥ nil) = encodeFrame (some (q,w,r)) := by
  let frame := encodeFrame (some (q,w,r))
  have good : run frameShape frame = 1 := (shapeValue frame).mpr
    ⟨[q,w,r],unpackPacked [q,w,r],rfl⟩
  rw [clip,evalBranch,admitted,conjunctionEvaluation,candidateValue,good,ltValue,childValue,
    if_pos smaller]
  rfl

/-- The actual original fallback already passes the descending guard on
every successfully decoded raw tape. The new physical program therefore
preserves its original evaluation even on malformed inputs. -/
theorem exact_DescendingFallback (other : Program 3) (old : ActualFallback other) :
    ActualFallback (fallback other) := by
  intro q w r
  unfold fallback
  rw [evaluate,vectorTwo]
  change evaluate clip (evaluate other (q ::ᵥ w ::ᵥ r ::ᵥ nil) ::ᵥ w ::ᵥ nil) = _
  rw [old]
  cases out : fallbackValue q w r with
  | none => exact exact_ClipNone w
  | some frame =>
    obtain ⟨q',w',r'⟩ := frame
    cases parsed : unpackNode w with
    | none => simp [fallbackValue,parsed] at out
    | some p =>
      obtain ⟨tag,fs⟩ := p
      have move : next tag fs q r = some (q',w',r') := by simpa [fallbackValue,parsed] using out
      exact exact_ClipSmaller q' w' r' w (exact_ContextWitnessDescends parsed move)

#print axioms exact_ClipNone
#print axioms exact_ClipSmaller
#print axioms exact_DescendingFallback
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBoundedFallbackNumericProof
