module
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldStateProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldIterationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserStepEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFold
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch)
open InternalAcceptanceCalibrationProof (evalBranch)
open NumberedWindowInternalSparseFieldCell (chosenCell cellGood)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (flagOfCell headTailOfCell)
open NumberedWindowInternalSparseFieldParserStepEvaluationProof (flagMissing)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePositiveFold (scratchCursor onCursor dead)
open NumberedWindowInternalSparsePositiveFoldTargets (encodeScratch)
open NumberedWindowInternalSparsePositiveFoldStateEvaluationProof
  (eval6 initialValue cursorValue onCursorValue deadValue)
open NumberedWindowInternalSparsePositiveFoldIterationProof (RawState repeatStates)

def nextPhysicalState (A : Program 4) (c ty : Nat) (p : RawState) : RawState :=
  if p.1 = 0 then p else
    match chosenCell p.1 with
    | none => (0,0)
    | some (hop,tail) => (tail,evalPhysicalAdvance A c ty p.2 hop)

/-- All parser branches are original: empty cursor retains state, a positive
malformed cell goes dead, and an actual found cell supplies A its head. -/
theorem exact_ParameterizedStepValue (A : Program 4) (k cursor current c ty start orig : Nat) :
    eval6 (stepAt A) k (encodeScratch cursor current) c ty start orig =
      let next := nextPhysicalState A c ty (cursor,current)
      encodeScratch next.1 next.2 := by
  unfold stepAt eval6
  rw [evalBranch]
  change (if eval6 scratchCursor k (encodeScratch cursor current) c ty start orig = 0 then
    encodeScratch cursor current else
    eval6 (branch (onCursor cellGood) dead (updateAt A))
      k (encodeScratch cursor current) c ty start orig) = _
  rw [cursorValue]
  cases cursor with
  | zero => simp [nextPhysicalState]
  | succ n =>
    rw [if_neg (Nat.succ_ne_zero n)]
    unfold eval6
    rw [evalBranch]
    change (if eval6 (onCursor cellGood) k (encodeScratch (n+1) current) c ty start orig = 0 then
      eval6 dead k (encodeScratch (n+1) current) c ty start orig else
      eval6 (updateAt A) k (encodeScratch (n+1) current) c ty start orig) = _
    rw [onCursorValue]
    cases found : chosenCell (n+1) with
    | none =>
      have bad : run cellGood (n+1) = 0 := flagMissing found
      rw [bad,if_pos rfl,deadValue]
      simp [nextPhysicalState,found]
    | some both =>
      obtain ⟨hop,tail⟩ := both
      have good := flagOfCell found
      obtain ⟨headV,tailV⟩ := headTailOfCell found
      rw [good,if_neg (Nat.succ_ne_zero 0),exact_ParameterizedUpdateValue,headV,tailV]
      simp [nextPhysicalState,found]

theorem exact_ParameterizedIterationValue (A : Program 4) (c ty start orig fuel : Nat) :
    evaluate (iterateAt A) (fuel ::ᵥ c ::ᵥ ty ::ᵥ start ::ᵥ orig ::ᵥ nil) =
      let done := repeatStates (nextPhysicalState A c ty) fuel (orig,start)
      encodeScratch done.1 done.2 := by
  induction fuel with
  | zero => exact initialValue c ty start orig
  | succ k ih =>
    let prev := repeatStates (nextPhysicalState A c ty) k (orig,start)
    change eval6 (stepAt A) k
      (evaluate (iterateAt A) (k ::ᵥ c ::ᵥ ty ::ᵥ start ::ᵥ orig ::ᵥ nil))
      c ty start orig = _
    rw [ih]
    change eval6 (stepAt A) k (encodeScratch prev.1 prev.2) c ty start orig = _
    exact exact_ParameterizedStepValue A k prev.1 prev.2 c ty start orig

#print axioms exact_ParameterizedStepValue
#print axioms exact_ParameterizedIterationValue

end LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFold
