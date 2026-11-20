module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldStateEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserStepEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldIterationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch)
open InternalAcceptanceCalibrationProof (evalBranch)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseFieldCell (chosenCell cellGood cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (flagOfCell headTailOfCell)
open NumberedWindowInternalSparseFieldParserStepEvaluationProof (flagMissing)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathAdvanceTargets
open NumberedWindowInternalSparsePositiveFold
open NumberedWindowInternalSparsePositiveFoldTargets
open NumberedWindowInternalSparsePositiveFoldStateEvaluationProof

abbrev RawState := Nat × Nat

def stateNext (entries : Entries) (s : Settings) (c ty : Nat) (p : RawState) : RawState :=
  if p.1 = 0 then p else
    match chosenCell p.1 with
    | none => (0,0)
    | some (hop,tail) => (tail,encodeState (packedOriginalAdvance entries s c ty p.2 hop))

def repeatStates (f : RawState → RawState) : Nat → RawState → RawState
  | 0,p => p
  | n+1,p => f (repeatStates f n p)

theorem repeatHead (f : RawState → RawState) (n : Nat) (p : RawState) :
    repeatStates f (n+1) p = repeatStates f n (f p) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [repeatStates,ih,repeatStates]

theorem repeatStable (f : RawState → RawState) (p : RawState) (fixed : f p = p) (n : Nat) :
    repeatStates f n p = p := by
  induction n with
  | zero => rfl
  | succ n ih => rw [repeatStates,ih,fixed]

theorem stepValue (entries : Entries) (s : Settings) (raw : Program 5) (least : Program 3)
    (cal : ActualAdvanceCalibration entries s raw least)
    (k cursor current c ty start orig : Nat) :
    eval6 (iterateStep raw least) k (encodeScratch cursor current) c ty start orig =
      let next := stateNext entries s c ty (cursor,current)
      encodeScratch next.1 next.2 := by
  unfold iterateStep eval6
  rw [evalBranch]
  change (if eval6 scratchCursor k (encodeScratch cursor current) c ty start orig = 0 then
    encodeScratch cursor current else
    eval6 (branch (onCursor cellGood) dead (updateCell raw least))
      k (encodeScratch cursor current) c ty start orig) = _
  rw [cursorValue]
  cases cursor with
  | zero => simp [stateNext]
  | succ n =>
    rw [if_neg (Nat.succ_ne_zero n)]
    unfold eval6
    rw [evalBranch]
    change (if eval6 (onCursor cellGood) k (encodeScratch (n+1) current) c ty start orig = 0 then
      eval6 dead k (encodeScratch (n+1) current) c ty start orig else
      eval6 (updateCell raw least) k (encodeScratch (n+1) current) c ty start orig) = _
    rw [onCursorValue]
    cases found : chosenCell (n+1) with
    | none =>
      have bad : run cellGood (n+1) = 0 := flagMissing found
      rw [bad,if_pos rfl,deadValue]
      simp [stateNext,found]
    | some both =>
      obtain ⟨hop,tail⟩ := both
      have good := flagOfCell found
      obtain ⟨headV,tailV⟩ := headTailOfCell found
      rw [good,if_neg (Nat.succ_ne_zero 0),updateValue,headV,tailV,cal c ty current hop]
      simp [stateNext,found]

theorem iterationValue (entries : Entries) (s : Settings) (raw : Program 5) (least : Program 3)
    (cal : ActualAdvanceCalibration entries s raw least) (c ty start orig fuel : Nat) :
    evaluate (iterateState raw least) (fuel ::ᵥ c ::ᵥ ty ::ᵥ start ::ᵥ orig ::ᵥ nil) =
      let done := repeatStates (stateNext entries s c ty) fuel (orig,start)
      encodeScratch done.1 done.2 := by
  induction fuel with
  | zero => exact initialValue c ty start orig
  | succ k ih =>
    let prev := repeatStates (stateNext entries s c ty) k (orig,start)
    change eval6 (iterateStep raw least) k
      (evaluate (iterateState raw least) (k ::ᵥ c ::ᵥ ty ::ᵥ start ::ᵥ orig ::ᵥ nil))
      c ty start orig = _
    rw [ih]
    change eval6 (iterateStep raw least) k (encodeScratch prev.1 prev.2) c ty start orig = _
    exact stepValue entries s raw least cal k prev.1 prev.2 c ty start orig

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldIterationProof
