module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldIterationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserRawPairProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldFuelProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowInternalSparseFieldCell (chosenCell)
open NumberedWindowInternalSparseFieldParserRawPairProof (tailBound)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
  (codeOfCell emptyUnpack missingUnpack splitUnpack)
open NumberedWindowInternalSparsePathAdvanceTargets
open NumberedWindowInternalSparsePositiveFoldTargets
open NumberedWindowInternalSparsePositiveFoldIterationProof

theorem stateRound (n : Nat) : encodeState (decodeState n) = n := by cases n <;> rfl
theorem optionRound (x : Option Nat) : decodeState (encodeState x) = x := by cases x <;> rfl

private theorem foldNil (entries : Entries) (s : Settings) (c ty start : Nat) :
    originalFold entries s c ty start 0 = decodeState start := by
  simp only [originalFold,emptyUnpack,Option.bind_eq_bind,Option.bind_some,List.foldl_nil]

private theorem foldMissing (entries : Entries) (s : Settings) (c ty start cert : Nat)
    (nz : cert ≠ 0) (missing : chosenCell cert = none) :
    originalFold entries s c ty start cert = none := by
  simp only [originalFold,missingUnpack nz missing,Option.bind_eq_bind,Option.bind_none]

private theorem foldCons (entries : Entries) (s : Settings) (c ty start cert hop tail : Nat)
    (found : chosenCell cert = some (hop,tail)) :
    originalFold entries s c ty start cert =
      originalFold entries s c ty (encodeState (packedOriginalAdvance entries s c ty start hop)) tail := by
  unfold originalFold
  rw [splitUnpack found]
  cases got : unpack tail <;>
    simp only [got,Option.map_none,Option.map_some,Option.bind_eq_bind,
      Option.bind_none,Option.bind_some,List.foldl_cons,optionRound,stateRound]

private theorem stable (entries : Entries) (s : Settings) (c ty start fuel : Nat) :
    repeatStates (stateNext entries s c ty) fuel (0,start) = (0,start) :=
  repeatStable (stateNext entries s c ty) (0,start) (by simp [stateNext]) fuel

theorem exactRepeat (entries : Entries) (s : Settings) (c ty cert fuel start : Nat)
    (bound : cert ≤ fuel) :
    repeatStates (stateNext entries s c ty) fuel (cert,start) =
      (0,encodeState (originalFold entries s c ty start cert)) := by
  induction cert using Nat.strongRecOn generalizing fuel start with
  | ind cert ih =>
    cases cert with
    | zero => rw [stable,foldNil,stateRound]
    | succ n =>
      cases fuel with
      | zero => exact False.elim (Nat.not_succ_le_zero n bound)
      | succ k =>
        rw [repeatHead]
        cases found : chosenCell (n+1) with
        | none =>
          have now : stateNext entries s c ty (n+1,start) = (0,0) := by simp [stateNext,found]
          rw [now,stable,foldMissing entries s c ty start (n+1) (Nat.succ_ne_zero n) found] <;> rfl
        | some both =>
          obtain ⟨hop,tail⟩ := both
          have pred : n = pair hop tail := Nat.succ.inj (codeOfCell found)
          have lower : tail ≤ n := by rw [pred]; exact tailBound hop tail
          have enough : tail ≤ k := Nat.le_trans lower (Nat.le_of_succ_le_succ bound)
          let next := encodeState (packedOriginalAdvance entries s c ty start hop)
          have now : stateNext entries s c ty (n+1,start) = (tail,next) := by
            simp [stateNext,found,next]
          rw [now,ih tail (Nat.lt_succ_of_le lower) k next enough,foldCons entries s c ty start (n+1) hop tail found]

theorem fuel (entries : Entries) (s : Settings) (raw : Program 5) (least : Program 3)
    (cal : ActualAdvanceCalibration entries s raw least) :
    ActualFuelCalibration entries s raw least := by
  intro c ty start cert fuel bound
  rw [iterationValue entries s raw least cal,exactRepeat entries s c ty cert fuel start bound]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldFuelProof
