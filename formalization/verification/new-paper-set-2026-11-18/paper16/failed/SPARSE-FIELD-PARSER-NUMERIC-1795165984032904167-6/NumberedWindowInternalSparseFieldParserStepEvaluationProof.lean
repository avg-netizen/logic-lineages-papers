module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeNumericThinChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserStepEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion
open InternalEqualityTestEvaluationProof
  (vectorOne vectorTwo vectorThree exactPredecessorEvaluation exactSubtractionEvaluation)
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalListCodecEvaluationProof (consEvaluation)
open InternalRawListRecursion (lookup)
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowInternalSparseFieldCell (atPredecessor cellGood cellHead cellTail chosenCell)
open NumberedWindowInternalSparseDecode (good)
open NumberedWindowInternalSparseDecodeNumericThinChecks (exact_GuardValue)
open NumberedWindowInternalSparseFieldParser
open NumberedWindowInternalSparseFieldParserTargets (encodeResult)

abbrev params : List.Vector Nat 2 := 0 ::ᵥ 0 ::ᵥ nil

theorem parserRow (n : Nat) :
    evaluate parser (n ::ᵥ nil) = evaluate (scratchRow parserBase parserStep) (n ::ᵥ params) := by
  unfold parser
  rw [evaluate,vectorThree]
  rfl

theorem atRawValue (p : Program 1) (i tab : Nat) :
    evaluate (atRaw p) (i ::ᵥ tab ::ᵥ params) = evaluate p ((i+1) ::ᵥ nil) := by
  unfold atRaw
  rw [evaluate,vectorOne]
  rfl

private theorem predecessorValue (p : Program 1) (n : Nat) :
    evaluate (atPredecessor p) ((n+1) ::ᵥ nil) = evaluate p (n ::ᵥ nil) := by
  unfold atPredecessor
  rw [evaluate,vectorOne]
  change evaluate p (evaluate InternalEqualityTest.predecessor ((n+1) ::ᵥ nil) ::ᵥ nil) = _
  rw [exactPredecessorEvaluation] <;> rfl

private theorem flag (n : Nat) :
    evaluate cellGood ((n+1) ::ᵥ nil) = 0 ∨ evaluate cellGood ((n+1) ::ᵥ nil) = 1 := by
  unfold cellGood
  rw [evalBranch]
  change (if n+1 = 0 then 0 else evaluate (atPredecessor good) ((n+1) ::ᵥ nil)) = 0 ∨
    (if n+1 = 0 then 0 else evaluate (atPredecessor good) ((n+1) ::ᵥ nil)) = 1
  rw [if_neg (Nat.succ_ne_zero n), predecessorValue, exact_GuardValue n]
  split <;> simp

theorem flagMissing {n : Nat} (h : chosenCell (n+1) = none) :
    evaluate cellGood ((n+1) ::ᵥ nil) = 0 := by
  rcases flag n with hz | ho
  · exact hz
  · simp [chosenCell,ho] at h

theorem fieldsPresent {n h t : Nat} (found : chosenCell (n+1) = some (h,t)) :
    evaluate cellGood ((n+1) ::ᵥ nil) = 1 ∧
      evaluate cellHead ((n+1) ::ᵥ nil) = h ∧ evaluate cellTail ((n+1) ::ᵥ nil) = t := by
  rcases flag n with hz | ho
  · simp [chosenCell,hz] at found
  · have pairEq : (evaluate cellHead ((n+1) ::ᵥ nil), evaluate cellTail ((n+1) ::ᵥ nil)) =
        (h,t) := by simpa [chosenCell, ho] using found
    exact ⟨ho,congrArg Prod.fst pairEq,congrArg Prod.snd pairEq⟩

theorem prependValue (h : Nat) (xs : Option (List Nat)) :
    evaluate prependResult (h ::ᵥ encodeResult xs ::ᵥ nil) =
      encodeResult (xs.map (fun ys => h :: ys)) := by
  unfold prependResult
  rw [evalBranch]
  cases xs with
  | none => rfl
  | some xs =>
    change (if numbersNumber xs + 1 = 0 then 0 else
      evaluate prependPayload (h ::ᵥ (numbersNumber xs+1) ::ᵥ nil)) = _
    rw [if_neg (Nat.succ_ne_zero _)]
    unfold prependPayload
    rw [evaluate,vectorOne]
    change Nat.succ (evaluate InternalListCodec.consCode
      (List.Vector.ofFn (fun j : Fin 2 => evaluate
        ((![.projection 0,.composition InternalEqualityTest.predecessor
          (fun _ : Fin 1 => .projection (1 : Fin 2))] : Fin 2 → Program 2) j)
        (h ::ᵥ (numbersNumber xs+1) ::ᵥ nil)))) = _
    rw [vectorTwo,consEvaluation]
    change Nat.succ (1+Nat.pair h (evaluate InternalEqualityTest.predecessor
      (List.Vector.ofFn fun _ : Fin 1 => numbersNumber xs+1))) = _
    rw [vectorOne,exactPredecessorEvaluation]
    rfl

theorem stepMissing {i tab : Nat} (missing : chosenCell (i+1) = none) :
    evaluate parserStep (i ::ᵥ tab ::ᵥ params) = 0 := by
  unfold parserStep
  rw [evalBranch, atRawValue, flagMissing missing, if_pos rfl]
  rfl

theorem stepPresent {i tab h t : Nat} (found : chosenCell (i+1) = some (h,t)) :
    evaluate parserStep (i ::ᵥ tab ::ᵥ params) =
      evaluate prependResult (h ::ᵥ evaluate lookup ((i-t) ::ᵥ tab ::ᵥ nil) ::ᵥ nil) := by
  obtain ⟨flagOne,hh,ht⟩ := fieldsPresent found
  unfold parserStep
  rw [evalBranch,atRawValue,flagOne,if_neg (Nat.succ_ne_zero 0)]
  unfold onCell priorResult tailLag
  let args := i ::ᵥ tab ::ᵥ params
  change evaluate prependResult (List.Vector.ofFn fun j : Fin 2 =>
    evaluate ((![atRaw cellHead,.composition lookup ![
      .composition InternalEqualityTest.subtract ![atRaw cellTail,.projection 0],
      .projection 1]] : Fin 2 → Program 4) j) args) = _
  rw [vectorTwo]
  change evaluate prependResult (evaluate (atRaw cellHead) args ::ᵥ evaluate lookup
    (List.Vector.ofFn fun j : Fin 2 =>
      evaluate ((![.composition InternalEqualityTest.subtract ![atRaw cellTail,.projection 0],
        .projection 1] : Fin 2 → Program 4) j) args) ::ᵥ nil) = _
  rw [vectorTwo]
  change evaluate prependResult (evaluate (atRaw cellHead) args ::ᵥ evaluate lookup
    (evaluate InternalEqualityTest.subtract (List.Vector.ofFn fun j : Fin 2 =>
      evaluate ((![atRaw cellTail,.projection 0] : Fin 2 → Program 4) j) args) ::ᵥ tab ::ᵥ nil)
    ::ᵥ nil) = _
  dsimp only [args]
  rw [vectorTwo,atRawValue,atRawValue,hh,ht]
  change evaluate prependResult (h ::ᵥ evaluate lookup
    (evaluate InternalEqualityTest.subtract (t ::ᵥ i ::ᵥ nil) ::ᵥ tab ::ᵥ nil) ::ᵥ nil) = _
  rw [exactSubtractionEvaluation]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserStepEvaluationProof
