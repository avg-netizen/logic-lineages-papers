module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchNumericCodecProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open ID1Completion.InternalAcceptanceCalibrationProof (evalBranch)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestEvaluationProof (exactPredecessorEvaluation)
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowInternalSparseCoverScratch
open NumberedWindowInternalSparseCoverScratchTargets

private theorem listCode (xs : List Nat) : Encodable.encode xs = numbersNumber xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [Encodable.encode_list_cons, Encodable.encode_nat, ih, numbersNumber, Nat.add_comm 1] <;> rfl

theorem payload : ExactCoverOptionPayload := by
  intro p
  cases p with
  | none =>
    rw [optionPayload, evalBranch, Encodable.encode_none] <;> rfl
  | some xs =>
    rw [optionPayload, evalBranch, Encodable.encode_some]
    change (if Nat.succ (Encodable.encode xs) = 0 then 0 else
      evaluate predecessor (Nat.succ (Encodable.encode xs) ::ᵥ nil)) = numbersNumber xs
    rw [if_neg (Nat.succ_ne_zero _), exactPredecessorEvaluation]
    exact listCode xs

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchNumericCodecProof
