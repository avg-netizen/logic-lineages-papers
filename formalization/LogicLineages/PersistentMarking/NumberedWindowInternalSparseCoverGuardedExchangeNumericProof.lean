module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeTargets
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchNumericProjectionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open ID1Completion.InternalEqualityTestEvaluationProof (vectorOne vectorTwo exactEqualityEvaluation)
open ID1Completion.InternalEqualityTest (equalityTest)
open NumberedWindowCoverBoundsAlgorithm (cover bounds)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowExchangeAlgorithm (bits row)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalSparseCoverScratchNumericProjectionProof (coverOptionValue)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets

theorem preservesOption : ExactOriginalExchangeCoverOption := by
  intro hp heads types a b hit
  have same := (NumberedWindowRawExchangeVerticesChecks.exact_OriginalGuardedExchangeBounds hp a b).1 hit
  have syntaxOk : (syntaxBits a).1 = true ∧ (syntaxBits b).1 = true ∧ (row hp a b).1 = true := by
    simpa [bits,Bool.and_eq_true,and_assoc] using hit
  simp only [cover,syntaxOk.1,syntaxOk.2.1,if_true,same]

private theorem compareValue (C : Program 3) (s : Settings) (xs : List.Vector Nat 2) :
    evaluate (compareOptions C s) xs =
      if evaluate (coverOption C s) (xs.get 0 ::ᵥ nil) = evaluate (coverOption C s) (xs.get 1 ::ᵥ nil)
        then 1 else 0 := by
  have slot (i : Fin 2) : evaluate (optionAtSlot C s i) xs =
      evaluate (coverOption C s) (xs.get i ::ᵥ nil) := by
    change evaluate (coverOption C s) (List.Vector.ofFn (fun _ : Fin 1 => xs.get i)) = _
    rw [vectorOne]
  change evaluate equalityTest (List.Vector.ofFn (fun i : Fin 2 =>
    evaluate ((![optionAtSlot C s 0,optionAtSlot C s 1] : Fin 2 → Program 2) i) xs)) = _
  rw [vectorTwo]
  change evaluate equalityTest (evaluate (optionAtSlot C s 0) xs ::ᵥ evaluate (optionAtSlot C s 1) xs ::ᵥ nil) = _
  rw [exactEqualityEvaluation,slot,slot]

theorem calibration : ExactGuardedExchangeCalibration := by
  intro C s X hC hX a b
  let xs : List.Vector Nat 2 := List.Vector.ofFn (NumberedWindowInternalSparseScalarEdge.exchangeTape a b)
  change evaluate (guardedExchange C s X) xs = _
  rw [guardedExchange,actualConjunctionEvaluation]
  have l : evaluate X xs = ((bits s.equivalentHeads a b).1).toNat := hX a b
  rw [l]
  cases hit : (bits s.equivalentHeads a b).1 with
  | false => rfl
  | true =>
    have same := preservesOption s.equivalentHeads s.window.2 s.types a b hit
    have code : evaluate (compareOptions C s) xs = 1 := by
      rw [compareValue]
      change (if evaluate (coverOption C s) (a ::ᵥ nil) = evaluate (coverOption C s) (b ::ᵥ nil) then 1 else 0) = 1
      rw [coverOptionValue C hC s a,coverOptionValue C hC s b,same,if_pos rfl]
    rw [code] <;> rfl
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeNumericProof
