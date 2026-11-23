module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open ID1Completion.InternalApplicationValidityStackAppend (append appendStep)
open ID1Completion.InternalRawListRecursionEvaluationProof (actualRawListRecursionEvaluation)
open ID1Completion.InternalListCodecEvaluationProof (consEvaluation)
open NumberedWindowInternalFreshProbeDispatchProgram (chooseBranch zeroAt predOne literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (compositeOne branchEvaluation zeroEvaluation literalEvaluation predEvaluation)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserNumericChecks (exact_ActualEncodedOutput)
open NumberedWindowInternalSparseFieldParserTargets (encodeResult)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open NumberedWindowInternalDirectSourcePartitionRawTargets

theorem conjunctionValue {n : Nat} (p q : Program n) (xs : List.Vector Nat n) :
    evaluate (conjunction p q) xs = (if evaluate p xs = 1 ∧ evaluate q xs = 1 then 1 else 0) :=
  actualConjunctionEvaluation n p q xs

theorem conjunctionBit {n : Nat} (p q : Program n) (xs : List.Vector Nat n) :
    evaluate (conjunction p q) xs =
      (decide (evaluate p xs = 1) && decide (evaluate q xs = 1)).toNat := by
  rw [conjunctionValue]
  by_cases hp : evaluate p xs = 1 <;> by_cases hq : evaluate q xs = 1 <;> simp [hp,hq]

theorem parserValue (i : Fin 3) (xs : List.Vector Nat 3) :
    evaluate (parserAt i) xs = encodeResult (unpack (xs.get i)) := by
  change evaluate (.composition parser (Fin.cons (.projection i) Fin.elim0)) xs = _
  rw [compositeOne]
  exact exact_ActualEncodedOutput (xs.get i)

theorem readyValue (i : Fin 3) (xs : List.Vector Nat 3) :
    evaluate (parsedAt i) xs = (unpack (xs.get i)).isSome.toNat := by
  change evaluate (chooseBranch (parserAt i) (zeroAt 3) (literal 3 1)) xs = _
  rw [branchEvaluation,parserValue,zeroEvaluation,literalEvaluation]
  cases unpack (xs.get i) <;> rfl

theorem payloadValue (i : Fin 3) (xs : List.Vector Nat 3) (ys : List Nat)
    (parsed : unpack (xs.get i) = some ys) :
    evaluate (payloadAt i) xs = numbersNumber ys := by
  change evaluate (.composition predOne (Fin.cons (parserAt i) Fin.elim0)) xs = _
  rw [compositeOne,parserValue,parsed]
  exact predEvaluation (numbersNumber ys + 1)

private theorem appendFold (xs ys : List Nat) :
    xs.foldr (fun head rest => 1 + Nat.pair head rest) (numbersNumber ys) = numbersNumber (xs ++ ys) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.foldr_cons,List.cons_append,numbersNumber,ih]

/-- Narrow numerical cut for the same original append: its historical wider
PrimaryExpansion home brings unrelated dependencies. -/
theorem appendValue (xs ys : List Nat) :
    evaluate append (numbersNumber xs ::ᵥ numbersNumber ys ::ᵥ nil) =
      numbersNumber (xs ++ ys) := by
  have h := actualRawListRecursionEvaluation 1 (.projection 0) appendStep (numbersNumber ys ::ᵥ nil)
    (numbersNumber xs)
  change evaluate append (numbersNumber xs ::ᵥ numbersNumber ys ::ᵥ nil) = _ at h
  rw [h,numbersRoundTrip]
  have hs (head rest : Nat) : evaluate appendStep
      (head ::ᵥ rest ::ᵥ numbersNumber ys ::ᵥ nil) = 1 + Nat.pair head rest :=
    consEvaluation head rest
  simp only [Option.getD_some,hs]
  exact appendFold xs ys

theorem decideToNatOne (b : Bool) : decide (b.toNat = 1) = b := by cases b <;> rfl

#print axioms appendValue
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericSupportProof
