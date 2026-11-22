module

public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineNumericTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptanceCalibrationProof (evalBranch)
open ID1Completion.InternalArithmeticProgramsEvaluationProof (exactAdditionEvaluation)
open ID1Completion.InternalLessThanEvaluationProof (exactLessThanEvaluation)
open ID1Completion.InternalPairingEvaluationProof (exactPairingEvaluation)
open ID1Completion.InternalUnpairEvaluationProof (exactUnpairEvaluation)
open ID1Completion.InternalEqualityTestEvaluationProof (vectorOne vectorTwo)
open NumberedWindowInternalAuxMeasureMemoTargets (combine readMeasure auxiliaryMeasure)
open NumberedWindowInternalChosenAuxMeasureCombine
open NumberedWindowInternalChosenAuxMeasureCombineNumericTargets

private theorem oneValue {n : Nat} (p : Program 1) (q : Program n) (xs : List.Vector Nat n) :
    evaluate (callOne p q) xs = evaluate p (evaluate q xs ::ᵥ nil) := by
  change evaluate p (List.Vector.ofFn (fun _ : Fin 1 => evaluate q xs)) = _
  rw [vectorOne]

private theorem twoValue {n : Nat} (p : Program 2) (q r : Program n) (xs : List.Vector Nat n) :
    evaluate (callTwo p q r) xs = evaluate p (evaluate q xs ::ᵥ evaluate r xs ::ᵥ nil) := by
  change evaluate p (List.Vector.ofFn (fun i => evaluate ((![q,r] : Fin 2 → Program n) i) xs)) = _
  rw [vectorTwo] <;> rfl

private theorem coordinateValue (p : Program 1) (i : Fin 2) (xs : List.Vector Nat 2) :
    evaluate (coordinate p i) xs = evaluate p (xs.get i ::ᵥ nil) := by
  rw [coordinate,oneValue] <;> rfl

private theorem maximumValue (a b : Nat) : evaluate maximum (a ::ᵥ b ::ᵥ nil) = max a b := by
  rw [maximum,evalBranch,exactLessThanEvaluation]
  change (if (if a < b then 1 else 0) = 0 then a else b) = max a b
  by_cases h : a < b
  · simp only [h,ite_true,Nat.one_ne_zero,ite_false,max_eq_right (Nat.le_of_lt h)]
  · simp only [h,ite_false,ite_true,max_eq_left (Nat.le_of_not_gt h)]

private theorem totalMeasure (n : Nat) : readMeasure n = n.unpair := by
  unfold readMeasure
  simp only [Encodable.decode_prod_val,Encodable.decode_nat] <;> cases n.unpair <;> rfl

theorem exact_ChosenAuxMeasureCombine : ExactChosenAuxMeasureCombine := by
  intro mf ma
  let xs := mf ::ᵥ ma ::ᵥ nil
  have first : evaluate predecessorDepth xs = (Nat.unpair mf).1 + (Nat.unpair ma).1 := by
    rw [predecessorDepth,twoValue,coordinateValue,coordinateValue]
    change evaluate ID1Completion.InternalArithmeticPrograms.addition
      (evaluate ID1Completion.InternalUnpair.left (mf ::ᵥ nil) ::ᵥ
        evaluate ID1Completion.InternalUnpair.left (ma ::ᵥ nil) ::ᵥ nil) = _
    rw [(exactUnpairEvaluation mf).1,(exactUnpairEvaluation ma).1,exactAdditionEvaluation]
  have last : evaluate numeralBound xs = max (Nat.unpair mf).2 (Nat.unpair ma).2 := by
    rw [numeralBound,twoValue,coordinateValue,coordinateValue]
    change evaluate maximum
      (evaluate ID1Completion.InternalUnpair.right (mf ::ᵥ nil) ::ᵥ
        evaluate ID1Completion.InternalUnpair.right (ma ::ᵥ nil) ::ᵥ nil) = _
    rw [(exactUnpairEvaluation mf).2,(exactUnpairEvaluation ma).2,maximumValue]
  change evaluate chosenCombine xs = combine mf ma
  rw [chosenCombine,twoValue,oneValue,last]
  change evaluate ID1Completion.InternalPairing.pairing
    (Nat.succ (evaluate predecessorDepth xs) ::ᵥ max (Nat.unpair mf).2 (Nat.unpair ma).2 ::ᵥ nil) = _
  rw [first,exactPairingEvaluation]
  simp only [combine,totalMeasure,auxiliaryMeasure,Encodable.encode_prod_val,Encodable.encode_nat] <;> rfl

#print axioms exact_ChosenAuxMeasureCombine

end LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineNumericProof
