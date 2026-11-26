module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureCombineTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureCombineNumericProof
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
open NumberedWindowInternalCoverAuxApplicationsTargets (reorder)
open NumberedWindowInternalCoverNumberedMeasureCombineTargets

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

private theorem reorderTail (P : Program 2) (id l r : Nat) :
    evaluate (reorder P (![1,2] : Fin 2 → Fin 3)) (id ::ᵥ l ::ᵥ r ::ᵥ nil) =
      evaluate P (l ::ᵥ r ::ᵥ nil) := by
  change evaluate P (List.Vector.ofFn (fun i => evaluate
    (.projection ((![1,2] : Fin 2 → Fin 3) i)) (id ::ᵥ l ::ᵥ r ::ᵥ nil))) = _
  rw [vectorTwo] <;> rfl

private theorem unpairCode (d w : Nat) :
    Nat.unpair (Encodable.encode ((d,w) : Nat × Nat)) = (d,w) := by
  simp only [Encodable.encode_prod_val,Encodable.encode_nat,Nat.unpair_pair]

theorem exact_CoverNumberedJoin : ExactCoverNumberedJoin := by
  intro id l r wl wr
  let pl := Encodable.encode ((l,wl) : Nat × Nat)
  let pr := Encodable.encode ((r,wr) : Nat × Nat)
  let xs := id ::ᵥ pl ::ᵥ pr ::ᵥ nil
  have d : evaluate numberedPredDepth xs = l+r := by
    change evaluate numberedPredDepth (id ::ᵥ pl ::ᵥ pr ::ᵥ nil) = l+r
    rw [numberedPredDepth,reorderTail,predecessorDepth,twoValue,coordinateValue,coordinateValue]
    change evaluate ID1Completion.InternalArithmeticPrograms.addition
      (evaluate ID1Completion.InternalUnpair.left (pl ::ᵥ nil) ::ᵥ
        evaluate ID1Completion.InternalUnpair.left (pr ::ᵥ nil) ::ᵥ nil) = _
    rw [(exactUnpairEvaluation pl).1,(exactUnpairEvaluation pr).1,unpairCode l wl,unpairCode r wr,exactAdditionEvaluation]
  have w : evaluate numberedChildMax xs = max wl wr := by
    change evaluate numberedChildMax (id ::ᵥ pl ::ᵥ pr ::ᵥ nil) = max wl wr
    rw [numberedChildMax,reorderTail,numeralBound,twoValue,coordinateValue,coordinateValue]
    change evaluate maximum
      (evaluate ID1Completion.InternalUnpair.right (pl ::ᵥ nil) ::ᵥ
        evaluate ID1Completion.InternalUnpair.right (pr ::ᵥ nil) ::ᵥ nil) = _
    rw [(exactUnpairEvaluation pl).2,(exactUnpairEvaluation pr).2,unpairCode l wl,unpairCode r wr,maximumValue]
  have chosen : evaluate numberedWidth xs = max id (max wl wr) := by
    rw [numberedWidth,twoValue,w]
    exact maximumValue id (max wl wr)
  change evaluate numberedJoin xs = Encodable.encode (l+r+1,max id (max wl wr))
  rw [numberedJoin,twoValue,oneValue,chosen]
  change evaluate ID1Completion.InternalPairing.pairing
    (Nat.succ (evaluate numberedPredDepth xs) ::ᵥ max id (max wl wr) ::ᵥ nil) = _
  rw [d,exactPairingEvaluation]
  simp only [Encodable.encode_prod_val,Encodable.encode_nat] <;> rfl

#print axioms exact_CoverNumberedJoin

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureCombineNumericProof
