module
public import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalParameterizedNumericIteration
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo)
open InternalPairingEvaluationProof (exactPairingEvaluation)
open InternalUnpairEvaluationProof (exactUnpairEvaluation)

/-- A carried step preserves the parameter and applies the same arbitrary
binary program to the value and that parameter. -/
theorem carryPairEvaluation (P : Program 2) (value parameter : Nat) :
    evaluate (carryP P) (Nat.pair parameter value ::ᵥ List.Vector.nil) =
      Nat.pair parameter (evaluate P (value ::ᵥ parameter ::ᵥ List.Vector.nil)) := by
  change evaluate InternalPairing.pairing (ofFn ![
    evaluate InternalUnpair.left (Nat.pair parameter value ::ᵥ List.Vector.nil),
    evaluate P (ofFn ![
      evaluate InternalUnpair.right (Nat.pair parameter value ::ᵥ List.Vector.nil),
      evaluate InternalUnpair.left (Nat.pair parameter value ::ᵥ List.Vector.nil)])]) = _
  simp only [vectorTwo, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [exactPairingEvaluation, (exactUnpairEvaluation _).1,
    (exactUnpairEvaluation _).2, Nat.unpair_pair]

/-- Induction on the original numeric primitive recursion, with no
restriction on the initial value, parameter, or binary program. -/
theorem repeatCarryPairEvaluation (P : Program 2) (count value parameter : Nat) :
    evaluate (InternalNumericIteration.repeatProgram (carryP P))
      (count ::ᵥ Nat.pair parameter value ::ᵥ List.Vector.nil) =
      Nat.pair parameter
        (Nat.iterate (fun x => evaluate P (x ::ᵥ parameter ::ᵥ List.Vector.nil))
          count value) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change evaluate (carryP P) (ofFn fun _ : Fin 1 =>
      evaluate (InternalNumericIteration.repeatProgram (carryP P))
        (count ::ᵥ Nat.pair parameter value ::ᵥ List.Vector.nil)) = _
    rw [vectorOne, ih, carryPairEvaluation]
    rw [Function.iterate_succ_apply']

/-- Standard evaluation on every natural input; this does not serve as an
internal-calculus reflection principle. -/
theorem exactParameterizedNumericIterationEvaluation :
    InternalParameterizedNumericIterationTargets.ExactParameterizedNumericIterationEvaluation := by
  intro P count value parameter
  change evaluate InternalUnpair.right (ofFn fun _ : Fin 1 =>
    evaluate (InternalNumericIteration.repeatProgram (carryP P))
      (ofFn ![count, evaluate InternalPairing.pairing (ofFn ![parameter, value])])) = _
  simp only [vectorOne, vectorTwo, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [exactPairingEvaluation, repeatCarryPairEvaluation,
    (exactUnpairEvaluation _).2, Nat.unpair_pair]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationEvaluationProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationEvaluationProof
