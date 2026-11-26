module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTickIterationMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTickNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof (vectorOne)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalLiteralTickIterationMotiveProof (tickLoop)

def numericIter (tick : Program 1) : Nat → Nat → Nat
  | 0, x => x
  | n+1, x => numericIter tick n (run tick x)

private theorem commute (tick : Program 1) (fuel x : Nat) :
    run tick (numericIter tick fuel x) = numericIter tick fuel (run tick x) := by
  induction fuel generalizing x with
  | zero => rfl
  | succ n ih => exact ih (run tick x)

private theorem numericStep (tick : Program 1) (k prev x : Nat) :
    evaluate (.composition tick (fun _ : Fin 1 => .projection 1 : Fin 1 → Program 3))
      (k ::ᵥ prev ::ᵥ x ::ᵥ nil) = run tick prev := by
  change evaluate tick (List.Vector.ofFn (fun _ : Fin 1 => prev)) = _
  rw [vectorOne]
  rfl

theorem evalTickLoop (tick : Program 1) (fuel x : Nat) :
    evaluate (tickLoop tick) (fuel ::ᵥ x ::ᵥ nil) = numericIter tick fuel x := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
    change evaluate (.composition tick (fun _ : Fin 1 => .projection 1))
      (n ::ᵥ evaluate (tickLoop tick) (n ::ᵥ x ::ᵥ nil) ::ᵥ x ::ᵥ nil) = _
    rw [numericStep,ih,commute]
    rfl

#print axioms evalTickLoop
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTickNumericProof
