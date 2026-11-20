module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericShapeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldStateEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericSlotsProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (conjunction)
open InternalEqualityTestEvaluationProof (vectorTwo exactEqualityEvaluation)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open NumberedWindowInternalSparsePathEnvelope (run applyUnary)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalAtomicRefinementNumericFieldsProof (sourceValue targetValue)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawContext rawResult rawLeast)
open NumberedWindowInternalSparsePositiveFold (positive)
open NumberedWindowInternalSparsePositiveFoldStateEvaluationProof (vectorFive)
open NumberedWindowInternalSparseAddressPositive

abbrev tape (x w y : Nat) : List.Vector Nat 3 := x ::ᵥ w ::ᵥ y ::ᵥ nil

theorem acceptedBoth {n : Nat} (p q : Program n) (xs : List.Vector Nat n) :
    evaluate (conjunction p q) xs = 1 ↔ evaluate p xs = 1 ∧ evaluate q xs = 1 := by
  rw [conjunctionEvaluation]
  split <;> simp_all

theorem sourceEval (p : Program 1) (x w y : Nat) : evaluate (atAddress p 0) (tape x w y) = run p x :=
  sourceValue p x w y

theorem targetEval (p : Program 1) (x w y : Nat) : evaluate (atAddress p 2) (tape x w y) = run p y :=
  targetValue p x w y

def sideReports (ctxValid tyValid : Program 1) (q : Nat) : Prop :=
  run addressGood q = 1 ∧
    (run ctxValid (run rawContext q) = 1 ∧ run tyValid (run rawResult q) = 1)

theorem sourceSide (cv tv : Program 1) (x w y : Nat) :
    evaluate (sideGood cv tv 0) (tape x w y) = 1 ↔ sideReports cv tv x := by
  simp only [sideGood,sideReports,acceptedBoth,sourceEval,applyValue]

theorem targetSide (cv tv : Program 1) (x w y : Nat) :
    evaluate (sideGood cv tv 2) (tape x w y) = 1 ↔ sideReports cv tv y := by
  simp only [sideGood,sideReports,acceptedBoth,targetEval,applyValue]

theorem sameTest (p : Program 1) (x w y : Nat) :
    evaluate (sameField p) (tape x w y) = 1 ↔ run p x = run p y := by
  unfold sameField
  change evaluate InternalEqualityTest.equalityTest
    (List.Vector.ofFn fun i : Fin 2 => evaluate ((![atAddress p 0,atAddress p 2] : Fin 2 → Program 3) i)
      (tape x w y)) = 1 ↔ _
  rw [vectorTwo]
  change evaluate InternalEqualityTest.equalityTest
    (evaluate (atAddress p 0) (tape x w y) ::ᵥ evaluate (atAddress p 2) (tape x w y) ::ᵥ nil) = 1 ↔ _
  rw [sourceEval,targetEval,exactEqualityEvaluation]
  split <;> simp_all

theorem foldCall (raw : Program 5) (least : Program 3) (x w y : Nat) :
    evaluate (callFold raw least) (tape x w y) =
      evaluate (positive raw least)
        (run rawContext x ::ᵥ run rawResult x ::ᵥ run rawLeast x ::ᵥ w ::ᵥ run rawLeast y ::ᵥ nil) := by
  let p : Fin 5 → Program 3 := ![atAddress rawContext 0,atAddress rawResult 0,
    atAddress rawLeast 0,.projection 1,atAddress rawLeast 2]
  change evaluate (positive raw least) (List.Vector.ofFn fun i : Fin 5 => evaluate (p i) (tape x w y)) = _
  rw [vectorFive]
  change evaluate (positive raw least) (evaluate (atAddress rawContext 0) (tape x w y) ::ᵥ
    evaluate (atAddress rawResult 0) (tape x w y) ::ᵥ evaluate (atAddress rawLeast 0) (tape x w y)
      ::ᵥ w ::ᵥ evaluate (atAddress rawLeast 2) (tape x w y) ::ᵥ nil) = _
  simp only [sourceEval,targetEval]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericSlotsProof
