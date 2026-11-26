module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportEvaluationSupportProof
open OriginalRawSyntaxTransport InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

 theorem unaryCompositionEvaluation {n : Nat} (p : Program 1) (q : Program n)
    (v : List.Vector Nat n) :
    evaluate (.composition p (fun _ : Fin 1 => q)) v =
      evaluate p (List.Vector.ofFn ![evaluate q v]) := by
  change evaluate p (List.Vector.ofFn fun _ : Fin 1 => evaluate q v) = _
  congr 1

 theorem binaryCompositionEvaluation {n : Nat} (p : Program 2) (q r : Program n)
    (v : List.Vector Nat n) :
    evaluate (.composition p ![q,r]) v =
      evaluate p (List.Vector.ofFn ![evaluate q v,evaluate r v]) := by
  change evaluate p (List.Vector.ofFn fun i : Fin 2 => evaluate (![q,r] i) v) = _
  congr 1

 theorem ternaryCompositionEvaluation {n : Nat} (p : Program 3) (q r s : Program n)
    (v : List.Vector Nat n) :
    evaluate (.composition p ![q,r,s]) v =
      evaluate p (List.Vector.ofFn ![evaluate q v,evaluate r v,evaluate s v]) := by
  change evaluate p (List.Vector.ofFn fun i : Fin 3 => evaluate (![q,r,s] i) v) = _
  congr 1

 theorem constantEvaluation (n k : Nat) (v : List.Vector Nat n) : evaluate (constant n k) v = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Nat.succ (evaluate (constant n k) v) = k + 1
    rw [ih]

 theorem succOfEvaluation {n : Nat} (p : Program n) (v : List.Vector Nat n) :
    evaluate (succOf p) v = evaluate p v + 1 := rfl

 theorem addOfEvaluation {n : Nat} (p q : Program n) (v : List.Vector Nat n) :
    evaluate (addOf p q) v = evaluate p v + evaluate q v := by
  rw [addOf, binaryCompositionEvaluation, InternalArithmeticProgramsEvaluationProof.vectorTwo]
  exact InternalArithmeticProgramsEvaluationProof.exactAdditionEvaluation _ _

 theorem sameOfEvaluation {n : Nat} (p q : Program n) (v : List.Vector Nat n) :
    evaluate (sameOf p q) v = if evaluate p v = evaluate q v then 1 else 0 :=
  sameEvaluation p q v

 theorem lessCompositionEvaluation {n : Nat} (p q : Program n) (v : List.Vector Nat n) :
    evaluate (.composition InternalLessThan.ltTest ![p,q]) v =
      if evaluate p v < evaluate q v then 1 else 0 := by
  rw [binaryCompositionEvaluation, InternalEqualityTestEvaluationProof.vectorTwo]
  exact InternalLessThanEvaluationProof.exactLessThanEvaluation _ _

 theorem predecessorCompositionEvaluation {n : Nat} (p : Program n) (v : List.Vector Nat n) :
    evaluate (.composition InternalEqualityTest.predecessor (fun _ : Fin 1 => p)) v =
      evaluate p v - 1 := by
  rw [unaryCompositionEvaluation, InternalEqualityTestEvaluationProof.vectorOne,
    InternalEqualityTestEvaluationProof.exactPredecessorEvaluation]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportEvaluationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportEvaluationSupportProof
