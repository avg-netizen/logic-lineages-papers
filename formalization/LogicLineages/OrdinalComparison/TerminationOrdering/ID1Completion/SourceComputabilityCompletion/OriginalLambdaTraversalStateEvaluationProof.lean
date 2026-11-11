module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalStateEvaluationProof
open OriginalLambdaTraversal InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalLambdaTraversalSelectorProof
open OriginalHereditaryValidityEvaluationSupportProof
  (unaryCompositionEvaluation binaryCompositionEvaluation)
open InternalApplicationValidityStackEvaluationProof (oneEvaluation zeroEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem compositionThreeEvaluation {n : Nat} (p : Program 3) (q r s : Program n)
    (v : List.Vector Nat n) :
    evaluate (.composition p ![q,r,s]) v =
      evaluate p (List.Vector.ofFn ![evaluate q v,evaluate r v,evaluate s v]) := by
  change evaluate p (List.Vector.ofFn fun i : Fin 3 => evaluate (![q,r,s] i) v) = _
  congr 1

theorem compositionFourEvaluation {n : Nat} (p : Program 4) (q r s t : Program n)
    (v : List.Vector Nat n) :
    evaluate (.composition p ![q,r,s,t]) v =
      evaluate p (List.Vector.ofFn ![evaluate q v,evaluate r v,evaluate s v,evaluate t v]) := by
  change evaluate p (List.Vector.ofFn fun i : Fin 4 => evaluate (![q,r,s,t] i) v) = _
  congr 1

theorem framePayloadEvaluation (v : List.Vector Nat 1) :
    evaluate framePayload v = (Nat.unpair (evaluate currentFrame v)).2 := by
  rw [framePayload, rightOfEvaluation]

theorem currentRawEvaluation (v : List.Vector Nat 1) :
    evaluate currentRaw v = (Nat.unpair (evaluate framePayload v)).1 := by
  rw [currentRaw, leftOfEvaluation]

theorem currentParameterEvaluation (v : List.Vector Nat 1) :
    evaluate currentParameter v = (Nat.unpair (evaluate framePayload v)).2 := by
  rw [currentParameter, rightOfEvaluation]

theorem currentTagEvaluation (v : List.Vector Nat 1) :
    evaluate currentTag v = tagValue (evaluate currentRaw v) := by
  rw [currentTag, unaryCompositionEvaluation, rawTagEvaluation]
  rfl

theorem currentDomainEvaluation (v : List.Vector Nat 1) :
    evaluate currentDomain v = domainValue (evaluate currentRaw v) := by
  rw [currentDomain, unaryCompositionEvaluation, rawDomainEvaluation]
  rfl

theorem currentTypeEvaluation (v : List.Vector Nat 1) :
    evaluate currentType v = resultTypeValue (evaluate currentRaw v) := by
  rw [currentType, unaryCompositionEvaluation, rawTypeEvaluation]
  rfl

theorem currentFunctionEvaluation (v : List.Vector Nat 1) :
    evaluate currentFunction v = functionChildValue (evaluate currentRaw v) := by
  rw [currentFunction, unaryCompositionEvaluation, rawFunctionEvaluation]
  rfl

theorem currentArgumentEvaluation (v : List.Vector Nat 1) :
    evaluate currentArgument v = argumentChildValue (evaluate currentRaw v) := by
  rw [currentArgument, unaryCompositionEvaluation, rawArgumentEvaluation]
  rfl

theorem currentCodomainEvaluation (v : List.Vector Nat 1) :
    evaluate currentCodomain v = lambdaCodomainValue (evaluate currentRaw v) := by
  rw [currentCodomain, unaryCompositionEvaluation, rawCodomainEvaluation]
  rfl

theorem currentBodyEvaluation (v : List.Vector Nat 1) :
    evaluate currentBody v = lambdaBodyValue (evaluate currentRaw v) := by
  rw [currentBody, unaryCompositionEvaluation, rawBodyEvaluation]
  rfl

theorem currentChildParameterEvaluation (v : List.Vector Nat 1) :
    evaluate currentChildParameter v =
      childParameterValue (evaluate currentRaw v) (evaluate currentParameter v) := by
  rw [currentChildParameter, binaryCompositionEvaluation, childParameterEvaluation]
  rfl

theorem visitOfEvaluation {n : Nat} (raw parameter : Program n) (v : List.Vector Nat n) :
    evaluate (visitOf raw parameter) v = visitValue (evaluate raw v) (evaluate parameter v) := by
  rw [visitOf, pairOfEvaluation, zeroEvaluation, pairOfEvaluation]
  rfl

theorem applicationReturnOfEvaluation {n : Nat} (d e : Program n) (v : List.Vector Nat n) :
    evaluate (applicationReturnOf d e) v = applicationReturnValue (evaluate d v) (evaluate e v) := by
  rw [applicationReturnOf, pairOfEvaluation, oneEvaluation, pairOfEvaluation]
  rfl

theorem lambdaReturnOfEvaluation {n : Nat} (d e : Program n) (v : List.Vector Nat n) :
    evaluate (lambdaReturnOf d e) v = lambdaReturnValue (evaluate d v) (evaluate e v) := by
  rw [lambdaReturnOf, pairOfEvaluation, twoEvaluation, pairOfEvaluation]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalStateEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalStateEvaluationProof
