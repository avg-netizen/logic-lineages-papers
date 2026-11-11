module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityEvaluationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectorProof
open OriginalLambdaTraversal InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof
open OriginalHereditaryValidityEvaluationSupportProof
  (unaryCompositionEvaluation binaryCompositionEvaluation)
open InternalApplicationResultStackEvaluationProof (tailOfEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem rawTypeEvaluation (v : List.Vector Nat 1) :
    evaluate rawType v = resultTypeValue (v.get 0) := leftEvaluation v

theorem rawTagEvaluation (v : List.Vector Nat 1) :
    evaluate rawTag v = tagValue (v.get 0) :=
  OriginalLambdaConstructorEvaluationProof.tagEvaluation v

theorem rawDomainEvaluation (v : List.Vector Nat 1) :
    evaluate rawDomain v = domainValue (v.get 0) :=
  OriginalLambdaConstructorEvaluationProof.domainEvaluation v

theorem rawFunctionEvaluation (v : List.Vector Nat 1) :
    evaluate rawFunction v = functionChildValue (v.get 0) := by
  rw [rawFunction, pairOfEvaluation, consOfEvaluation, rawDomainEvaluation,
    rawTypeEvaluation, functionPayloadEvaluation, appBodyEvaluation]
  rfl

theorem rawArgumentEvaluation (v : List.Vector Nat 1) :
    evaluate rawArgument v = argumentChildValue (v.get 0) := by
  rw [rawArgument, pairOfEvaluation, rawDomainEvaluation,
    argumentPayloadEvaluation, appBodyEvaluation]
  rfl

theorem rawCodomainEvaluation (v : List.Vector Nat 1) :
    evaluate rawCodomain v = lambdaCodomainValue (v.get 0) := by
  rw [rawCodomain, tailOfEvaluation, rawTypeEvaluation]
  rfl

theorem rawBodyEvaluation (v : List.Vector Nat 1) :
    evaluate rawBody v = lambdaBodyValue (v.get 0) := by
  rw [rawBody, binaryCompositionEvaluation, OriginalLambdaConstructorEvaluationProof.bodyEvaluation]
  change Nat.pair (evaluate rawCodomain v)
    (Nat.unpair (Nat.unpair (Nat.unpair (v.get 0)).2).2).2 = _
  rw [rawCodomainEvaluation]
  rfl

theorem childParameterEvaluation (v : List.Vector Nat 2) :
    evaluate childParameter v = childParameterValue (v.get 0) (v.get 1) := by
  rw [childParameter, pairOfEvaluation, leftOfEvaluation, consOfEvaluation,
    unaryCompositionEvaluation, rawDomainEvaluation, rightOfEvaluation]
  rfl

theorem applicationEvaluation (v : List.Vector Nat 4) :
    evaluate application v = applicationValue (v.get 0) (v.get 1) (v.get 2) (v.get 3) :=
  InternalApplicationCertificateConstructorsEvaluationProof.applicationEvaluation v

theorem lambdaEvaluation (v : List.Vector Nat 3) :
    evaluate OriginalLambdaConstructor.constructor v =
      lambdaValue (v.get 0) (v.get 1) (v.get 2) :=
  OriginalLambdaConstructorEvaluationProof.constructorEvaluation v

theorem actualOriginalLambdaTraversalSelectorCalibration :
    OriginalLambdaTraversalTargets.ActualOriginalLambdaTraversalSelectorCalibration := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro value
    exact ⟨rawTypeEvaluation _, rawTagEvaluation _, rawDomainEvaluation _,
      rawFunctionEvaluation _, rawArgumentEvaluation _, rawCodomainEvaluation _, rawBodyEvaluation _⟩
  · intro value parameter
    exact childParameterEvaluation (List.Vector.ofFn ![value,parameter])
  · intro d e f a
    exact applicationEvaluation (List.Vector.ofFn ![d,e,f,a])
  · intro d e b
    exact lambdaEvaluation (List.Vector.ofFn ![d,e,b])

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectorProof
