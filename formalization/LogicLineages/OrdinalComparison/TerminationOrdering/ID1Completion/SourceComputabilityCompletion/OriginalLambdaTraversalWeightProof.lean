module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityWorkProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackStateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalWeightProof
open OriginalLambdaTraversal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem workWeightCons (frame : Nat) (rest : List Nat) :
    workWeight (frame :: rest) = frameWeight frame + workWeight rest := by
  simp only [workWeight, List.map_cons, List.sum_cons]

theorem visitWeight (value parameter : Nat) :
    frameWeight (visitValue value parameter) = fuelValue value := by
  simp [frameWeight, visitValue, fuelValue]

theorem applicationReturnWeight (d e : Nat) : frameWeight (applicationReturnValue d e) = 1 := by
  simp [frameWeight, applicationReturnValue]

theorem lambdaReturnWeight (d e : Nat) : frameWeight (lambdaReturnValue d e) = 1 := by
  simp [frameWeight, lambdaReturnValue]

theorem functionPayload (value : Nat) :
    payloadValue (functionChildValue value) = OriginalHereditaryValidity.functionPayloadValue value :=
  InternalApplicationValidityStackStateProof.functionChildPayload value

theorem argumentPayload (value : Nat) :
    payloadValue (argumentChildValue value) = OriginalHereditaryValidity.argumentPayloadValue value :=
  InternalApplicationValidityStackStateProof.argumentChildPayload value

theorem bodyPayload (value : Nat) :
    payloadValue (lambdaBodyValue value) = OriginalHereditaryValidity.lambdaBodyPayloadValue value := by
  simp only [lambdaBodyValue, OriginalHereditaryValidity.lambdaBodyValue,
    payloadValue, OriginalHereditaryValidity.payloadValue,
    InternalApplicationValidityStack.payloadValue, Nat.unpair_pair]

theorem applicationFuelBound (value : Nat) (h : tagValue value = 2) :
    1 + fuelValue (functionChildValue value) + fuelValue (argumentChildValue value) + 1 ≤
      fuelValue value := by
  have hb := OriginalHereditaryValidityWorkProof.applicationPayloadBound value h
  change OriginalHereditaryValidity.functionPayloadValue value +
    OriginalHereditaryValidity.argumentPayloadValue value + 2 ≤ payloadValue value at hb
  simp only [fuelValue, functionPayload, argumentPayload]
  omega

theorem lambdaFuelBound (value : Nat) (h : tagValue value = 1) :
    1 + fuelValue (lambdaBodyValue value) + 1 ≤ fuelValue value := by
  have hb := OriginalHereditaryValidityWorkProof.lambdaPayloadBound value h
  change OriginalHereditaryValidity.lambdaBodyPayloadValue value + 1 ≤ payloadValue value at hb
  simp only [fuelValue, bodyPayload]
  omega

theorem fuelEvaluation (value parameter : Nat) :
    evaluate fuel (List.Vector.ofFn ![value,parameter]) = fuelValue value := by
  change evaluate InternalApplicationResultStack.fuel
    (List.Vector.ofFn fun _ : Fin 1 => value) = _
  rw [InternalEqualityTestEvaluationProof.vectorOne]
  change evaluate InternalApplicationResultStack.fuel (List.Vector.ofFn ![value]) = _
  exact InternalApplicationResultStackStateProof.fuelEvaluation value

theorem actualOriginalLambdaTraversalFuelBounds :
    OriginalLambdaTraversalTargets.ActualOriginalLambdaTraversalFuelBounds := by
  refine ⟨?_, applicationFuelBound, lambdaFuelBound⟩
  intro value parameter
  exact ⟨fuelEvaluation value parameter,
    by simp [workWeightCons, visitWeight, workWeight]⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalWeightProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalWeightProof
