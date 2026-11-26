module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalWeightProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSemanticProof
open OriginalLambdaTraversal OriginalLambdaTraversalWeightProof

/-- Independent native semantics, by genuine well-founded recursion on the
ORIGINAL term payload. It mentions no machine, state, iteration or budget.
The lambda body is evaluated at the actual extended runtime parameter. -/
def semanticFold (leaf : Nat → Nat → Nat) (value parameter : Nat) : Nat :=
  if ha : tagValue value = 2 then
    applicationValue (domainValue value) (resultTypeValue value)
      (semanticFold leaf (functionChildValue value) parameter)
      (semanticFold leaf (argumentChildValue value) parameter)
  else if hl : tagValue value = 1 then
    lambdaValue (domainValue value) (lambdaCodomainValue value)
      (semanticFold leaf (lambdaBodyValue value) (childParameterValue value parameter))
  else leaf value parameter
termination_by payloadValue value
decreasing_by
  · have hb := OriginalHereditaryValidityWorkProof.applicationPayloadBound value ha
    change OriginalHereditaryValidity.functionPayloadValue value +
      OriginalHereditaryValidity.argumentPayloadValue value + 2 ≤ payloadValue value at hb
    rw [functionPayload]
    omega
  · have hb := OriginalHereditaryValidityWorkProof.applicationPayloadBound value ha
    change OriginalHereditaryValidity.functionPayloadValue value +
      OriginalHereditaryValidity.argumentPayloadValue value + 2 ≤ payloadValue value at hb
    rw [argumentPayload]
    omega
  · have hb := OriginalHereditaryValidityWorkProof.lambdaPayloadBound value hl
    change OriginalHereditaryValidity.lambdaBodyPayloadValue value + 1 ≤ payloadValue value at hb
    rw [bodyPayload]
    omega

theorem semanticEquation (leaf : Nat → Nat → Nat) (value parameter : Nat) :
    semanticFold leaf value parameter =
      if tagValue value = 2 then
        applicationValue (domainValue value) (resultTypeValue value)
          (semanticFold leaf (functionChildValue value) parameter)
          (semanticFold leaf (argumentChildValue value) parameter)
      else if tagValue value = 1 then
        lambdaValue (domainValue value) (lambdaCodomainValue value)
          (semanticFold leaf (lambdaBodyValue value) (childParameterValue value parameter))
      else leaf value parameter := by
  rw [semanticFold]
  split_ifs <;> rfl

def stateIterate (leaf : Nat → Nat → Nat) : Nat → State → State
  | 0, state => state
  | count + 1, state => stateStep leaf (stateIterate leaf count state)

def terminal (state : State) : Prop :=
  state = failedState ∨ (state.status = 1 ∧ state.work = [])

/-- Meaning of a finite work list. A visit computes its separate semantic
fold immediately; returns use original constructors. This structurally
recursive function never expands a visit into a new machine work list. -/
def workMeaning (fold : Nat → Nat → Nat) : List Nat → List Nat → Option (List Nat)
  | [], results => some results
  | frame :: rest, results =>
      let tag := (Nat.unpair frame).1
      let payload := (Nat.unpair frame).2
      if tag = 0 then
        workMeaning fold rest (fold (Nat.unpair payload).1 (Nat.unpair payload).2 :: results)
      else if tag = 1 then
        match results with
        | argument :: function :: remaining =>
          workMeaning fold rest
            (applicationValue (Nat.unpair payload).1 (Nat.unpair payload).2
              function argument :: remaining)
        | _ => none
      else if tag = 2 then
        match results with
        | body :: remaining =>
          workMeaning fold rest
            (lambdaValue (Nat.unpair payload).1 (Nat.unpair payload).2 body :: remaining)
        | _ => none
      else none

def stateMeaning (leaf : Nat → Nat → Nat) (state : State) : Option (List Nat) :=
  if state.status = 1 then workMeaning (semanticFold leaf) state.work state.results else none

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSemanticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSemanticProof
