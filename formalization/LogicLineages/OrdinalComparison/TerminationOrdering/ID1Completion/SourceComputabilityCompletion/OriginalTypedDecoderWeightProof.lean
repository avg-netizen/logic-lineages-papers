module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportWeightProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderWeightProof
open OriginalTypedDecoder
open OriginalRawSyntaxTransportWeightProof (unpairSum)

 theorem workWeightNil : workWeight [] = 0 := rfl
 theorem workWeightCons (request : Nat) (rest : List Nat) :
    workWeight (request :: rest) = requestWeight request + workWeight rest := by
  simp only [workWeight, List.map_cons, List.sum_cons]

 theorem workWeightAppend (first rest : List Nat) :
    workWeight (first ++ rest) = workWeight first + workWeight rest := by
  simp [workWeight]

 theorem termRequestWeight (gamma typ raw : Nat) :
    requestWeight (termRequestValue gamma typ raw) = raw + 1 := by
  simp [requestWeight, requestRaw, termRequestValue]

 theorem argumentsRequestWeight (gamma types raw : Nat) :
    requestWeight (argumentsRequestValue gamma types raw) = raw + 1 := by
  simp [requestWeight, requestRaw, argumentsRequestValue]

/-- Pair bounds are applied to the unchanged raw payload and every numbered
metadata spine. They neither decode metadata nor assume a valid source Code. -/
 theorem expansionDecrease (H : Nat → Nat) (request : Nat) (children : List Nat)
    (he : expandValue H request = some children) :
    workWeight children < requestWeight request := by
  have h0 := unpairSum (requestRaw request)
  have h1 := unpairSum (Nat.unpair (requestRaw request)).2
  have h2 := unpairSum (Nat.unpair (Nat.unpair (requestRaw request)).2).2
  have h3 := unpairSum (Nat.unpair (Nat.unpair (Nat.unpair (requestRaw request)).2).2).2
  have h4 := unpairSum (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (requestRaw request)).2).2).2).2
  have h5 := unpairSum (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (requestRaw request)).2).2).2).2).2
  simp only [expandValue] at he
  split_ifs at he <;> cases he <;> simp_all [workWeight, requestWeight, requestRaw, termRequestValue,
    argumentsRequestValue] <;> omega

 theorem workDecrease (H : Nat → Nat) (state : State)
    (hs : state.status = 1) (hw : state.work ≠ []) :
    workWeight (stateStep H state).work < workWeight state.work := by
  rcases state with ⟨s,work⟩
  simp only at hs hw
  subst s
  cases work with
  | nil => exact False.elim (hw rfl)
  | cons request rest =>
    cases he : expandValue H request with
    | none =>
      simp [stateStep, he, failedState, workWeightCons, workWeightNil, requestWeight]
    | some children =>
      have hb := expansionDecrease H request children he
      simp only [stateStep, if_true, he, workWeightAppend, workWeightCons]
      omega

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderWeightProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderWeightProof
