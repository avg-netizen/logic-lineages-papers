module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportWeightProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

 theorem unpairSum (raw : Nat) : (Nat.unpair raw).1 + (Nat.unpair raw).2 ≤ raw := by
  simpa only [Nat.pair_unpair] using Nat.add_le_pair (Nat.unpair raw).1 (Nat.unpair raw).2

 theorem unaryTags (raw : Nat) (h : arityValue raw = 1) : tagValue raw = 1 ∨ tagValue raw = 4 := by
  unfold arityValue at h
  split_ifs at h <;> simp_all

 theorem binaryTags (raw : Nat) (h : arityValue raw = 2) :
    tagValue raw = 2 ∨ tagValue raw = 5 ∨ tagValue raw = 7 := by
  unfold arityValue at h
  split_ifs at h <;> simp_all

 theorem unaryChildBound (raw : Nat) (h : arityValue raw = 1) : firstValue raw + 1 ≤ raw := by
  have ht := unaryTags raw h
  have hr := unpairSum raw
  have hp := unpairSum (payloadValue raw)
  have hh : 1 ≤ tagValue raw := by rcases ht with h | h <;> omega
  simp only [firstValue, if_pos ht]
  change tagValue raw + payloadValue raw ≤ raw at hr
  omega

 theorem binaryChildrenBound (raw : Nat) (h : arityValue raw = 2) :
    firstValue raw + secondValue raw + 2 ≤ raw := by
  have ht := binaryTags raw h
  have hn : ¬ (tagValue raw = 1 ∨ tagValue raw = 4) := by rcases ht with h | h | h <;> omega
  have hh : 2 ≤ tagValue raw := by rcases ht with h | h | h <;> omega
  have hr := unpairSum raw
  change tagValue raw + payloadValue raw ≤ raw at hr
  have h0 := unpairSum (payloadValue raw)
  have h1 := unpairSum (Nat.unpair (payloadValue raw)).2
  have h2 := unpairSum (Nat.unpair (Nat.unpair (payloadValue raw)).2).2
  have h3 := unpairSum (Nat.unpair (Nat.unpair (Nat.unpair (payloadValue raw)).2).2).2
  have h4 := unpairSum (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (payloadValue raw)).2).2).2).2
  by_cases h5 : tagValue raw = 5
  · simp only [firstValue, secondValue, if_neg hn, if_pos h5]
    omega
  · simp only [firstValue, secondValue, if_neg hn, if_neg h5]
    omega

 theorem workWeightCons (frame : Nat) (rest : List Nat) :
    workWeight (frame :: rest) = frameWeight frame + workWeight rest := by
  simp only [workWeight, List.map_cons, List.sum_cons]

 theorem visitWeight (d k raw : Nat) : frameWeight (visitValue d k raw) = fuelValue raw := by
  simp [frameWeight, visitValue, fuelValue]

 theorem finishWeight (raw : Nat) : frameWeight (finishValue raw) = 1 := by
  simp [frameWeight, finishValue]

 theorem unaryFuelBound (raw : Nat) (h : arityValue raw = 1) :
    1 + fuelValue (firstValue raw) + 1 ≤ fuelValue raw := by
  have hb := unaryChildBound raw h
  simp only [fuelValue]
  omega

 theorem binaryFuelBound (raw : Nat) (h : arityValue raw = 2) :
    1 + fuelValue (firstValue raw) + fuelValue (secondValue raw) + 1 ≤ fuelValue raw := by
  have hb := binaryChildrenBound raw h
  simp only [fuelValue]
  omega

 theorem fuelEvaluation (v : List.Vector Nat 3) : evaluate fuel v = fuelValue (v.get 2) := by
  simp only [fuel, succOfEvaluation, addOfEvaluation, projectionEvaluation, fuelValue]
  omega

 theorem actualRawSyntaxFuelBounds : OriginalRawSyntaxTransportTargets.ActualRawSyntaxFuelBounds := by
  refine ⟨?_, unaryFuelBound, binaryFuelBound⟩
  intro d k raw
  exact ⟨fuelEvaluation _, by simp [workWeightCons, visitWeight, workWeight]⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportWeightProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportWeightProof
