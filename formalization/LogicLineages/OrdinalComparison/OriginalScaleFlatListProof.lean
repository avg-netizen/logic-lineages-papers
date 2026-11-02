module
public import LogicLineages.OrdinalComparison.OriginalScaleFlatListReplicationProof
public import LogicLineages.OrdinalComparison.OriginalScaleFlatListAlgebraProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalScaleFlatList.Proof
open HeterogeneousUnaryAssembly ScalarCarrierAccounting OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem actualOriginalScaleChain : Targets.ActualOriginalScaleChain := by
  intro k Γ xs C b c hb hc
  obtain ⟨uC,hC,hgC⟩ := AdmissibleAssignment.actualAdmissibleAssignmentGenerated Γ
    (Ty.curriedGround (k+1)) OrdinalSyntax.defaultPolicy C
  obtain ⟨vC,hSat,hvalue⟩ := UnaryCarrier.Proof.saturate_assignment k C uC hC
  let caller := unaryInput Γ (UnaryCarrier.saturate k C) vC hSat
  let inputs := paidList b xs caller
  obtain ⟨K,hK,hhead⟩ := HeterogeneousUnaryAssembly.Proof.actualMergedChain Γ inputs
  have htrace := (literalReplication Γ b xs caller).2
  have hs : ∀ a ∈ xs.map (fun op => unitValue (op.vector 1)), a < epsilonZero := by
    intro a ha
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp ha
    exact record_head_below op
  have hcaller : unitValue (caller.vector 1) < epsilonZero := record_head_below caller
  have hc' : 3*(xs.map (fun op => unitValue (op.vector 1))).length+4 ≤ c := by simpa using hc
  have hbal := flat_balance (xs.map (fun op => unitValue (op.vector 1))) (unitValue (caller.vector 1))
    (scale b) c hs hcaller (scale_two b hb) hc'
  have hcval : unitValue (caller.vector 1) = unitValue (uC (UnaryCarrier.headIndex k)) := hvalue (fun _ => 1)
  have hg : GeneratedOrdinalGrade Γ 1 (uC (UnaryCarrier.headIndex k)) := hgC (UnaryCarrier.headIndex k)
  have hbalance : ordinalNaturalProduct (scale b : Ordinal)
      (ordinalNaturalSum (sourceSum xs + (c : Ordinal)) (unitValue (caller.vector 1))) =
      chargedSum ((List.replicate (scale b) (xs.map (fun op => unitValue (op.vector 1)))).flatten ++
        List.replicate (scale b) (unitValue (caller.vector 1))) + (gap b xs c : Ordinal) := by
    simpa only [sourceSum,gap,List.length_map] using hbal
  refine ⟨uC,vC,hC,hSat,hvalue,K,hK,(exactPositiveGap Γ b xs c hb hc).1,?_⟩
  intro ρ μ
  have hCvalue := UnaryCarrier.Proof.positive_unit_value 1 (uC (UnaryCarrier.headIndex k)) (by decide) hg ρ
  change expressionValue (UnitObservation.substitution ρ) (uC (UnaryCarrier.headIndex k)) =
    unitValue (uC (UnaryCarrier.headIndex k)) at hCvalue
  rw [hCvalue,← hcval]
  calc
    ordinalNaturalProduct (scale b : Ordinal)
        (ordinalNaturalSum (sourceSum xs + (c : Ordinal)) (unitValue (caller.vector 1))) =
        chargedSum ((List.replicate (scale b) (xs.map (fun op => unitValue (op.vector 1)))).flatten ++
          List.replicate (scale b) (unitValue (caller.vector 1))) + (gap b xs c : Ordinal) := hbalance
    _ = chargedSum (inputs.map (fun op => unitValue (op.vector 1))) + (gap b xs c : Ordinal) := by rw [htrace]
    _ = expressionValue (UnitObservation.substitution μ) (K 1) + (gap b xs c : Ordinal) := by rw [hhead μ]
end LogicLineages.OrdinalComparison.Source.OriginalScaleFlatList.Proof
