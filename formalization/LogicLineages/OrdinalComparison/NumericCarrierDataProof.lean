module
public import LogicLineages.OrdinalComparison.NumericCarrierDataSemanticProof
public import LogicLineages.OrdinalComparison.NumericCarrierDataPrimitiveProof
public import LogicLineages.OrdinalComparison.DeterministicCarrierDataProof
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.NumericCarrierData.Proof

theorem actualCarrierRecord : Targets.ActualCarrierRecord := by
  intro k Γ op hop
  dsimp only
  rw [exactCarrierCode]
  have hc := SourceAnnotationCode.Proof.exactOperatorCodec _ (DeterministicCarrierData.carrierData op)
  rw [hc.2.1,hc.2.2.1]
  have ha := DeterministicCarrierData.Proof.exactCarrierData k Γ op hop
  refine ⟨?_,ha.2⟩
  rw [DefaultSourceAssignment.Proof.assignmentCorrect,ha.1]
  rfl
end LogicLineages.OrdinalComparison.Source.NumericCarrierData.Proof
