module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAccountTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundBudgetBoxProof
public import LogicLineages.ControlSensitivityCurrent.CurrentSelectedCarriersStatementChecks
public import LogicLineages.OrdinalComparison.NumericCarrierDataSemanticProof
public import LogicLineages.OrdinalComparison.GroundCaptureClosingCodeSemanticProof
public import LogicLineages.OrdinalComparison.UnitHeadCodeProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundAccount

open LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.StandardControlCurrent
open ScalarAnnotationData AdmissibleSum
open DeterministicAccountData (UnaryRecord)
open CurrentReserve (unitValue zeroUnits)

theorem currentHeadClassification : CurrentGroundAccountTargets.CurrentHeadClassification := by
  intro f Γ i q hg hi
  obtain ⟨a,fin,n,_,hc,_,ht,hf,hn⟩ := UnitHeadCode.Proof.actualPositiveClassification Γ i q hg hi
  have he : unitValue f q = denote (fun _ => 1) q := by
    unfold unitValue
    rw [zeroUnits]
    exact (CurrentAffineHeads.positiveNoCollapse Γ i q hi hg).2 f _
  exact ⟨_,fin,n,hc,by rw [he]; exact ht,by rw [he]; exact hf,by rw [he]; exact hn⟩

theorem literalCarrier : CurrentGroundAccountTargets.LiteralCarrier := by
  intro p f k Γ op ho
  let σ := Ty.curriedGround (k+1)
  let F : Variable (σ :: Γ) σ := .here
  obtain ⟨u,w,v,hA⟩ := CurrentSelectedCarriers.StatementChecks.actual_operator_carriers p f
    (σ :: Γ) k op.arity F op.source
  have he : u = op.vector := Option.some.inj (hA.1.symm.trans ho)
  subst u
  let src := CurrentSelectedCarriers.carrierAt F op.arity op.source
  let r : UnaryRecord (σ :: σ :: Γ) := ⟨src,v⟩
  have hv : AdmissibleAssignment.assignment p src = some v := hA.2.2.1
  refine ⟨r,w,?_,rfl,⟨hA,hv,hA.2.2.2.2.2.1,rfl⟩,?_⟩
  · simp only [carrierRecord,show CurrentSelectedCarriers.carrierAt
      (.here : Variable (σ :: Γ) σ) op.arity op.source = src from rfl,hv,bind,Option.bind_some,pure,r]
    rfl
  · have hcodec := SourceAnnotationCode.Proof.exactOperatorCodec (σ :: Γ) op
    have hFresh := SourceCarrierMapCode.Proof.concreteExact.2 Γ σ
      (Ty.curriedGround (op.arity+1)) op.source
    have hSat := NumericCarrierData.Proof.saturate_source op.arity (op.source.rename UnaryCarrier.renameTracked)
    have hClose : GroundCaptureClosingCode.sourceCode ((σ :: σ :: Γ).map SyntaxCode.typeCode) 0
        (SyntaxCode.encodeTerm (UnaryCarrier.saturate op.arity (op.source.rename UnaryCarrier.renameTracked))) =
      SyntaxCode.encodeTerm src :=
      GroundCaptureClosingCode.Proof.exactProtectedSource [] (σ :: σ :: Γ) (Ty.curriedGround 1) _
    have ha := CurrentGroundBudget.assignmentCode p src v hv
    simp only [List.map_cons,σ] at hClose ha
    unfold carrierCode
    simp only [hcodec.1,hcodec.2.1,List.map_cons,List.getD_cons_zero]
    rw [hFresh,hSat,hClose]
    simp only [ha,List.map_cons,bind,Option.bind_some,pure,r,recordCode,σ] <;> rfl

end LogicLineages.ControlSensitivityCurrent.CurrentGroundAccount
