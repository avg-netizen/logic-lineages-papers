module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedDCBProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedDCB.StatementChecks

theorem fullPublishedDCB : Targets.Target := Proof.fullTarget
theorem finiteSPresentation : Targets.FiniteSPresentation := fullPublishedDCB.1
theorem actualParameters : Targets.ActualParameters := fullPublishedDCB.2.1
theorem publishedDiagonal : Targets.PublishedDiagonal := fullPublishedDCB.2.2.1
theorem provabilityCalibration : Targets.ProvabilityCalibration := fullPublishedDCB.2.2.2.1
theorem sProofCertification : Targets.SProofCertification := fullPublishedDCB.2.2.2.2.1
theorem dProofCertification : Targets.DProofCertification := fullPublishedDCB.2.2.2.2.2.1
theorem selectedReflection : Targets.SelectedReflection := fullPublishedDCB.2.2.2.2.2.2.1
theorem selectedDistribution : Targets.SelectedDistribution := fullPublishedDCB.2.2.2.2.2.2.2.1
theorem completeThree : Targets.CompleteThree := fullPublishedDCB.2.2.2.2.2.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowPublishedDCB.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedDCB
