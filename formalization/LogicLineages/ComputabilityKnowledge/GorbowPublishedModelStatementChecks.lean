module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedModelProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedModel.StatementChecks

theorem fullPublishedModel : Targets.Target := Proof.fullTarget
theorem guardCalibration : Targets.GuardCalibration := fullPublishedModel.1
theorem implicationCalibration : Targets.ImplicationCalibration := fullPublishedModel.2.1
theorem sProvabilityCalibration : Targets.SProvabilityCalibration := fullPublishedModel.2.2.1
theorem dProvabilityCalibration : Targets.DProvabilityCalibration := fullPublishedModel.2.2.2.1
theorem theoremSetModel : Targets.TheoremSetModel := fullPublishedModel.2.2.2.2.1
theorem consistency : Targets.Consistency := fullPublishedModel.2.2.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowPublishedModel.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedModel
