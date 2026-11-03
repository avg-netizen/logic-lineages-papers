module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedRevisionProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedRevision.StatementChecks

theorem fullRevision : Targets.Target := Proof.fullTarget
theorem extensionModel : Targets.ExtensionModel := fullRevision.1
theorem stageAxioms : Targets.StageAxioms := fullRevision.2.1
theorem stageTheorems : Targets.StageTheorems := fullRevision.2.2.1
theorem theoremCodePersistence : Targets.TheoremCodePersistence := fullRevision.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowPublishedRevision.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedRevision
