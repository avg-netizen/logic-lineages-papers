module

public import LogicLineages.ComputabilityKnowledge.GorbowPRSubtreeProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRSubtree.StatementChecks

theorem nodeBlocks : Targets.NodeBlocks := Proof.nodeBlocks
theorem lookupTransport : Targets.LookupTransport := Proof.lookupTransport

end LogicLineages.ComputabilityKnowledge.GorbowPRSubtree.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowPRSubtree.StatementChecks
