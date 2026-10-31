module

public import LogicLineages.ComputabilityKnowledge.GorbowPRRegistryProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRRegistry.StatementChecks

theorem exactNodes : Targets.ExactNodes := Proof.exactNodes
theorem rootTag : Targets.RootTag := Proof.rootTag
theorem taggedCoverage : Targets.TaggedCoverage := Proof.taggedCoverage
theorem uniqueTags : Targets.UniqueTags := Proof.uniqueTags
theorem exactDispatch : Targets.ExactDispatch := Proof.exactDispatch
theorem invalidTag : Targets.InvalidTag := Proof.invalidTag
theorem invalidArity : Targets.InvalidArity := Proof.invalidArity

end LogicLineages.ComputabilityKnowledge.GorbowPRRegistry.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowPRRegistry.StatementChecks
