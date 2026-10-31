module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretationProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretation.StatementChecks

theorem internalHeader : Targets.InternalHeader := Proof.internalHeader
theorem internalTerm : Targets.InternalTerm := Proof.internalTerm
theorem namedFunction : Targets.NamedFunction := Proof.namedFunction
theorem namedRelation : Targets.NamedRelation := Proof.namedRelation
theorem specificNamedBridge : Targets.SpecificNamedBridge := Proof.specificNamedBridge

end LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretation.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretation.StatementChecks
