module

public import LogicLineages.ComputabilityKnowledge.GorbowPRChildTagsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRChildTags.StatementChecks

theorem compositionFunction : Targets.CompositionFunction := Proof.compositionFunction
theorem compositionArgument : Targets.CompositionArgument := Proof.compositionArgument
theorem recursionBase : Targets.RecursionBase := Proof.recursionBase
theorem recursionStep : Targets.RecursionStep := Proof.recursionStep

end LogicLineages.ComputabilityKnowledge.GorbowPRChildTags.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowPRChildTags.StatementChecks
