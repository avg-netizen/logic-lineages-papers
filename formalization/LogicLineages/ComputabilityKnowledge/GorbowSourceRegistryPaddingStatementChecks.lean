module

public import LogicLineages.ComputabilityKnowledge.GorbowSourceRegistryPaddingProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSourceRegistryPadding.StatementChecks

theorem layout : Targets.Layout := Proof.layout
theorem functionRoot : Targets.FunctionRoot := Proof.functionRoot
theorem relationRoot : Targets.RelationRoot := Proof.relationRoot
theorem lowTagsHighArity : Targets.LowTagsHighArity := Proof.lowTagsHighArity
theorem headerDisjoint : Targets.HeaderDisjoint := Proof.headerDisjoint
theorem specificPrograms : Targets.SpecificPrograms := Proof.specificPrograms

end LogicLineages.ComputabilityKnowledge.GorbowSourceRegistryPadding.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowSourceRegistryPadding.StatementChecks
