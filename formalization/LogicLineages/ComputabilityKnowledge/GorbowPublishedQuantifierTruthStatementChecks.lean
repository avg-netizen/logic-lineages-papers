module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedQuantifierTruthProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedQuantifierTruth.StatementChecks

theorem fullQuantifierTruth : Targets.Target := Proof.fullTarget
theorem namedFunctions : Targets.NamedFunctions := fullQuantifierTruth.1
theorem namedRelations : Targets.NamedRelations := fullQuantifierTruth.2.1
theorem sourceDispatch : Targets.SourceDispatch := fullQuantifierTruth.2.2.1
theorem positiveQuantifierAxioms : Targets.PositiveQuantifierAxioms := fullQuantifierTruth.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowPublishedQuantifierTruth.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedQuantifierTruth
