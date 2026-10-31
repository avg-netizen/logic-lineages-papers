module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCountsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCounts.StatementChecks

theorem childCountExact : Targets.ChildCountExact := Proof.childCountExact
theorem stateCountExact : Targets.StateCountExact := Proof.stateCountExact

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCounts.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCounts
