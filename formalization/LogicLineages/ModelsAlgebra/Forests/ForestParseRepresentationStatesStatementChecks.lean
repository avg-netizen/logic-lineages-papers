module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStatesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStates.StatementChecks

theorem stateSetLeaf : Targets.StateSetLeaf := Proof.stateSetLeaf
theorem stateSetGraphExact : Targets.StateSetGraphExact := Proof.stateSetGraphExact
theorem stateSetNodeExact : Targets.StateSetNodeExact := Proof.stateSetNodeExact
theorem stateSetAcceptExact : Targets.StateSetAcceptExact := Proof.stateSetAcceptExact

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStates.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStates
