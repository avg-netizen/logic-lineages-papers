module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarConnectedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarConnected.StatementChecks

theorem connectedFlowNecessary : Targets.ConnectedFlowNecessary := Proof.connectedFlowNecessary

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarConnected.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarConnected
