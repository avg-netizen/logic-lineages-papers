module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlowProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlow.StatementChecks

theorem grammarFlowNecessary : Targets.GrammarFlowNecessary := Proof.grammarFlowNecessary

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlow.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlow
