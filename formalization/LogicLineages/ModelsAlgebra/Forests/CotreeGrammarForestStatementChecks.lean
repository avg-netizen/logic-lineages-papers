module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarForestProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarForest.StatementChecks

theorem forestBalance : Targets.ForestBalance := Proof.forestBalance

theorem forestTerminals : Targets.ForestTerminals := Proof.forestTerminals

theorem normalForestExists : Targets.NormalForestExists := Proof.normalForestExists

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarForest.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarForest
