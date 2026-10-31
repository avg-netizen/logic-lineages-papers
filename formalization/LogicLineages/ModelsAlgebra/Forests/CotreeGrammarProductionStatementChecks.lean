module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarProductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarProduction.StatementChecks

theorem binaryFactorization : Targets.BinaryFactorization := Proof.binaryFactorization

theorem containsFactorization : Targets.ContainsFactorization := Proof.containsFactorization

theorem exactContextDichotomy : Targets.ExactContextDichotomy := Proof.exactContextDichotomy

theorem cycleRotateProduction : Targets.CycleRotateProduction := Proof.cycleRotateProduction

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarProduction.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarProduction
