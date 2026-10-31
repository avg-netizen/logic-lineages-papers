module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarNormalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarNormal.StatementChecks

theorem realizedBalance : Targets.RealizedBalance := Proof.realizedBalance

theorem normalStructure : Targets.NormalStructure := Proof.normalStructure

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarNormal.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarNormal
