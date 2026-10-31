module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarShapeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarShape.StatementChecks

theorem shapeLanguageExact : Targets.ShapeLanguageExact := Proof.shapeLanguageExact

theorem graftRunExact : Targets.GraftRunExact := Proof.graftRunExact

theorem graftGrammarSound : Targets.GraftGrammarSound := Proof.graftGrammarSound

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarShape.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarShape
