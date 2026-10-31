module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammar.StatementChecks

theorem rulesExact : Targets.RulesExact := Proof.rulesExact

theorem grammarLanguageExact : Targets.GrammarLanguageExact := Proof.grammarLanguageExact

theorem skeletonNonempty : Targets.SkeletonNonempty := Proof.skeletonNonempty

theorem countPermutationExact : Targets.CountPermutationExact := Proof.countPermutationExact

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammar.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammar
