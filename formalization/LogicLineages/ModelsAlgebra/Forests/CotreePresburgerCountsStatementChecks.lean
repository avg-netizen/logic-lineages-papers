module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCountsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCounts.StatementChecks

theorem wordCountsExact : Targets.WordCountsExact := Proof.wordCountsExact
theorem formulaCountsExact : Targets.FormulaCountsExact := Proof.formulaCountsExact

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCounts.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCounts
