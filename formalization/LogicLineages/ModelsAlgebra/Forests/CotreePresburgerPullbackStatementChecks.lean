module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerPullbackProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerPullback.StatementChecks

theorem wordCountsEqCount : Targets.WordCountsEqCount := Proof.wordCountsEqCount
theorem pushWordCountsExact : Targets.PushWordCountsExact := Proof.pushWordCountsExact
theorem pullFormulaExact : Targets.PullFormulaExact := Proof.pullFormulaExact
theorem pullWordExact : Targets.PullWordExact := Proof.pullWordExact

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerPullback.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerPullback
