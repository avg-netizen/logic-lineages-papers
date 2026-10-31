module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProjectionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProjection.StatementChecks

theorem projectedWordCounts : Targets.ProjectedWordCounts := Proof.projectedWordCounts
theorem wordTotalCounts : Targets.WordTotalCounts := Proof.wordTotalCounts
theorem allowedWordCounts : Targets.AllowedWordCounts := Proof.allowedWordCounts

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProjection.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProjection
