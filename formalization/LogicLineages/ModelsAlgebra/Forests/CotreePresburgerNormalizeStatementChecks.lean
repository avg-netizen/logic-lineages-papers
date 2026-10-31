module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerNormalizeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerNormalize.StatementChecks

theorem coefficientModulusPositive : Targets.CoefficientModulusPositive := Proof.coefficientModulusPositive
theorem adjustmentExact : Targets.AdjustmentExact := Proof.adjustmentExact
theorem normalizationExact : Targets.NormalizationExact := Proof.normalizationExact
theorem eliminationExact : Targets.EliminationExact := Proof.eliminationExact

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerNormalize.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerNormalize
