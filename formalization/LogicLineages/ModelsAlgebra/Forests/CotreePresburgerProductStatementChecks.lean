module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProductProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProduct.StatementChecks

theorem productRunsExact : Targets.ProductRunsExact := Proof.productRunsExact
theorem productLanguageExact : Targets.ProductLanguageExact := Proof.productLanguageExact
theorem productComplete : Targets.ProductComplete := Proof.productComplete
theorem differenceLanguageExact : Targets.DifferenceLanguageExact := Proof.differenceLanguageExact
theorem inclusionToEmpty : Targets.InclusionToEmpty := Proof.inclusionToEmpty
theorem sourceInclusionToEmpty : Targets.SourceInclusionToEmpty := Proof.sourceInclusionToEmpty

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProduct.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProduct
