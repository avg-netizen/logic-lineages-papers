module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularProductProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularProduct.StatementChecks
 theorem productExact : Targets.ProductExact := Proof.productExact
 theorem downwardProductExact : Targets.DownwardProductExact := Proof.downwardProductExact
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularProduct.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularProduct
