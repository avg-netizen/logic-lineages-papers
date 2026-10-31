module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealConstructors.StatementChecks
 theorem productIdeal : Targets.ProductIdeal := Proof.productIdeal
 theorem linearPieceIdeal : Targets.LinearPieceIdeal := Proof.linearPieceIdeal
 theorem contextSupport : Targets.ContextSupport := Proof.contextSupport
end LogicLineages.ModelsAlgebra.Forests.RankedIdealConstructors.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealConstructors
