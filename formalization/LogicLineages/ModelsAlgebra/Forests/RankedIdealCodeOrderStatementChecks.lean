module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealCodeOrderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealCodeOrder.StatementChecks
 theorem stateOrderExact : Targets.StateOrderExact := Proof.stateOrderExact
 theorem inclusionExact : Targets.InclusionExact := Proof.inclusionExact
end LogicLineages.ModelsAlgebra.Forests.RankedIdealCodeOrder.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealCodeOrder
