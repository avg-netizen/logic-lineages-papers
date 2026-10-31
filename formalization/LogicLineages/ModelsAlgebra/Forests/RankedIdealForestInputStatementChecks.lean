module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealForestInputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealForestInput.StatementChecks
 theorem encodedGraphExact : Targets.EncodedGraphExact := Proof.encodedGraphExact
 theorem avoidanceExact : Targets.AvoidanceExact := Proof.avoidanceExact
 theorem forestJEPExact : Targets.ForestJEPExact := Proof.forestJEPExact
end LogicLineages.ModelsAlgebra.Forests.RankedIdealForestInput.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealForestInput
