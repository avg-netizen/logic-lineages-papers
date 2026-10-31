module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationACProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationAC.StatementChecks

theorem graphAssociationSound : Targets.GraphAssociationSound := Proof.graphAssociationSound

theorem rootConnectivity : Targets.RootConnectivity := Proof.rootConnectivity

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationAC.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationAC
