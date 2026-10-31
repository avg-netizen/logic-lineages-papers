module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationComponentsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationComponents.StatementChecks

theorem fiberReachability : Targets.FiberReachability := Proof.fiberReachability

theorem fiberIsoRecovery : Targets.FiberIsoRecovery := Proof.fiberIsoRecovery

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationComponents.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationComponents
