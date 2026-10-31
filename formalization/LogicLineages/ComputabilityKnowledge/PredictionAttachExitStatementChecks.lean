module
public import LogicLineages.ComputabilityKnowledge.PredictionAttachExitProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionAttachExit.StatementChecks
theorem bridgeStep : Targets.BridgeStep := PredictionAttachExit.bridgeStep
theorem rightPhase : Targets.RightPhase := PredictionAttachExit.rightPhase
theorem fullComposition : Targets.FullComposition := PredictionAttachExit.fullComposition
end LogicLineages.ComputabilityKnowledge.PredictionAttachExit.StatementChecks
#audit_namespace LogicLineages.ComputabilityKnowledge.PredictionAttachExit.StatementChecks
