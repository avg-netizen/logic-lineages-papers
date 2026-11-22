module
public import LogicLineages.PermittedControl.StageEmitterGuardTargets
public import LogicLineages.PermittedControl.StageCallbackGuardRenderTargets
import LogicLineages.PermittedControl.StageEmitterGuardProof
import LogicLineages.PermittedControl.StageCallbackGuardRenderStatementChecks

public section
namespace LogicLineages.PermittedControl.StageCallbackGuardRender
open ClosedBlockDecision (ClosedBlockDecision)

/-- The guard rendering in exactly the frozen form of `StageEmitter.GuardExact`. -/
theorem guardExact : StageEmitter.GuardExact guardCode := StatementChecks.fixed_exactGuardCode

/-- The guard rendering in exactly the frozen form of `StageEmitter.GuardEffective`. -/
theorem guardEffective : StageEmitter.GuardEffective guardCode :=
  StatementChecks.fixed_guardCodeEffectivity.2.2

/-- Unconditional comparator for Paper 17 `thm:arithmetic`. -/
theorem closedBlockDecision : ClosedBlockDecision :=
  StageEmitter.exactClosedBlockDecisionFromGuard guardCode guardExact guardEffective

#print axioms guardExact
#print axioms guardEffective
#print axioms closedBlockDecision

end LogicLineages.PermittedControl.StageCallbackGuardRender
