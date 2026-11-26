module
public import LogicLineages.PermittedControl.StageEmitterGuardTargets
import LogicLineages.PermittedControl.StageEmitterHighProof
import LogicLineages.PermittedControl.RawPacketAlgebraJoinCalibrationProof
import LogicLineages.PermittedControl.RawPacketAlgebraJoinEffectivityProof
import LogicLineages.PermittedControl.StageCallbackRenderLinearCalibrationProof
import LogicLineages.PermittedControl.StageCallbackRenderLinearEffectivityProof
import LogicLineages.PermittedControl.StageCallbackRenderModularCalibrationProof
import LogicLineages.PermittedControl.StageCallbackRenderModularEffectivityProof

public section
namespace LogicLineages.PermittedControl.StageEmitter
open RawPacketAlgebra (exactAppendCode joinEffectivity)
open StageCallbackRender (exactLinearCode linearCodeEffectivity exactModularCode modularCodeEffectivity)

theorem exactRenderingFromGuard : ExactRenderingFromGuard := by
  intro g exact effective
  refine ⟨⟨exactAppendCode,exact,exactLinearCode,exactModularCode⟩,
    ⟨joinEffectivity.2.1,effective,linearCodeEffectivity.2.2.2.2.2,modularCodeEffectivity.2.2⟩⟩

theorem exactClosedBlockDecisionFromGuard : ExactClosedBlockDecisionFromGuard := by
  intro g exact effective
  obtain ⟨hR,hE⟩ := exactRenderingFromGuard g exact effective
  exact exactConditionalClosedBlockDecision ⟨renderingWith g,hR,hE⟩

theorem fullStageEmitterGuard : FullStageEmitterGuard :=
  ⟨exactRenderingFromGuard,exactClosedBlockDecisionFromGuard⟩

#print axioms exactRenderingFromGuard
#print axioms exactClosedBlockDecisionFromGuard
#print axioms fullStageEmitterGuard
end LogicLineages.PermittedControl.StageEmitter
