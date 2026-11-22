module
public import LogicLineages.PermittedControl.StageCallbackGuardRenderRecordTargets
import LogicLineages.PermittedControl.StageCallbackGuardRenderStatementChecks
import LogicLineages.PermittedControl.StageCallbackRenderLinearStatementChecks
import LogicLineages.PermittedControl.StageCallbackRenderModularStatementChecks
import LogicLineages.PermittedControl.RawPacketAlgebraJoinCalibrationProof
import LogicLineages.PermittedControl.RawPacketAlgebraJoinEffectivityProof

public section
namespace LogicLineages.PermittedControl.StageCallbackGuardRender

theorem exactR₀ : ExactR₀ :=
  ⟨RawPacketAlgebra.exactAppendCode,StatementChecks.fixed_exactGuardCode,
    StatementChecks.fixed_exactLinearCode,StatementChecks.fixed_exactModularCode⟩

theorem effectiveR₀ : EffectiveR₀ :=
  ⟨RawPacketAlgebra.appendPrimitive,StatementChecks.fixed_guardCodeEffectivity.2.2,
    StatementChecks.fixed_linearCodeEffectivity.2.2.2.2.2,StatementChecks.fixed_modularCodeEffectivity.2.2⟩

theorem fullR₀ : FullR₀ := ⟨exactR₀,effectiveR₀⟩

#print axioms exactR₀
#print axioms effectiveR₀
#print axioms fullR₀

end LogicLineages.PermittedControl.StageCallbackGuardRender
