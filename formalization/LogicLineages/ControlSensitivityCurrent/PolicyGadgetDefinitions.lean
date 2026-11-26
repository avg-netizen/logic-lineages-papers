module
public import LogicLineages.OrdinalComparison.ParametricSourceAdditionDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyGadget
open LogicLineages.OrdinalComparison.Source
/-- Literal I0 vector, independent of a policy and of a collapse control. -/
def identityZeroVector (Γ : List Ty) : OrdinalVector Γ 0 := fun _ =>
  .collapse .one (.add (.add (.add .one .one) .one) .one)
end LogicLineages.ControlSensitivityCurrent.PolicyGadget
