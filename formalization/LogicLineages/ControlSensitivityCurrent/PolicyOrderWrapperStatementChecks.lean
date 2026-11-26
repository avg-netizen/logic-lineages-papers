module
public import LogicLineages.ControlSensitivityCurrent.PolicyOrderWrapperProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyOrderWrapper.StatementChecks
theorem fixed_identity : PolicyOrderWrapperTargets.Identity := identityValue
theorem fixed_constant : PolicyOrderWrapperTargets.Constant := constantValue
theorem fixed_magnify : PolicyOrderWrapperTargets.Magnify := magnifyValue
theorem fixed_order_conversion : PolicyOrderWrapperTargets.OrderConversion := orderConversion
#print axioms fixed_identity
#print axioms fixed_constant
#print axioms fixed_magnify
#print axioms fixed_order_conversion
end LogicLineages.ControlSensitivityCurrent.PolicyOrderWrapper.StatementChecks
