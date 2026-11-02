module
public import LogicLineages.OrdinalComparison.DeterministicCarrierDataTargets
public import LogicLineages.OrdinalComparison.DeterministicCarrierDataProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.DeterministicCarrierData.StatementChecks
theorem exact_saturation : Targets.ExactSaturation := Proof.exactSaturation
theorem exact_carrier_data : Targets.ExactCarrierData := Proof.exactCarrierData
theorem exact_carrier_list : Targets.ExactCarrierList := Proof.exactCarrierList
end LogicLineages.OrdinalComparison.Source.DeterministicCarrierData.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.DeterministicCarrierData
