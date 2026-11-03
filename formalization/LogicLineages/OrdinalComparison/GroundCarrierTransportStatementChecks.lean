module
public import LogicLineages.OrdinalComparison.GroundCarrierTransportTargets
public import LogicLineages.OrdinalComparison.GroundCarrierTransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundCarrierTransport.StatementChecks
theorem exact_unit_value : Targets.ExactUnitValue := Proof.exactUnitValue
theorem tracked_invariants : Targets.TrackedInvariants := Proof.trackedInvariants
theorem exact_account_transport : Targets.ExactAccountTransport := Proof.exactAccountTransport
theorem actual_source_ground_transport : Targets.ActualSourceGroundTransport := Proof.actualSourceGroundTransport
end LogicLineages.OrdinalComparison.Source.GroundCarrierTransport.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.GroundCarrierTransport
