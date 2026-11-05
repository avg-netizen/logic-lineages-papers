module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.H10ReductionTargets
import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.H10BridgeProof
public meta import LogicLineages.Audit
public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SystemUndecidability.H10Export

/-- Exact checked theorem interface. The proof import is not re-exported;
the ordinary module system retains its verified axiom metadata and the build
receipt retains its full source dependency closure. -/
theorem bridge : H10ReductionTargets.CodedH10ToLinearSystems :=
  H10Adapter.Proof.codedH10ToLinearSystems

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SystemUndecidability.H10Export
#audit_namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SystemUndecidability.H10Export
