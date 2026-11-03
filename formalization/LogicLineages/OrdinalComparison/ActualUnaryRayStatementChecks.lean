module
public import LogicLineages.OrdinalComparison.ActualUnaryRayTargets
public import LogicLineages.OrdinalComparison.ActualUnaryRayProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualUnaryRay.StatementChecks
theorem genuine_ray_and_computability : Targets.GenuineRayAndComputability := Proof.genuineRayAndComputability
theorem actual_source_ray : Targets.ActualSourceRay := Proof.actualSourceRay
theorem actual_ray_observation : Targets.ActualRayObservation := Proof.actualRayObservation
end LogicLineages.OrdinalComparison.Source.ActualUnaryRay.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.ActualUnaryRay
