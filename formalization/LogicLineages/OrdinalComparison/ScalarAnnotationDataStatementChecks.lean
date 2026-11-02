module
public import LogicLineages.OrdinalComparison.ScalarAnnotationDataTargets
public import LogicLineages.OrdinalComparison.ScalarAnnotationDataProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ScalarAnnotationData.StatementChecks
theorem exact_certificates : Targets.ExactCertificates := Proof.exactCertificates
theorem exact_ground_closure : Targets.ExactGroundClosure := Proof.exactGroundClosure
theorem exact_ground_partial : Targets.ExactGroundPartial := Proof.exactGroundPartial
end LogicLineages.OrdinalComparison.Source.ScalarAnnotationData.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.ScalarAnnotationData
