module
public import LogicLineages.OrdinalComparison.SourceAnnotationCodeTargets
public import LogicLineages.OrdinalComparison.SourceAnnotationCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAnnotationCode.StatementChecks
theorem exact_operator_codec : Targets.ExactOperatorCodec := Proof.exactOperatorCodec
theorem exact_erasure : Targets.ExactErasure := Proof.exactErasure
theorem exact_repeat : Targets.ExactRepeat := Proof.exactRepeat
theorem exact_closing : Targets.ExactClosing := Proof.exactClosing
theorem primitive_recursive_algorithms : Targets.PrimitiveRecursiveAlgorithms := Proof.primitiveRecursiveAlgorithms
end LogicLineages.OrdinalComparison.Source.SourceAnnotationCode.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SourceAnnotationCode
