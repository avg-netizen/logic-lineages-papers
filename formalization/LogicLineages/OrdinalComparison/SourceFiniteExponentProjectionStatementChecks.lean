module
public import LogicLineages.OrdinalComparison.SourceFiniteExponentProjectionTargets
public import LogicLineages.OrdinalComparison.SourceFiniteExponentProjectionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceFiniteExponentProjection.StatementChecks
theorem exact_coefficients : Targets.ExactCoefficients := Proof.exactCoefficients
theorem signed_operations : Targets.SignedOperations := Proof.signedOperations
theorem exact_shift : Targets.ExactShift := Proof.exactShift
theorem expression_transport : Targets.ExpressionTransport := Proof.expressionTransport
end LogicLineages.OrdinalComparison.Source.SourceFiniteExponentProjection.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SourceFiniteExponentProjection
