module
public import LogicLineages.OrdinalComparison.SourceUnaryNormPaddingTargets
public import LogicLineages.OrdinalComparison.SourceUnaryNormPaddingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceUnaryNormPadding.StatementChecks
theorem exact_vector : Targets.ExactVector := Proof.exactVector
theorem admissible_extension : Targets.AdmissibleExtension := Proof.admissibleExtension
theorem polynomial_extension : Targets.PolynomialExtension := Proof.polynomialExtension
end LogicLineages.OrdinalComparison.Source.SourceUnaryNormPadding.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SourceUnaryNormPadding
