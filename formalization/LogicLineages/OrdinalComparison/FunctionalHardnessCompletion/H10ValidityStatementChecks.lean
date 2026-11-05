module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.H10ValidityCalibrationProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.H10ValidityProgramsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Validity.StatementChecks

theorem variables_validity : Targets.VariablesValidity := Proof.variablesValidity
theorem terms_validity : Targets.TermsValidity := Proof.termsValidity
theorem input_validity : Targets.InputValidity := Proof.inputValidity
theorem canonical_validity : Targets.CanonicalValidity := Proof.canonicalValidity
theorem validity_primitive : Targets.ValidityPrimitive := Proof.validityPrimitive

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Validity.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Validity.StatementChecks
