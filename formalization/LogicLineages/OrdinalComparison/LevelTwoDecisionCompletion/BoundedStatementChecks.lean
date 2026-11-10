module
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.BoundedWitnessProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.BoundedStatementChecks

theorem exact_matrix_semantics : Targets.ExactMatrixSemantics := MatrixProof.exactMatrixSemantics

theorem emitted_package_shape : Targets.EmittedPackageShape := MetadataProof.emittedPackageShape

theorem literal_package_metadata : Targets.LiteralPackageMetadata := MetadataProof.literalPackageMetadata

theorem emitted_package_metadata : Targets.EmittedPackageMetadata := MetadataProof.emittedPackageMetadata

theorem exact_matrix_syntax : Targets.ExactMatrixSyntax := MatrixProof.exactMatrixSyntax

theorem exact_closed_package : Targets.ExactClosedPackage := MatrixProof.exactClosedPackage

theorem literal_code_calibration : Targets.LiteralCodeCalibration := CodeProof.literalCodeCalibration

theorem actual_matrix_program : Targets.ActualMatrixProgram := CodePrograms.actualMatrixProgram

theorem actual_package_decision : Targets.ActualPackageDecision := DecisionProof.actualPackageDecision

theorem exact_source_domain : Targets.ExactSourceDomain := DecisionProof.exactSourceDomain

theorem actual_numeric_programs : Targets.ActualNumericPrograms := ProgramsProof.actualNumericPrograms

theorem actual_typed_decision : Targets.ActualTypedDecision := BoundedDecisionProof.actualTypedDecision

/-- The concrete solver on original source codes and original positive
valuations, checked at the frozen full theorem comparator. -/
theorem full_internal_level_two_comparison : Targets.FullInternalLevelTwoComparison :=
  BoundedWitnessProof.fullInternalLevelTwoComparison

#print axioms exact_matrix_semantics
#print axioms emitted_package_shape
#print axioms literal_package_metadata
#print axioms emitted_package_metadata
#print axioms exact_matrix_syntax
#print axioms exact_closed_package
#print axioms literal_code_calibration
#print axioms actual_matrix_program
#print axioms actual_package_decision
#print axioms exact_source_domain
#print axioms actual_numeric_programs
#print axioms actual_typed_decision
#print axioms full_internal_level_two_comparison

end LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.BoundedStatementChecks

#audit_namespace LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.BoundedStatementChecks
