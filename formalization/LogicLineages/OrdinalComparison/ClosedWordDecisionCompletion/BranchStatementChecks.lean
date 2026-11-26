module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchAssemblyProof
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchCodeProof
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchProgramsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchStatementChecks

theorem exact_residue_syntax : BranchTargets.ExactResidueSyntax :=
  ResidueAdapterProof.exactResidueSyntax

theorem exact_residue_semantics : BranchTargets.ExactResidueSemantics :=
  ResidueAdapterProof.exactResidueSemantics

theorem actual_child_syntax : BranchTargets.ActualChildSyntax :=
  BranchProof.actualChildSyntax

theorem actual_child_equivalence : BranchTargets.ActualChildEquivalence :=
  BranchProof.actualChildEquivalence

theorem literal_code_calibration : BranchTargets.LiteralCodeCalibration :=
  CodeProof.literalCodeCalibration

theorem actual_numeric_programs : BranchTargets.ActualNumericPrograms :=
  CodePrograms.actualNumericPrograms

theorem full_branch_assembly : BranchTargets.FullBranchAssembly :=
  ⟨exact_residue_syntax,exact_residue_semantics,actual_child_syntax,
    actual_child_equivalence,literal_code_calibration,actual_numeric_programs⟩

#print axioms exact_residue_syntax
#print axioms exact_residue_semantics
#print axioms actual_child_syntax
#print axioms actual_child_equivalence
#print axioms literal_code_calibration
#print axioms actual_numeric_programs
#print axioms full_branch_assembly

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchStatementChecks

#audit_namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchStatementChecks
