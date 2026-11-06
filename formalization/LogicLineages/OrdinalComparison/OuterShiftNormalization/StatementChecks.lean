module
public import LogicLineages.OrdinalComparison.OuterShiftNormalization.TerminalProof
public import LogicLineages.OrdinalComparison.OuterShiftNormalization.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.OuterShiftNormalization.StatementChecks

theorem fixed_splitSyntax : Targets.SplitSyntax := Proof.splitSyntax
theorem fixed_normalizationSyntax : Targets.NormalizationSyntax := Proof.normalizationSyntax
theorem fixed_shiftSumCorrect : Targets.ShiftSumCorrect := Proof.shiftSumCorrect
theorem fixed_normalizationCorrect : Targets.NormalizationCorrect := Proof.normalizationCorrect
theorem fixed_tailNormalization : Targets.TailNormalization := Proof.tailNormalization
theorem fixed_leafComparisons : Targets.LeafComparisons := Proof.leafComparisons
theorem fixed_leafWordComparisons : Targets.LeafWordComparisons := Proof.leafWordComparisons
theorem fixed_nonlinearLeafGuard : Targets.NonlinearLeafGuard := Proof.nonlinearLeafGuard
theorem fixed_normalizationPrograms : Targets.NormalizationPrograms := Proof.normalizationPrograms

#print axioms fixed_splitSyntax
#print axioms fixed_normalizationSyntax
#print axioms fixed_shiftSumCorrect
#print axioms fixed_normalizationCorrect
#print axioms fixed_tailNormalization
#print axioms fixed_leafComparisons
#print axioms fixed_leafWordComparisons
#print axioms fixed_nonlinearLeafGuard
#print axioms fixed_normalizationPrograms

end LogicLineages.OrdinalComparison.OuterShiftNormalization.StatementChecks
