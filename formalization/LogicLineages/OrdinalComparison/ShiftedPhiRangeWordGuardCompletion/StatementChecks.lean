module
public import LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.WordProof
public import LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.StatementChecks

theorem fixed_shiftedPhiOrder : Targets.ShiftedPhiOrder := Proof.shiftedPhiOrder
theorem fixed_phiRangeWordGuardCorrect : Targets.PhiRangeWordGuardCorrect := Proof.phiRangeWordGuardCorrect
theorem fixed_headDecrease : Targets.HeadDecrease := Proof.headDecrease
theorem fixed_guardPrograms : Targets.GuardPrograms := Proof.guardPrograms

#print axioms fixed_shiftedPhiOrder
#print axioms fixed_phiRangeWordGuardCorrect
#print axioms fixed_headDecrease
#print axioms fixed_guardPrograms

end LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.StatementChecks
