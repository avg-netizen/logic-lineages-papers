module
public import LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.WordProof
public import LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.StatementChecks

theorem fixed_rangeHeadPreimage : Targets.RangeHeadPreimage := Proof.rangeHeadPreimage
theorem fixed_counterRangeWordGuardCorrect : Targets.CounterRangeWordGuardCorrect := Proof.counterRangeWordGuardCorrect
theorem fixed_counterHeadDecrease : Targets.CounterHeadDecrease := Proof.counterHeadDecrease
theorem fixed_guardPrograms : Targets.GuardPrograms := Proof.guardPrograms

#print axioms fixed_rangeHeadPreimage
#print axioms fixed_counterRangeWordGuardCorrect
#print axioms fixed_counterHeadDecrease
#print axioms fixed_guardPrograms

end LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.StatementChecks
