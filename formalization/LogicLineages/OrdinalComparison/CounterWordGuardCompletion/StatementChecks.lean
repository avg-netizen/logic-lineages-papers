module
public import LogicLineages.OrdinalComparison.CounterWordGuardCompletion.WordProof
public import LogicLineages.OrdinalComparison.CounterWordGuardCompletion.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterWordGuardCompletion.StatementChecks

theorem fixed_leaderWordCorrect : Targets.LeaderWordCorrect := Proof.leaderWordCorrect
theorem fixed_sourceShiftedCounterOrder : Targets.SourceShiftedCounterOrder := Proof.sourceShiftedCounterOrder
theorem fixed_counterWordGuardCorrect : Targets.CounterWordGuardCorrect := Proof.counterWordGuardCorrect
theorem fixed_counterHeadDecrease : Targets.CounterHeadDecrease := Proof.counterHeadDecrease
theorem fixed_guardPrograms : Targets.GuardPrograms := Proof.guardPrograms

#print axioms fixed_leaderWordCorrect
#print axioms fixed_sourceShiftedCounterOrder
#print axioms fixed_counterWordGuardCorrect
#print axioms fixed_counterHeadDecrease
#print axioms fixed_guardPrograms

end LogicLineages.OrdinalComparison.CounterWordGuardCompletion.StatementChecks
