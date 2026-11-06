module
public import LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.TerminalProof
public import LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.StatementChecks

theorem fixed_letterGrowth : Targets.LetterGrowth := Proof.letterGrowth
theorem fixed_compensatedGrowth : Targets.CompensatedGrowth := Proof.compensatedGrowth
theorem fixed_wordGrowth : Targets.WordGrowth := Proof.wordGrowth
theorem fixed_terminalGuard : Targets.TerminalGuard := Proof.terminalGuard
theorem fixed_growthPrograms : Targets.GrowthPrograms := Proof.growthPrograms

#print axioms fixed_letterGrowth
#print axioms fixed_compensatedGrowth
#print axioms fixed_wordGrowth
#print axioms fixed_terminalGuard
#print axioms fixed_growthPrograms

end LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.StatementChecks
