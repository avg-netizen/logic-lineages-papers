module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.Proof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.StatementChecks

theorem fixed_booleanGuardsCorrect : Targets.BooleanGuardsCorrect := Proof.booleanGuardsCorrect
theorem fixed_terminalSyntax : Targets.TerminalSyntax := Proof.terminalSyntax
theorem fixed_terminalComparison : Targets.TerminalComparison := Proof.terminalComparison
theorem fixed_terminalSameVariable : Targets.TerminalSameVariable := Proof.terminalSameVariable
theorem fixed_compilerCalibration : Targets.CompilerCalibration := Proof.compilerCalibration
theorem fixed_compiledSyntax : Targets.CompiledSyntax := Proof.compiledSyntax
theorem fixed_compiledDomains : Targets.CompiledDomains := Proof.compiledDomains
theorem fixed_compiledThreeWay : Targets.CompiledThreeWay := Proof.compiledThreeWay
theorem fixed_compiledSameVariable : Targets.CompiledSameVariable := Proof.compiledSameVariable
theorem fixed_boundedCompilerPrograms : Targets.BoundedCompilerPrograms := CompilerProgramsProof.boundedCompilerPrograms
theorem fixed_compilerProgram : Targets.CompilerProgram := CompilerProgramsProof.compilerProgram
theorem fixed_fullWordGuards : Targets.FullWordGuards := Proof.fullWordGuards

#print axioms fixed_booleanGuardsCorrect
#print axioms fixed_terminalSyntax
#print axioms fixed_terminalComparison
#print axioms fixed_terminalSameVariable
#print axioms fixed_compilerCalibration
#print axioms fixed_compiledSyntax
#print axioms fixed_compiledDomains
#print axioms fixed_compiledThreeWay
#print axioms fixed_compiledSameVariable
#print axioms fixed_boundedCompilerPrograms
#print axioms fixed_compilerProgram
#print axioms fixed_fullWordGuards

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.StatementChecks
