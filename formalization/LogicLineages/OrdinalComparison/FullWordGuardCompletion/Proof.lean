module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.CompilerComparisonProof
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.CompilerProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.Proof

theorem fullWordGuards : Targets.FullWordGuards :=
  ⟨compilerCalibration,compiledSyntax,compiledDomains,compiledThreeWay,
    compiledSameVariable,CompilerProgramsProof.boundedCompilerPrograms,
    CompilerProgramsProof.compilerProgram⟩

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.Proof
