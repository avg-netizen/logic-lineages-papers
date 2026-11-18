module
public import LogicLineages.ControlSensitivityCurrent.CurrentCompilerOutputProof
public import LogicLineages.ControlSensitivityCurrent.CurrentCompilerEffectiveProof
public import LogicLineages.ControlSensitivityCurrent.CompilerCompositionProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentCompiler.StatementChecks

/-- Paper19 `thm:compiler`, including the two actual computable source comparison outputs. -/
theorem fixed_complete_compiler : CurrentCompilerTargets.CompleteCompiler :=
  ⟨effective,literal_outputs,valid_codes,CompilerComposition.astCorrect,CompilerComposition.sharedCorrect,
    CompilerComposition.retention,CompilerComposition.outputBudgets⟩

#print axioms fixed_complete_compiler

end LogicLineages.ControlSensitivityCurrent.CurrentCompiler.StatementChecks
