module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerSingleProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerCompilerProgramsProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.ContractTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerProof

/-- Concrete original-name compiler: literal ranked stages, actual finite
work-stack termination, least-stopping search, then finite case products. -/
theorem fullRankedCancellation : ContractTargets.FullRankedCancellation :=
  ⟨Runner.compile,RunnerCode.actualFamilyProgram,exactFamilyPackage⟩

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerProof
