module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.BranchProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.SuffixProof
open GorbowPRProgram HistoryRuleSuffix IndependenceProof PreservationProof

theorem rulePreserves (logical arithmetic : Program 1) (axiomProgram : Program 3) :
    Preserves (ruleDispatcher logical arithmetic axiomProgram) :=
  ruleSelectPreserves 0 (independentPreserves (unaryLeafIndependent logical))
    (ruleSelectPreserves 1 (independentPreserves (unaryLeafIndependent arithmetic))
      (ruleSelectPreserves 2 (conjunctionPreserves commonIndependent BranchProof.mpPreserves)
        (ruleSelectPreserves 3 (conjunctionPreserves generalizeIndependent BranchProof.generalizePreserves)
          (ruleSelectPreserves 4 (independentPreserves (axiomIndependent axiomProgram))
            (independentPreserves (constantIndependent 0))))))

theorem internalLineSuffix : Targets.InternalLineSuffix := by
  intro valid logical arithmetic axiomProgram
  exact conjunctionPreserves (unaryLeafIndependent valid) (rulePreserves logical arithmetic axiomProgram)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.SuffixProof
