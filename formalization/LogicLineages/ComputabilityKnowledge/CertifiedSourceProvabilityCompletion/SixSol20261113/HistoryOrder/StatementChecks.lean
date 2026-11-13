module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder.PairProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder.StatementChecks

theorem additiveSplit : Targets.AdditiveSplit := SplitProof.additiveSplit
theorem pairLowerOrder : Targets.PairLowerOrder := PairProof.pairLowerOrder
theorem pairUpperOrder : Targets.PairUpperOrder := PairProof.pairUpperOrder
theorem pairGraph : Targets.PairGraph := PairProof.pairGraph

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder
