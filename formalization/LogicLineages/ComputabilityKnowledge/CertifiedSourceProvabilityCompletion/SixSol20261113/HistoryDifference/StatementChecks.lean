module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference.PairProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference.StatementChecks

theorem predecessorZero : Targets.PredecessorZero := EquationsProof.predecessorZero
theorem predecessorSuccessor : Targets.PredecessorSuccessor := EquationsProof.predecessorSuccessor
theorem differenceShift : Targets.DifferenceShift := ShiftProof.differenceShift
theorem differenceCancel : Targets.DifferenceCancel := ArithmeticProof.differenceCancel
theorem differenceSaturate : Targets.DifferenceSaturate := ArithmeticProof.differenceSaturate
theorem pairLowerSector : Targets.PairLowerSector := PairProof.pairLowerSector
theorem pairUpperSector : Targets.PairUpperSector := PairProof.pairUpperSector

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference
