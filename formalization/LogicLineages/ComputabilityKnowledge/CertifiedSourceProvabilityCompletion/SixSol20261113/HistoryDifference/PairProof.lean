module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference.ArithmeticProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference.PairProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof
open GorbowPRChildTags List.Vector

theorem pairLowerSector : Targets.PairLowerSector := by
  intro n p tag ht ctx a k
  have hd := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select
    HistoryCodec.pairArguments ht 0
  obtain ⟨hc⟩ := ArithmeticProof.differenceCancel n p (HistoryCodec.differenceTag tag) hd ctx a (.succ k)
  obtain ⟨hp⟩ := HistoryCodec.PairProof.internalPairPositive n p tag ht ctx a (.add a (.succ k)) k
  exact ⟨.mp hp hc⟩

theorem pairUpperSector : Targets.PairUpperSector := by
  intro n p tag ht ctx b k
  have hd := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select
    HistoryCodec.pairArguments ht 0
  obtain ⟨hc⟩ := ArithmeticProof.differenceSaturate n p (HistoryCodec.differenceTag tag) hd ctx b k
  obtain ⟨hp⟩ := HistoryCodec.PairProof.internalPairZero n p tag ht ctx (.add b k) b
  exact ⟨.mp hp hc⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference.PairProof
