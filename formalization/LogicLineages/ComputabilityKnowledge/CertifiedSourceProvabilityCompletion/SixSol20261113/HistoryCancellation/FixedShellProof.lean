module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.ArithmeticProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.FixedShellProof
open GorbowSyntax GorbowTheoryProof
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem pairLowerFixedSecond : Targets.PairLowerFixedSecond := by
  intro n p tag ht ctx a b c
  let T := GorbowPRNumeralCalculation.Theory p
  let L := HistoryOrder.lower a b
  let R := HistoryOrder.lower c b
  let E := Formula.equal (HistoryDifference.pairCall tag a b) (HistoryDifference.pairCall tag c b)
  obtain ⟨hl⟩ := HistoryOrder.PairProof.pairLowerOrder n p tag ht ctx a b
  obtain ⟨hr⟩ := HistoryOrder.PairProof.pairLowerOrder n p tag ht ctx c b
  have hL : Hilbert.Local T ctx [E,R,L] L := .hypothesis (by simp)
  have hR : Hilbert.Local T ctx [E,R,L] R := .hypothesis (by simp)
  have hE : Hilbert.Local T ctx [E,R,L] E := .hypothesis List.mem_cons_self
  have hvL := Hilbert.Local.mp (.base hl) hL
  have hvR := Hilbert.Local.mp (.base hr) hR
  have he := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hvL)
    (localTrans _ _ _ hE hvR)
  have hout : Hilbert.Local T ctx [E,R,L] (.equal a c) :=
    .mp (.base (ArithmeticProof.left a c (.mul b b))) he
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
    (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))⟩

theorem pairUpperFixedFirst : Targets.PairUpperFixedFirst := by
  intro n p tag ht ctx a b c
  let T := GorbowPRNumeralCalculation.Theory p
  let L := HistoryOrder.upper a b
  let R := HistoryOrder.upper a c
  let E := Formula.equal (HistoryDifference.pairCall tag a b) (HistoryDifference.pairCall tag a c)
  obtain ⟨hl⟩ := HistoryOrder.PairProof.pairUpperOrder n p tag ht ctx a b
  obtain ⟨hr⟩ := HistoryOrder.PairProof.pairUpperOrder n p tag ht ctx a c
  have hL : Hilbert.Local T ctx [E,R,L] L := .hypothesis (by simp)
  have hR : Hilbert.Local T ctx [E,R,L] R := .hypothesis (by simp)
  have hE : Hilbert.Local T ctx [E,R,L] E := .hypothesis List.mem_cons_self
  have hvL := Hilbert.Local.mp (.base hl) hL
  have hvR := Hilbert.Local.mp (.base hr) hR
  have he := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hvL)
    (localTrans _ _ _ hE hvR)
  have hout : Hilbert.Local T ctx [E,R,L] (.equal b c) :=
    .mp (.base (ArithmeticProof.left b c (.add (.mul a a) a))) he
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
    (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.FixedShellProof
