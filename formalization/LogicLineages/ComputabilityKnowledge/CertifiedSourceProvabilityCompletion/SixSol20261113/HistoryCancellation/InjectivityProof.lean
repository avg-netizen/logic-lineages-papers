module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.SectorProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.InjectivityProof
open GorbowSyntax GorbowTheoryProof

theorem pairInjective : Targets.PairInjective := by
  intro n p tag ht ctx a b c d
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := Formula.imp
    (.equal (HistoryDifference.pairCall tag a b) (HistoryDifference.pairCall tag c d))
    (.conj (.equal a c) (.equal b d))
  obtain ⟨hll⟩ := SectorProof.lowerLower p tag ht a b c d
  obtain ⟨hlu⟩ := SectorProof.lowerUpper p tag ht a b c d
  obtain ⟨hul⟩ := SectorProof.upperLower p tag ht a b c d
  obtain ⟨huu⟩ := SectorProof.upperUpper p tag ht a b c d
  obtain ⟨hs1⟩ := HistoryOrder.SplitProof.additiveSplit T ctx a b
  obtain ⟨hs2⟩ := HistoryOrder.SplitProof.additiveSplit T ctx c d
  have hl : Derivation T (.imp (HistoryOrder.lower a b) Q) := by
    have h : Hilbert.Local T ctx [HistoryOrder.lower a b] (HistoryOrder.lower a b) := .hypothesis List.mem_cons_self
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (.mp (.mp (.mp (.base (.logical (.orElim _ _ _))) (.mp (.base hll) h))
        (.mp (.base hlu) h)) (.base hs2)))
  have hu : Derivation T (.imp (HistoryOrder.upper a b) Q) := by
    have h : Hilbert.Local T ctx [HistoryOrder.upper a b] (HistoryOrder.upper a b) := .hypothesis List.mem_cons_self
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (.mp (.mp (.mp (.base (.logical (.orElim _ _ _))) (.mp (.base hul) h))
        (.mp (.base huu) h)) (.base hs2)))
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hl) hu) hs1⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.InjectivityProof
