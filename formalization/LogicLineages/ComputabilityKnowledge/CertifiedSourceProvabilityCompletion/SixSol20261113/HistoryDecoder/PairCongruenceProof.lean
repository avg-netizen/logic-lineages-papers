module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.PairCongruenceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

/-- Distinct installed copies of the literal pair AST agree internally.
This is derived from their actual sector equations, never native calibration. -/
theorem pairCopies {n : Nat} (p : Program n) s t
    (hs : (nodes p)[s]? = some ⟨2,HistoryCodec.pair⟩)
    (ht : (nodes p)[t]? = some ⟨2,HistoryCodec.pair⟩)
    {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (HistoryDifference.pairCall s a b) (HistoryDifference.pairCall t a b))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := Formula.equal (HistoryDifference.pairCall s a b) (HistoryDifference.pairCall t a b)
  obtain ⟨hsl⟩ := HistoryOrder.PairProof.pairLowerOrder n p s hs ctx a b
  obtain ⟨htl⟩ := HistoryOrder.PairProof.pairLowerOrder n p t ht ctx a b
  obtain ⟨hsu⟩ := HistoryOrder.PairProof.pairUpperOrder n p s hs ctx a b
  obtain ⟨htu⟩ := HistoryOrder.PairProof.pairUpperOrder n p t ht ctx a b
  obtain ⟨hsplit⟩ := HistoryOrder.SplitProof.additiveSplit T ctx a b
  have hl : Derivation T (.imp (HistoryOrder.lower a b) Q) := by
    have h : Hilbert.Local T ctx [HistoryOrder.lower a b] (HistoryOrder.lower a b) := .hypothesis List.mem_cons_self
    have h1 := Hilbert.Local.mp (.base hsl) h
    have h2 := Hilbert.Local.mp (.base htl) h
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (localTrans _ _ _ h1 (HistoryOrder.StepProof.localSym _ _ h2)))
  have hu : Derivation T (.imp (HistoryOrder.upper a b) Q) := by
    have h : Hilbert.Local T ctx [HistoryOrder.upper a b] (HistoryOrder.upper a b) := .hypothesis List.mem_cons_self
    have h1 := Hilbert.Local.mp (.base hsu) h
    have h2 := Hilbert.Local.mp (.base htu) h
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (localTrans _ _ _ h1 (HistoryOrder.StepProof.localSym _ _ h2)))
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hl) hu) hsplit⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.PairCongruenceProof
