module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof

/-- Exhaustiveness of the two arithmetic sectors, proved in ordinary PA for
arbitrary terms, with no standard-number reflection or comparison oracle. -/
def AdditiveSplit : Prop := ∀ (T : Sentence → Prop) ctx (a b : Term ctx),
  Nonempty (Derivation T (.disj (lower a b) (upper a b)))

/-- The actual codec at arbitrary arguments under an internally quantified gap. -/
def PairLowerOrder : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩ → ∀ ctx (a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (lower a b) (lowerValue tag a b)))

def PairUpperOrder : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩ → ∀ ctx (a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (upper a b) (upperValue tag a b)))

/-- Full symbolic arithmetic graph of the existing square-shell pair Program.
This is NOT injectivity, decoder inversion or list lookup preservation. -/
def PairGraph : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩ → ∀ ctx (a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (pairGraph tag a b))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder.Targets
