module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryBounds.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryBounds.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector

/-- Actual syntax-explicit square-shell pair, arbitrary input terms. -/
def PairFirstBound : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩ → ∀ ctx (a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (weakBound a (call tag (a ::ᵥ b ::ᵥ nil))))

def PairSecondBound : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩ → ∀ ctx (a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (weakBound b (call tag (a ::ᵥ b ::ᵥ nil))))

/-- Strict entry-code descent for the EXISTING history-list cons codec,
without assuming decoding, well-formedness or standard-natural calibration. -/
def ConsFirstStrictBound : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,HistoryCodec.cons⟩ → ∀ ctx (a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (strictBound a (call tag (a ::ᵥ b ::ᵥ nil))))

/-- Strict tail-code descent, needed for genuine encoded-history recursion. -/
def ConsSecondStrictBound : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,HistoryCodec.cons⟩ → ∀ ctx (a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (strictBound b (call tag (a ::ᵥ b ::ᵥ nil))))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryBounds.Targets
