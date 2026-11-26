module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.StatementChecks

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoderBounds
open GorbowSyntax GorbowPRDefiningEquations List.Vector

/-- Genuine internal additive gap bound for the existing literal decoder. -/
def outputBound {ctx : Nat} (tag : Nat) (input : Term ctx) : Formula ctx :=
  HistoryBounds.weakBound (call tag (input ::ᵥ nil)) input

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoderBounds
