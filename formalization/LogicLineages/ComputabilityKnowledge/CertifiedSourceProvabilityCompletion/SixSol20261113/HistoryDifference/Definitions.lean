module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.StatementChecks

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference
open GorbowSyntax GorbowPRDefiningEquations List.Vector

def differenceCall {ctx : Nat} (tag : Nat) (a b : Term ctx) : Term ctx :=
  call tag (a ::ᵥ b ::ᵥ nil)

def pairCall {ctx : Nat} (tag : Nat) (a b : Term ctx) : Term ctx :=
  call tag (a ::ᵥ b ::ᵥ nil)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference
