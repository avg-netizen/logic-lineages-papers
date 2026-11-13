module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryBounds.StatementChecks

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation
open GorbowSyntax

/-- Cancellation as an internal implication, not metatheoretic numeral equality. -/
def cancelRight {ctx : Nat} (a b c : Term ctx) : Formula ctx :=
  .imp (.equal (.add a c) (.add b c)) (.equal a b)
def cancelLeft {ctx : Nat} (a b c : Term ctx) : Formula ctx :=
  .imp (.equal (.add c a) (.add c b)) (.equal a b)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation
