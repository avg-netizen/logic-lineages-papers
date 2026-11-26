module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder.StatementChecks

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryBounds
open GorbowSyntax SixSol20261112.Fuel

/-- Internal additive witness for child ≤ code. -/
def weakBound {ctx : Nat} (child code : Term ctx) : Formula ctx :=
  .ex (.equal (liftTerm code) (.add (liftTerm child) (.var 0)))

/-- Internal strictly positive gap, the bound needed for numeric-code descent. -/
def strictBound {ctx : Nat} (child code : Term ctx) : Formula ctx :=
  .ex (.equal (liftTerm code) (.add (liftTerm child) (.succ (.var 0))))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryBounds
