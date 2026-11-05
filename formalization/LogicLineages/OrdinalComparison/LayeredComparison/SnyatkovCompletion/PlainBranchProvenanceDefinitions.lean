module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearBlockDefinitions
public import Mathlib.Data.Finset.Card

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchProvenance
open NormalForm

def nonlinear : Summand → Bool
  | .variable _ => false
  | .phi _ _ | .hyperPhi _ _ _ => true
def plain : Summand → Bool
  | .variable _ | .phi _ _ => true
  | .hyperPhi _ _ _ => false
/-- Membership records unchanged summand values, not multiplicities or order. -/
def nonlinearOccurrences (p : Formula) : List Summand :=
  (LinearBlock.occurrences p).filter nonlinear
def nonlinearNames (p : Formula) : Finset Nat :=
  ((nonlinearOccurrences p).map Summand.name).toFinset

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchProvenance
