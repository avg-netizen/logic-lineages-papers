module
public import LogicLineages.StandardControlCurrent.HyperCloseBlockDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.DominantBoundaryDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.InverseBoundaryBlock
open OrdinalComparison LayeredComparison.SnyatkovCompletion
open NonlinearProjectionCompletion

def branch (xs : List Nat) (i a : Nat) (shift : Int) (lower upper : Term) (p : Matrix) :
    List Nat × Matrix :=
  (xs.erase i,DominantBoundary.project i a shift lower upper p)
abbrev Input := List Nat × DominantBoundary.Code.Input
def program (q : Input) : List Nat × Nat :=
  (q.1.erase q.2.1,DominantBoundary.Code.project q.2)
end LogicLineages.StandardControlCurrent.InverseBoundaryBlock
