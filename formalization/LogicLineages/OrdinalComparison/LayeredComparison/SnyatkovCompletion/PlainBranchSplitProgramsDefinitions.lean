module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitPrograms.Code

def small (code : Nat) : Nat :=
  BoundedRows.Code.block ((MaximalPlainBranchPrograms.Code.variables code).map
    (fun i => (i, MaximalPlainBranchPrograms.Code.cutoff code))) code
def smallAnswer (code : Nat) : Bool := ZeroValuation.Code.evaluate (small code)
def branches (code : Nat) : List Nat :=
  (MaximalPlainBranchPrograms.Code.variables code).map
    (fun i => MaximalPlainBranchPrograms.Code.eliminate i code)
def step (code : Nat) : Bool × List Nat :=
  let q := PlainLinearCleanup.Code.cleanup code
  (smallAnswer q, branches q)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitPrograms.Code
