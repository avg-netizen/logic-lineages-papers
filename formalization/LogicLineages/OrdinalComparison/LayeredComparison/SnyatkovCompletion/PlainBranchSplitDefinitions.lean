module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainLinearCleanupDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplit
open NormalForm

def small (p : Formula) : Formula :=
  BoundedRows.block (p.variables.map (fun i => (i, MaximalPlainBranch.cutoff p))) p
def smallAnswer (p : Formula) : Bool := ZeroValuation.evaluate (small p)
def branches (p : Formula) : List Formula :=
  p.variables.map (fun i => MaximalPlainBranch.eliminate i p)
/-- Only a finite answer and actual successor formulas are computed. -/
def step (p : Formula) : Bool × List Formula :=
  let q := PlainLinearCleanup.cleanup p
  (smallAnswer q, branches q)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplit
