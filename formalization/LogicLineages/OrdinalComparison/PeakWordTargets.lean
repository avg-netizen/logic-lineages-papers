module
public import LogicLineages.OrdinalComparison.PrincipalWordActionDefinitions
public import LogicLineages.OrdinalComparison.ActualTerminalDefinitions
public import LogicLineages.OrdinalComparison.ActualCollapseDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Full paper07 lem:peakword (409–425), on the faithful closed normal notation
input. The extracted word is executable; its actual ordinal action is semantic,
not an assertion of an unproved executable kernel evaluator. -/
def FullActualPrincipalPeakWord : Prop :=
  ∀ o : NONote, Order.IsSuccLimit o.1.repr → ∀ n : Nat,
    let word := principalKernelWord (principalExponentBlocks o.1) 0
    let t := Vendor.R1.treeWeight o.1 + n
    let initial := o.1.repr + (n : Ordinal)
    word ≠ [] ∧
    actualPrincipalWordRun word t = (actualTerminalValue initial, actualReplacementCount initial) ∧
    actualPrincipalWordGenuine word t ∧
    0 < (actualPrincipalWordRun word t).2 ∧
    actualCollapse initial = (actualPrincipalWordRun word t).1 + (actualPrincipalWordRun word t).2

end LogicLineages.OrdinalComparison.Targets
