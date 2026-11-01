module
public import LogicLineages.OrdinalComparison.SourceKernelCallsDefinitions
public import LogicLineages.OrdinalComparison.SourceSignatureBudgetDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Fixed INITIAL carrier budget. Actual head and kernel bounds are tracked
pointwise; no child conservative syntax-budget monotonicity is asserted. -/
def comparisonSourceBounded (budget : Nat) (E : OneVariableComparisonExpr) : Prop :=
  (∀ rho∈comparisonOriginalSourceHeads E,Vendor.R1.treeWeight rho.1≤budget) ∧
  (∀ p∈comparisonAuxiliarySourceWord E,Vendor.R1.treeWeight p.1.1≤budget)

end LogicLineages.OrdinalComparison
