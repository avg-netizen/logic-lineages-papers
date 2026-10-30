module
public import LogicLineages.OrdinalComparison.CollectedPeakDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Literal source nonlinear-root threshold, computed only from finite syntax. -/
def collectedNonlinearThreshold (rho : NONote) (c b : Nat) (tags : CollectedPositiveTags) : Nat :=
  max 4 (max (Vendor.R1.treeWeight rho.1+c+b) (2*collectedCoefficientSum tags+1))

end LogicLineages.OrdinalComparison
