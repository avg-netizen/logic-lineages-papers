module
public import LogicLineages.OrdinalComparison.CollectedPeakDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Source affine-band threshold with the actual faithful notation norm.
No value or peak evaluation is used to compute this threshold. -/
def collectedAffineThreshold (rho : NONote) (c b : Nat) : Nat :=
  max 4 (Vendor.R1.treeWeight rho.1+c+b+1)

end LogicLineages.OrdinalComparison
