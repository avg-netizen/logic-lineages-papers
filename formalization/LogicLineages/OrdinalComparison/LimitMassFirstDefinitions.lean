module
public import LogicLineages.OrdinalComparison.ProfileDominatorDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Literal effective threshold (6.5) for the source limit-exponent mass case. -/
def profileLimitMassThreshold (L : NONote) (E : FixedLimitPositiveExpr) : Nat :=
  max 4 (max (profileReserveBlocks (profileBoundWord E)+4)
    (max (fixedLimitProfileThreshold E)
      (max (Vendor.R1.treeWeight L.1+1) (profileReserveLeadingBound (profileBoundWord E)))))

end LogicLineages.OrdinalComparison
