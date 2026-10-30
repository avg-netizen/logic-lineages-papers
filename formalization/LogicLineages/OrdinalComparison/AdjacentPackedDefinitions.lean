module
public import LogicLineages.OrdinalComparison.ProfileDominatorDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Paper07 (6.1), on faithful finite syntax. No semantic kernel is evaluated. -/
def profileAdjacentThreshold (L : NONote) (E : FixedLimitPositiveExpr) : Nat :=
  max 4 (max (profileReserveBlocks (profileBoundWord E) + 5)
    (max (fixedLimitProfileThreshold E)
      (max (Vendor.R1.treeWeight L.1) (profileReserveLeadingBound (profileBoundWord E)))))

end LogicLineages.OrdinalComparison
