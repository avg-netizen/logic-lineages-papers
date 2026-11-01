module
public import LogicLineages.OrdinalComparison.SourceCarrierClosureProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceCarrierClosure.StatementChecks

theorem fixed_containment : Targets.DisplayedRawArgumentHeadContainment := containment
theorem fixed_initial : Targets.ActualInitialPairBounds := initial
theorem fixed_peak : Targets.ActualPeakChildBounds := peak
theorem fixed_stripped : Targets.ActualStrippedChildBounds := stripped
theorem fixed_normalized : Targets.ActualNormalizedSourceBounds := normalized
theorem fixed_full : Targets.FullActualFixedSourceCarrierClosure := full

end LogicLineages.OrdinalComparison.SourceCarrierClosure.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.SourceCarrierClosure
