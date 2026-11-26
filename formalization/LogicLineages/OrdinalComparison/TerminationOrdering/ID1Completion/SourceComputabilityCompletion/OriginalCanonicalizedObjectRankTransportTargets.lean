module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectRankTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectRankTransportTargets
open UniformCertificateCompletion OriginalCanonicalizedObjectRankTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Original Object weakening and actual SAME-final canonicalization preserve
rank internally, with only the original active-window/input-typing premises. -/
def ActualOriginalCanonicalizedObjectWeakeningRank : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    WeakeningRankLaw p H G W

/-- Genuine contextual erasure and actual SAME-final canonicalization do not
increase rank. No raw erased canonicality or native calibration is assumed. -/
def ActualOriginalCanonicalizedObjectErasureRank : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    ErasureRankLaw p H G W

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectRankTransportTargets
