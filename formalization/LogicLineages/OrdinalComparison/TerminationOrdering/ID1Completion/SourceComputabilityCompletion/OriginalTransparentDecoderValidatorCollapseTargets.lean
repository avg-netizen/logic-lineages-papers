module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargets
open UniformCertificateCompletion OriginalTransparentDecoderValidatorCollapse
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Independent all-output collapse of the actual local HT at the same r. -/
def ActualOriginalTransparentDecoderTargetCollapse : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    TargetCollapse p H G W

/-- Independent all-output collapse of actual local HS, with source and
 target callbacks coupled. No separate r.oldSource equality is asserted. -/
def ActualOriginalTransparentDecoderSourceCollapse : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    SourceCollapse p H G W

/-- SAME-final target validity, with the original final pipeline unchanged. -/
def ActualOriginalTransparentDecoderFinalTargetCollapse : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    FinalTargetCollapse p H G W

/-- SAME-final source validity, retaining the actual original source Program. -/
def ActualOriginalTransparentDecoderFinalSourceCollapse : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    FinalSourceCollapse p H G W

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargets
