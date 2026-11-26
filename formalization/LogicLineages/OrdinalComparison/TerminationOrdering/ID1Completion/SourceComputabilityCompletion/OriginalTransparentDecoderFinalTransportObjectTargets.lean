module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportObjectDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportObjectTargets
open UniformCertificateCompletion OriginalTransparentDecoderValidatorCollapse
open OriginalTransparentDecoderFinalTransportObject
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- SAME-final target validity under actual raw Object weakening.
This is a validator law, not selectedTyped or canonical Object transport. -/
def ActualOriginalTransparentDecoderFinalTargetObjectWeakening : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    ObjectWeakening (InternalOriginalUniformDescentSelection.targetValidity (selected p H G W))

/-- SAME-final target validity under actual raw Object erasure.
This is a validator law, not selectedTyped or canonical Object transport. -/
def ActualOriginalTransparentDecoderFinalTargetObjectErasure : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    ObjectErasure (InternalOriginalUniformDescentSelection.targetValidity (selected p H G W))

/-- SAME-final source validity under actual raw Object weakening.
This is a validator law, not selectedTyped or canonical Object transport. -/
def ActualOriginalTransparentDecoderFinalSourceObjectWeakening : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    ObjectWeakening (InternalOriginalUniformDescentSelection.validity (selected p H G W))

/-- SAME-final source validity under actual raw Object erasure.
This is a validator law, not selectedTyped or canonical Object transport. -/
def ActualOriginalTransparentDecoderFinalSourceObjectErasure : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    ObjectErasure (InternalOriginalUniformDescentSelection.validity (selected p H G W))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportObjectTargets
