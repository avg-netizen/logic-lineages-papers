module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportTargets
open UniformCertificateCompletion
open OriginalTransparentDecoderValidatorCollapse OriginalTransparentDecoderFinalTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Target validity at the SAME unchanged finalData r, before and after shift. -/
def ActualOriginalTransparentDecoderFinalTargetWeakening : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    PackedWeakening (InternalOriginalUniformDescentSelection.targetValidity (selected p H G W))

/-- Target validity under original packed erasure; no selectedTyped premise. -/
def ActualOriginalTransparentDecoderFinalTargetErasure : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    PackedErasure (InternalOriginalUniformDescentSelection.targetValidity (selected p H G W))

/-- Source validity at that identical final tuple, retaining its actual source
checker and arbitrary outer context. -/
def ActualOriginalTransparentDecoderFinalSourceWeakening : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    PackedWeakening (InternalOriginalUniformDescentSelection.validity (selected p H G W))

/-- The original source validator itself pays the erased variable's type.
No erased-type window or Gamma-in-window premise is added. -/
def ActualOriginalTransparentDecoderFinalSourceErasure : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    PackedErasure (InternalOriginalUniformDescentSelection.validity (selected p H G W))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportTargets
