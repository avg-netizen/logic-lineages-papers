module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineTargets
open UniformCertificateCompletion OriginalSpineGuardLeaf OriginalSelectedStepSpine
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Closed compositional transport through the original selected checker.
Its internal leaf supplier is explicit, so this generic theorem alone is not
an unconditional source bridge. The concrete specializations below must
discharge that supplier from their literal conjunctions. -/
def ActualOriginalSelectedStepSpineTransport : Prop :=
  ∀ (endpoint : Program 6) (oldStep : Program 4),
  LeafHasSpineGuard oldStep → SelectedHasSpineGuard endpoint oldStep

/-- The concrete refined leaf pays the supplier internally. Endpoint and
old leaf are arbitrary original Programs; no native calibration, window,
typed-child premise, leaf progress assumption or extra witness is supplied. -/
def ActualOriginalRefinedSelectedStepSpineGuard : Prop :=
  ∀ (endpoint : Program 6) (oldStep : Program 4),
  SelectedHasSpineGuard endpoint (OriginalSpineGuardLeaf.refined oldStep)

/-- Refine the original leaf once, then use the UNCHANGED existing finalInputs
pipeline. Its constructor/neutral conjunctions retain that leaf as a factor.
Full UCC.stepAccepted at the SAME final tuple implies the literal spine guard
at the same raw endpoints, original certificate and separate parameter.
No source/Object certificate, full-fold mark law or complete Package selection
is claimed by this raw-step supporting contract. -/
def ActualOriginalFinalRawStepSpineGuard : Prop :=
  ∀ p : GlobalSourcePackage.Inputs,
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  RawStepHasSpineGuard (OuterSelection.data r.base r.window) r.oldStep

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineTargets
