module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateTargets
open UniformCertificateCompletion OriginalVariableErasureCertificate
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Actual SAME-source variable certificates collapse under the literal
original Object erasure, with strict original endpoint rank decrease 1 to 0.
The existing final tuple is arbitrary; no native calibration is a premise. -/
def ActualOriginalVariableErasureCertificateCollapse : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    RawCollapseLaw p H G W

/-- The collapse survives the SAME unchanged final canonical Object program
on both erased endpoints, retaining the original strict rank conclusion. -/
def ActualOriginalVariableErasureCertificateCanonicalCollapse : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    CanonicalCollapseLaw p H G W

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateTargets
