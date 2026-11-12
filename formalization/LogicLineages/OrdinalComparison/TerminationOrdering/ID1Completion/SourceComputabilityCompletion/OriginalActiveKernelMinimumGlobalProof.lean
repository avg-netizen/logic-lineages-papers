module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumIdempotenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimumGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumGlobalProof
open UniformCertificateCompletion
open OriginalActiveKernelMinimumTargets
open OriginalActiveKernelMinimumCoherenceProof OriginalActiveKernelMinimumIdempotenceProof
open OriginalActiveClassKernelInternalProof OriginalActiveClassKernelCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact all-vector kernel calibration permits the entire accepted
minimum package to be retained at this one concrete implementation. Its
internal coherence and fixed-point laws are proved independently. -/
theorem actualOriginalActiveKernelMinimumRetention :
    ActualOriginalActiveKernelMinimumRetention := by
  intro n arity p H G W P hp hH hG hW hP
  have hkernel := actualOriginalActiveClassKernelCalibration n arity p H G W P
    hp hH hG hW hP
  have hminimum :=
    OriginalActiveObservedMinimumGlobalProof.actualOriginalActiveObservedMinimumRetention
      n arity p H G W (OriginalActiveClassKernel.classTest p H G W P)
      hp hH hG hW hkernel
  exact ⟨hP,hminimum,
    actualOriginalActiveClassKernelCharacterization p H G W
      OriginalRawSyntaxTransport.variableRankPackedRaw P,
    actualOriginalActiveClassKernelHitDomain p H G W
      OriginalRawSyntaxTransport.variableRankPackedRaw P,
    actualOriginalActiveClassKernelRowCoherence p H G W
      OriginalRawSyntaxTransport.variableRankPackedRaw P,
    actualOriginalActiveKernelMinimumCoherence p H G W P,
    actualOriginalActiveKernelMinimumIdempotence p H G W P⟩

/-- Select the original p and class compiler before every runtime window
and Gamma. The new key always refers to that original p, never its own
minimum output or a separately selected final tuple. -/
theorem actualOriginalActiveKernelMinimumSelection :
    ActualOriginalActiveKernelMinimumSelection := by
  intro n arity
  obtain ⟨p,H,G,W,hprevious⟩ :=
    OriginalRankGuardedRepresentativeGlobalProof.actualOriginalRankGuardedRepresentativeSelection
      n arity
  obtain ⟨P,hP⟩ :=
    OriginalTransparentMinimumClassSelectionProof.actualOriginalTransparentMinimumClassSelection
      n arity
  exact ⟨p,H,G,W,P,actualOriginalActiveKernelMinimumRetention n arity p H G W P
    hprevious.1.1 hprevious.1.2.1 hprevious.1.2.2.1 hprevious.1.2.2.2.1 hP⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumGlobalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumGlobalProof
