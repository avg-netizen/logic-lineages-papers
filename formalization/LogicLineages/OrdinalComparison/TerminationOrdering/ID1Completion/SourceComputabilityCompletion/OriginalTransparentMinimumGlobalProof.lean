module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumClassSelectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumGuardedClassProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalScanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumGlobalProof
open UniformCertificateCompletion OriginalTransparentMinimum
open OriginalTransparentMinimumNativeProof OriginalTransparentMinimumClassSelectionProof
open OriginalTransparentMinimumInternalReflexiveProof OriginalTransparentMinimumInternalMinimumProof
open OriginalTransparentMinimumGuardedClassProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Retain the original selected tuple and select only its class-test compiler.
All internal consumers still require the independent universal scan theorem. -/
theorem selectionOfScan (hscan : ∀ Q : Program 3, ScanLaw Q) :
    OriginalTransparentMinimumTargets.ActualOriginalTransparentMinimumSelection := by
  intro n arity
  obtain ⟨p,H,G,W,hprevious⟩ :=
    OriginalRankGuardedRepresentativeGlobalProof.actualOriginalRankGuardedRepresentativeSelection n arity
  obtain ⟨P,hP⟩ := actualOriginalTransparentMinimumClassSelection n arity
  have hp := hprevious.1.1
  have hH := hprevious.1.2.1
  have hG := hprevious.1.2.2.1
  have hW := hprevious.1.2.2.2.1
  have hminimum := minimumOfScan (OriginalTypedDecoder.target H G) P (hscan _)
  exact ⟨p,H,G,W,P,hprevious,hP,
    actualOriginalTransparentMinimumLiteralFields p H G W P,
    actualOriginalTransparentMinimumNativePreparation n arity p H G P hp hH hG hP,
    actualOriginalTransparentMinimumInternalReflexive (OriginalTypedDecoder.target H G) P,
    hscan _,hminimum,guardedClassOfMinimum p H G W P hminimum,
    actualOriginalTransparentMinimumRetention n arity p H G W P hp hH hG hW hP⟩


theorem actualOriginalTransparentMinimumInternalMinimum :
    OriginalTransparentMinimumTargets.ActualOriginalTransparentMinimumInternalMinimum := by
  intro T P
  exact minimumOfScan T P
    (OriginalTransparentMinimumInternalScanProof.actualOriginalTransparentMinimumInternalScan _)

theorem actualOriginalTransparentMinimumInternalGuardedClass :
    OriginalTransparentMinimumTargets.ActualOriginalTransparentMinimumInternalGuardedClass := by
  intro p H G W P
  exact guardedClassOfMinimum p H G W P
    (actualOriginalTransparentMinimumInternalMinimum (OriginalTypedDecoder.target H G) P)

theorem actualOriginalTransparentMinimumSelection :
    OriginalTransparentMinimumTargets.ActualOriginalTransparentMinimumSelection :=
  selectionOfScan OriginalTransparentMinimumInternalScanProof.actualOriginalTransparentMinimumInternalScan

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumGlobalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumGlobalProof
