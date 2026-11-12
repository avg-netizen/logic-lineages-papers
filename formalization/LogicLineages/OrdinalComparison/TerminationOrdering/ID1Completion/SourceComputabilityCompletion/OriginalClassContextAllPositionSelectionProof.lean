module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionSelectionOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionNativeCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimumGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionSelectionProof
open UniformCertificateCompletion OriginalClassContextAllPositionSelection
open OriginalClassContextAllPositionSelectionTargets OriginalClassContextAllPositionSelectionOutputProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualRetention : ActualRetention := by
  intro n arity p H G W P hp hH hG hW hP
  have hkernel := OriginalActiveClassKernelCalibrationProof.actualOriginalActiveClassKernelCalibration
    n arity p H G W P hp hH hG hW hP
  have hobs := OriginalClassContextAllPositionNativeCalibrationProof.calibration
    n arity p H G W (OriginalActiveClassKernel.classTest p H G W P) hp hH hG hW hkernel
  have hretain := OriginalActiveObservedMinimumGlobalProof.actualOriginalActiveObservedMinimumRetention
    n arity p H G W (classTest p H G W P) hp hH hG hW hobs
  exact ⟨hP,hretain,actualOutput p H G W P⟩

theorem actualSelection : ActualSelection := by
  intro n arity
  obtain ⟨p,H,G,W,hprevious⟩ :=
    OriginalRankGuardedRepresentativeGlobalProof.actualOriginalRankGuardedRepresentativeSelection n arity
  obtain ⟨P,hP⟩ :=
    OriginalTransparentMinimumClassSelectionProof.actualOriginalTransparentMinimumClassSelection n arity
  exact ⟨p,H,G,W,P,actualRetention n arity p H G W P
    hprevious.1.1 hprevious.1.2.1 hprevious.1.2.2.1 hprevious.1.2.2.2.1 hP⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionSelectionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionSelectionProof
