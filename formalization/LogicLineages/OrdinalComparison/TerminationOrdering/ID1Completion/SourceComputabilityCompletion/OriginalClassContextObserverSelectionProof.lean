module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverSelectionOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimumGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverSelectionProof
open UniformCertificateCompletion OriginalClassContextObserverSelection
open OriginalClassContextObserverSelectionTargets OriginalClassContextObserverSelectionOutputProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalClassContextObserverRetention : ActualOriginalClassContextObserverRetention := by
  intro n arity p H G W P hp hH hG hW hP
  have hkernel := OriginalActiveClassKernelCalibrationProof.actualOriginalActiveClassKernelCalibration
    n arity p H G W P hp hH hG hW hP
  have hobs := OriginalClassContextObserverCalibrationProof.actualOriginalClassContextObserverCalibration
    n arity p H G W (OriginalActiveClassKernel.classTest p H G W P) hp hH hG hW hkernel
  have hretain := OriginalActiveObservedMinimumGlobalProof.actualOriginalActiveObservedMinimumRetention
    n arity p H G W (classTest p H G W P) hp hH hG hW hobs
  exact ⟨hP,hretain,actualOriginalClassContextObserverOutput p H G W P⟩

theorem actualOriginalClassContextObserverSelection : ActualOriginalClassContextObserverSelection := by
  intro n arity
  obtain ⟨p,H,G,W,hprevious⟩ :=
    OriginalRankGuardedRepresentativeGlobalProof.actualOriginalRankGuardedRepresentativeSelection n arity
  obtain ⟨P,hP⟩ :=
    OriginalTransparentMinimumClassSelectionProof.actualOriginalTransparentMinimumClassSelection n arity
  exact ⟨p,H,G,W,P,actualOriginalClassContextObserverRetention n arity p H G W P
    hprevious.1.1 hprevious.1.2.1 hprevious.1.2.2.1 hprevious.1.2.2.2.1 hP⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverSelectionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverSelectionProof
