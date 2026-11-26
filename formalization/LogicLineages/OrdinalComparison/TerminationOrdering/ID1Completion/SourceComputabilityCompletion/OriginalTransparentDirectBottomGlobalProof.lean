module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobalInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobalProof
open UniformCertificateCompletion OriginalTransparentDirectBottomGlobal
open OriginalTransparentDirectBottomGlobalTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Source transparency and both step refinements are calibrated before
retaining the existing package. Native equality never supplies an internal rule. -/
theorem actualOriginalDirectBottomGlobalRetention : ActualOriginalDirectBottomGlobalRetention := by
  intro n arity p H G W P hp hH hG hW hP
  have hc := OriginalTransparentDecoderSelectionCalibrationProof.actualOriginalTransparentDecoderCalibration
    n arity p H G W hp hH hG hW
  have hb := OriginalTransparentDirectBottomCalibrationProof.actualOriginalDirectBottomCalibration
    n arity (concreteInputs p H G W) hc.1
  have hl := OriginalTransparentLambdaStepGlobalProof.actualOriginalTransparentLambdaStepGlobalRetention
    n arity (initial p H G W) H G W P hb hH hG hW hP
  have hf : GlobalSourcePackage.InputsCalibrated n arity (finalInputs p H G W P) := hl.1.2.2.1
  have hn : NativePreparation n arity p H G W P := by
    refine ⟨hc.1,hb,hf,?_⟩
    intro v
    exact ⟨(hb.2.2.2.2.1 v).trans (hp.2.2.2.2.1 v).symm,
      (hf.2.2.2.2.1 v).trans (hp.2.2.2.2.1 v).symm⟩
  exact ⟨hc,hn,hl,
    OriginalTransparentDirectBottomGlobalInternalProof.actualOriginalDirectBottomGlobalIntroduction p H G W P⟩

theorem actualOriginalDirectBottomGlobalSelection : ActualOriginalDirectBottomGlobalSelection := by
  intro n arity
  obtain ⟨p,H,G,W,hprevious⟩ :=
    OriginalRankGuardedRepresentativeGlobalProof.actualOriginalRankGuardedRepresentativeSelection n arity
  obtain ⟨P,hP⟩ := OriginalTransparentMinimumClassSelectionProof.actualOriginalTransparentMinimumClassSelection n arity
  exact ⟨p,H,G,W,P,actualOriginalDirectBottomGlobalRetention n arity p H G W P
    hprevious.1.1 hprevious.1.2.1 hprevious.1.2.2.1 hprevious.1.2.2.2.1 hP⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobalProof
