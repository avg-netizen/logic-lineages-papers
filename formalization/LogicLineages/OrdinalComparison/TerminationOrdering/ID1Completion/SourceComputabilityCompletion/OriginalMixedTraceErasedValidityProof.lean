module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceErasedValidityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceErasedValidityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeelSupportProof (andIntro)
theorem actualBothErasedSource : OriginalMixedTraceErasedValidityTargets.ActualBothErasedSource := by
 intro H G M W oldStep body alpha Delta s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hs hr hin hop hnp hes het
 obtain ⟨law⟩ := OriginalMixedTraceValidityProof.actualTargetSourceValidity H G M W oldStep body alpha Delta s t cert oldParam
 obtain ⟨prem⟩ := andIntro hs hr
 have ht := (show Nonempty (Derivation body Delta
  (InternalApplicationCertificateConstructors.graph2 (OriginalTransparentMixedDirectBottom.source H G M W)
   (SourceComputabilityFormulaSupportProof.numeral 1) t oldParam)) from
    ⟨Derivation.implicationElimination law prem⟩)
 exact andIntro
  (OriginalPackedSourceErasureProof.actualOriginalPackedSourceErasure body alpha Delta H G M W
   s erasedS d cutoff gamma extended c oldParam newParam hin hes hop hnp hs)
  (OriginalPackedSourceErasureProof.actualOriginalPackedSourceErasure body alpha Delta H G M W
   t erasedT d cutoff gamma extended c oldParam newParam hin het hop hnp ht)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceErasedValidityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceErasedValidityProof
