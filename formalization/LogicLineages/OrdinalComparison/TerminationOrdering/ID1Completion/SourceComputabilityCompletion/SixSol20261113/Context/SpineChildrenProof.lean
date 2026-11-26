module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineChildrenTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportUnaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineChildrenProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedDecoderTransportLogicalProof (iffForward)
open OriginalTransparentDecoderValidatorCollapsePackedProof

theorem actualOrdinary : SpineChildrenTargets.ActualOrdinary := by
  intro H G M W body alpha Delta packed parameter typ raw c gamma head base headData result types hs hp hparam hc hh ht
  have hsource := sourceFieldsElim H G M W packed parameter typ raw c gamma hp hparam hs
  have hf := iffForward (OriginalUniverseDecoderTransportUnaryAcceptanceProof.ordinaryIff H M W
    raw head base headData result types typ gamma c hc hh ht) (andRight hsource)
  exact andIntro (andLeft hsource) (andRight (andRight (andRight (andRight hf))))

theorem actualNumbered : SpineChildrenTargets.ActualNumbered := by
  intro H G M W body alpha Delta packed parameter typ raw c gamma label head recorded base extraTypes extras headData headResult baseTypes hs hp hparam hc hh ht
  have hsource := sourceFieldsElim H G M W packed parameter typ raw c gamma hp hparam hs
  have hf := iffForward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.numberedIff H M W
    raw label head recorded base extraTypes extras headData headResult baseTypes typ gamma c hc hh ht) (andRight hsource)
  exact andIntro (andLeft hsource) (andRight (andRight (andRight (andRight hf))))

theorem actualCons : SpineChildrenTargets.ActualCons := by
  intro H G M W body alpha Delta raw types domain head tail requestedDomain tailTypes packed parameter gamma c ha hg hc ht hp hparam
  have hf := iffForward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.consIff H M W
    raw domain head tail types requestedDomain tailTypes gamma c hc ht) ha
  have hchildren := andRight (andRight hf)
  exact andIntro
    (sourceFieldsIntro H G M W packed parameter domain head c gamma hp hparam hg (andLeft hchildren))
    (andRight hchildren)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineChildrenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineChildrenProof
