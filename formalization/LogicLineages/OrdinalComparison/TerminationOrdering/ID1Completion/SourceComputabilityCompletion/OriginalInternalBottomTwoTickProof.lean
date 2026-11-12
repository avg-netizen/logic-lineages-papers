module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomVisitProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalEncodedFrameReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalBottomProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalNilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalReturnCombinedControlProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomTwoTickProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalContextInsertionLengthProof (lengthZero)
open InternalApplicationValidityStackAppendListProof (appendZeroValue)
open InternalNumericIterationSupportProof

theorem actualTwoTick : OriginalInternalBottomTwoTickTargets.ActualTwoTick := by
 intro R body alpha Delta raw typ packed c parameter rawJob typed job visitFrame work input counts payload frame returnWork middle root tail value stack output
   hb hpacked hp hr ht hj hv hs hc hpay hf hm htail hvalue hout hw hret hstack hroot
 have hfirst := OriginalInternalBottomVisitProof.visit R raw typ c parameter rawJob typed job visitFrame work input counts payload frame returnWork middle
   hb hp hr ht hj hv hs hc hpay hf hm hw hret
 have hreturned := OriginalHereditaryReturnInternalBottomProof.bottomLaw body alpha Delta packed z z typ raw raw hpacked hb hb
 have hsecond := OriginalEncodedFrameReturnProof.termChildren0 R body alpha Delta
   middle returnWork z frame z payload packed parameter z z z z root raw tail value stack output job counts typed rawJob typ raw
   hm hret hf hpay hj ht hr hc hpacked lengthZero OriginalTypedArgumentObservationsInternalNilProof.reverseZero
   (appendZeroValue z) hroot hreturned htail hvalue hstack hout
 have hcombined := OriginalInternalReturnCombinedControlProof.control R middle returnWork z frame z payload output hm hret hf hsecond
 have hone := repeatSuccValue (OriginalHereditaryCombinedStep.step R) z input middle input
   (repeatZeroValue (OriginalHereditaryCombinedStep.step R) input) hfirst
 exact repeatSuccValue (OriginalHereditaryCombinedStep.step R) (suc z) middle output input hone hcombined
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomTwoTickProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomTwoTickProof
