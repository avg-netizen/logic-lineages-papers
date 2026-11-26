module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.EncodedMetadataFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentMetadataFields.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.EncodedMetadataFields.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem internalHeadFactor : Targets.InternalHeadFactor := by
  intro body alpha Delta V target node code param rawHead encodedHead hraw
  exact ⟨fun h => unaryRecover OriginalHeadEncodingBridge.encodeHead (TransparentMetadataFields.head V target)
    encodedHead rawHead ![node,code,param] h hraw,
    fun h => unaryValue OriginalHeadEncodingBridge.encodeHead (TransparentMetadataFields.head V target)
      encodedHead rawHead ![node,code,param] h hraw⟩

theorem internalNumbered : Targets.InternalNumbered := by
  intro body alpha Delta V target node code param raw rank rawHead encodedHead tau base ts extras hV hq hc he
  obtain ⟨ha,hh,hl,ht⟩ := TransparentMetadataFields.InternalProof.internalNumbered body alpha Delta V target
    node code param raw rank rawHead tau base ts extras hV hq hc
  exact ⟨ha,(internalHeadFactor body alpha Delta V target node code param rawHead encodedHead hh).mpr he,hl,ht⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.EncodedMetadataFields.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.EncodedMetadataFields.InternalProof
