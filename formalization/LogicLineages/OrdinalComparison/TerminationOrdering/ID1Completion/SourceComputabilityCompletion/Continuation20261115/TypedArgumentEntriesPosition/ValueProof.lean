module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.BindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.ValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalRecursionGraphStepSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open OriginalTypedDecoderInternalAcceptance
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalAcceptanceSyntaxProof
open OriginalTypedDecoderTransportLogicalProof (iffForward)
open OriginalTypedDecoderInternalScalarSyntaxProof (stepArrowFieldsRename)

open OriginalContextInsertion (lengthGraph)

open OriginalContextInsertion (Below)
open InternalSquareRootArithmeticSupportProof (orderLeft orderRight)
open InternalOriginalOrderSyntaxProof (orderRename)
theorem nilPosition (H : Program 1) (types raw gamma param entries count index entry annotation child expected payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 6) payload)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph count types)))
    (hb : Nonempty (Derivation body Delta (Below index count))) :
    Nonempty (Derivation body Delta (eqn annotation expected ⊓ TermAccepted H expected child gamma)) := by
  have hi := TypedArgumentEntriesContent.SupportProof.nilIdentities H types raw gamma param entries payload hp ha hv
  have hl0 := headTransport OriginalContextInsertion.length count types z Fin.elim0 (andLeft hi) hl
  obtain ⟨hz⟩ := OriginalContextInsertionLengthProof.lengthNilRecover count hl0
  obtain ⟨hb⟩ := hb
  obtain ⟨hn⟩ := InternalLeastNumberProof.actualNothingBelowZero body alpha index
  exact ⟨Derivation.explosion (Derivation.implicationElimination
    (InternalPositiveUnfoldingSupportProof.weakenClosed hn Delta) (orderRight index hz hb))⟩

theorem headPosition (H : Program 1) (gamma entry annotation child expected headEntry headAnnotation head requested : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn entry headEntry)))
    (ht : Nonempty (Derivation body Delta (eqn expected requested)))
    (hr : Nonempty (Derivation body Delta (eqn requested headAnnotation)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing headEntry headAnnotation head)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry annotation child)))
    (ha : Nonempty (Derivation body Delta (TermAccepted H headAnnotation head gamma))) :
    Nonempty (Derivation body Delta (eqn annotation expected ⊓ TermAccepted H expected child gamma)) := by
  obtain ⟨he⟩ := he
  have htyped := TypedArgumentEntriesContent.EntryValueProof.acceptedHeadEntry H gamma headEntry entry headAnnotation head annotation child ⟨symm he⟩ hp hq ha
  have hq' := outputTransport InternalPairing.pairing entry headEntry ![annotation,child] ⟨he⟩ hq
  obtain ⟨hann⟩ := valueUnique InternalUnpair.left annotation headAnnotation (Fin.cons headEntry Fin.elim0)
    (pairLeft headEntry annotation child hq') (pairLeft headEntry headAnnotation head hp)
  obtain ⟨ht⟩ := ht
  obtain ⟨hr⟩ := hr
  have heq := trans hann (trans (symm hr) (symm ht))
  exact andIntro ⟨heq⟩ (headTransport (OriginalTypedDecoder.termCheck H) (numeral 1) annotation expected
    (Fin.cons child (Fin.cons gamma Fin.elim0)) ⟨heq⟩ htyped)

theorem successorPosition (H : Program 1)
    (types raw gamma param entries count index entry annotation child expected headAnnotation head tail requested tailTypes
      tailEntries headEntry tailCount pred : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw headAnnotation head tail)))
    (htypes : Nonempty (Derivation body Delta (StepCons types requested tailTypes)))
    (hentries : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode entries headEntry tailEntries)))
    (hacc : Nonempty (Derivation body Delta (ArgumentsAccepted H tailTypes tail gamma)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph count types)))
    (hb : Nonempty (Derivation body Delta (Below index count)))
    (hlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup entry index entries)))
    (htlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup expected index types)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry annotation child)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw)))
    (hlen : Nonempty (Derivation body Delta (lengthGraph tailCount tailTypes)))
    (hindex : Nonempty (Derivation body Delta (eqn index (suc pred)))) :
    Nonempty (Derivation body Delta (eqn annotation expected ⊓ TermAccepted H expected child gamma)) := by
  obtain ⟨hlenEq⟩ := OriginalContextInsertionLengthProof.lengthConsRecover types requested tailTypes count tailCount htypes hl hlen
  obtain ⟨hi⟩ := hindex
  obtain ⟨hb⟩ := hb
  have hbTail := OriginalContextInsertionBelowCoreProof.successorStrict pred tailCount
    ⟨orderRight (suc pred) hlenEq (orderLeft count hi hb)⟩
  have hel := headTransport InternalRawListRecursion.lookup entry index (suc pred) (Fin.cons entries Fin.elim0) ⟨hi⟩ hlook
  have htl := headTransport InternalRawListRecursion.lookup expected index (suc pred) (Fin.cons types Fin.elim0) ⟨hi⟩ htlook
  have helTail := iffForward (OriginalAllPositionContextDeleteDropProof.lookupConsIff entries headEntry tailEntries pred entry hentries) hel
  have htlTail := iffForward (OriginalAllPositionContextDeleteDropProof.lookupConsIff types requested tailTypes pred expected htypes) htl
  exact BindingProof.belowRawApply H raw tail tailTypes gamma param tailEntries tailCount pred entry annotation child expected ih
    (CrossRootCacheCoherence.SupportProof.consTailStrict raw headAnnotation head tail hc)
    (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro hacc he) hlen) hbTail) helTail) htlTail) hq)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.ValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.ValueProof
