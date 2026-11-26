module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.LengthBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.LengthValueProof
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

theorem nilLength (H : Program 1) (types raw gamma param entries entryLength typeLength payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 6) payload)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph entryLength entries)))
    (ht : Nonempty (Derivation body Delta (lengthGraph typeLength types))) :
    Nonempty (Derivation body Delta (eqn entryLength typeLength)) := by
  have hi := SupportProof.nilIdentities H types raw gamma param entries payload hp ha hv
  have hl0 := headTransport OriginalContextInsertion.length entryLength entries z Fin.elim0 (andRight hi) hl
  have ht0 := headTransport OriginalContextInsertion.length typeLength types z Fin.elim0 (andLeft hi) ht
  obtain ⟨hel⟩ := OriginalContextInsertionLengthProof.lengthNilRecover entryLength hl0
  obtain ⟨het⟩ := OriginalContextInsertionLengthProof.lengthNilRecover typeLength ht0
  exact ⟨trans hel (symm het)⟩

theorem consAtValues (H : Program 1)
    (types raw gamma param entries entryLength typeLength tau head tail requested tailTypes
      tailEntries entry listCode tailEntryLength tailTypeLength : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph entryLength entries)))
    (ht : Nonempty (Derivation body Delta (lengthGraph typeLength types)))
    (ih : Nonempty (Derivation body Delta (LengthInductionDefinitions.BelowRaw H raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail param)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau head)))
    (hlist : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode entry tailEntries)))
    (hle : Nonempty (Derivation body Delta (lengthGraph tailEntryLength tailEntries)))
    (hlt : Nonempty (Derivation body Delta (lengthGraph tailTypeLength tailTypes))) :
    Nonempty (Derivation body Delta (eqn entryLength typeLength)) := by
  obtain ⟨htypes,_,_,hacc⟩ := SupportProof.consAccepted H types raw gamma tau head tail requested tailTypes hc hf ha
  have hentries := SupportProof.consEntries raw param entries tau head tail tailEntries entry listCode hc hv he hp hlist
  obtain ⟨hsmall⟩ := LengthBindingProof.belowRawApply H raw tail tailTypes gamma param tailEntries tailEntryLength tailTypeLength ih
    (CrossRootCacheCoherence.SupportProof.consTailStrict raw tau head tail hc)
    (andIntro (andIntro (andIntro hacc he) hle) hlt)
  obtain ⟨heq⟩ := OriginalContextInsertionLengthProof.lengthConsRecover entries entry tailEntries entryLength tailEntryLength hentries hl hle
  obtain ⟨htq⟩ := OriginalContextInsertionLengthProof.lengthConsRecover types requested tailTypes typeLength tailTypeLength htypes ht hlt
  exact ⟨trans heq (trans (congSuc hsmall) (symm htq))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.LengthValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.LengthValueProof
