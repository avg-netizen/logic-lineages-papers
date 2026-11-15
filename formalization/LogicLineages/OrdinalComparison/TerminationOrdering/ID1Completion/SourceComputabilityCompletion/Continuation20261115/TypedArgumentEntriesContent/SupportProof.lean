module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.SupportProof
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

theorem nilIdentities (H : Program 1) (types raw gamma param entries payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 6) payload)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param))) :
    Nonempty (Derivation body Delta (eqn types z ⊓ eqn entries z)) := by
  have hn := iffForward (OriginalTypedDecoderInternalAcceptanceLeafProof.nilIff H raw payload types gamma hp) ha
  have hz := andLeft hn
  have ht := andRight hn
  rw [equalEqn] at hz ht
  have hc := TypedArgumentEntriesDefined.SupportProof.nilPair raw payload hp hz
  have hx := ArgumentEntriesNilExtraction.Proof.nilExtraction body alpha Delta raw param hc
  obtain ⟨he⟩ := valueUnique ArgumentEntriesRecursor.extract (suc entries) (suc z) ![raw,param] hv hx
  exact andIntro ht ⟨cancelSuc he⟩

theorem consAccepted (H : Program 1) (types raw gamma tau head tail requested tailTypes : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma))) :
    Nonempty (Derivation body Delta (StepCons types requested tailTypes)) ∧
    Nonempty (Derivation body Delta (eqn requested tau)) ∧
    Nonempty (Derivation body Delta (TermAccepted H tau head gamma)) ∧
    Nonempty (Derivation body Delta (ArgumentsAccepted H tailTypes tail gamma)) := by
  have h := iffForward (OriginalTypedDecoderTransportBinaryAcceptanceProof.consIff H raw tau head tail types requested tailTypes gamma hc hf) ha
  have he := andLeft (andRight h)
  rw [equalEqn] at he
  exact ⟨OriginalTypedDecoderInternalListProof.consFields types requested tailTypes (andLeft h) hf,
    he, andLeft (andRight (andRight h)), andRight (andRight (andRight h))⟩

theorem consEntries (raw param entries tau head tail tailEntries entry listCode : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail param)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode entry tailEntries))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode entries entry tailEntries)) := by
  have hs := StandaloneConsExtraction.Proof.consSuccess body alpha Delta raw tau head tail param tailEntries entry listCode hc ht hp hl
  obtain ⟨he⟩ := valueUnique ArgumentEntriesRecursor.extract (suc entries) (suc listCode) ![raw,param] hv hs
  exact outputTransport InternalListCodec.consCode listCode entries ![entry,tailEntries]
    ⟨symm (cancelSuc he)⟩ hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.SupportProof
