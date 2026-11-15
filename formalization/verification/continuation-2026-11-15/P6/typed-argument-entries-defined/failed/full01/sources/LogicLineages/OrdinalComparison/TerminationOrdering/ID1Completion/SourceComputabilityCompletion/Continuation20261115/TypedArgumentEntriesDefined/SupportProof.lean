module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesDefined.BindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesDefined.SupportProof
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

theorem positiveOutput (raw param value entries : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)))
    (hs : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param))) :
    Nonempty (Derivation body Delta (eqn value z).not) := by
  obtain ⟨he⟩ := valueUnique ArgumentEntriesRecursor.extract value (suc entries) ![raw,param] hv hs
  have hh := InternalBetaTotalityProof.addHyp he (eqn value z)
  exact ⟨Derivation.implicationIntroduction
    (sucNeZeroApply (trans (symm hh) (Derivation.hypothesis List.mem_cons_self)))⟩

theorem nilPair (raw payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 6) payload)))
    (hz : Nonempty (Derivation body Delta (eqn payload z))) :
    Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0)) := by
  have hpair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 6) z)) := by
    unfold graph2 programGraph at hp ⊢
    apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 Delta
      (OrdinaryArithmetic.graphFormula InternalPairing.pairing) raw ![numeral 6,payload] ![numeral 6,z] _ hp
    intro i
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun q => Fin.elim0 q) k) i
    · rw [InternalSourceInversionSupportProof.onEquality]; exact ⟨refl _⟩
    · rw [InternalSourceInversionSupportProof.onEquality]; exact hz
  exact binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 0 6)
    (OriginalRawSyntaxTransport.constant 0 0) raw (numeral 6) z Fin.elim0 hpair
    (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 6 Fin.elim0)
    (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 Fin.elim0)

theorem nilDefined (H : Program 1) (types raw gamma param value payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 6) payload)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param))) :
    Nonempty (Derivation body Delta (eqn value z).not) := by
  have hz := andLeft (iffForward (OriginalTypedDecoderInternalAcceptanceLeafProof.nilIff H raw payload types gamma hp) ha)
  rw [InternalControlGraphSupportProof.equalEqn] at hz
  have hc := nilPair raw payload hp hz
  exact positiveOutput raw param value z hv (ArgumentEntriesNilExtraction.Proof.nilExtraction body alpha Delta raw param hc)

theorem tailAccepted (H : Program 1) (types raw gamma tau head tail requested tailTypes : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma))) :
    Nonempty (Derivation body Delta (ArgumentsAccepted H tailTypes tail gamma)) := by
  have h := iffForward (OriginalTypedDecoderTransportBinaryAcceptanceProof.consIff H raw tau head tail types requested tailTypes gamma hc hf) ha
  exact andRight (andRight (andRight h))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesDefined.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesDefined.SupportProof
