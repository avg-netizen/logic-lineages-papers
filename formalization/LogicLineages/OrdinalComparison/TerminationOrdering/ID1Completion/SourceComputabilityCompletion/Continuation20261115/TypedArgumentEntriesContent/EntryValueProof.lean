module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryValueProof
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

theorem nilEntry (H : Program 1) (types raw gamma param entries entry tau child payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 6) payload)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) entries entry))) :
    Nonempty (Derivation body Delta (TermAccepted H tau child gamma)) := by
  have hi := SupportProof.nilIdentities H types raw gamma param entries payload hp ha hv
  have hm0 := headTransport contains (numeral 1) entries z (Fin.cons entry Fin.elim0) (andRight hi) hm
  have hz := (PrimaryMembership.Proof.nilGraph body alpha Delta (numeral 1) entry).mp hm0
  rw [equalEqn] at hz
  obtain ⟨hz⟩ := hz
  exact ⟨Derivation.explosion (sucNeZeroApply hz)⟩

theorem acceptedHeadEntry (H : Program 1) (gamma headEntry entry annotation head tau child : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn headEntry entry)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing headEntry annotation head)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau child)))
    (ha : Nonempty (Derivation body Delta (TermAccepted H annotation head gamma))) :
    Nonempty (Derivation body Delta (TermAccepted H tau child gamma)) := by
  have hp' := outputTransport InternalPairing.pairing headEntry entry ![annotation,head] he hp
  have ht := valueUnique InternalUnpair.left annotation tau (Fin.cons entry Fin.elim0)
    (pairLeft entry annotation head hp') (pairLeft entry tau child hq)
  have hc := valueUnique InternalUnpair.right head child (Fin.cons entry Fin.elim0)
    (pairRight entry annotation head hp') (pairRight entry tau child hq)
  unfold TermAccepted programGraph at ha ⊢
  apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 3 Delta
    (OrdinaryArithmetic.graphFormula (OriginalTypedDecoder.termCheck H)) (numeral 1)
    ![annotation,head,gamma] ![tau,child,gamma] _ ha
  intro i
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.cases ?_ (fun q => Fin.elim0 q) l) k) i
  · rw [InternalSourceInversionSupportProof.onEquality]; exact ht
  · rw [InternalSourceInversionSupportProof.onEquality]; exact hc
  · rw [InternalSourceInversionSupportProof.onEquality]; exact ⟨refl _⟩

theorem consAtValues (H : Program 1)
    (types raw gamma param entries entry tau child annotation head tail requested tailTypes
      tailEntries headEntry listCode : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw annotation head tail)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) entries entry)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau child)))
    (ih : Nonempty (Derivation body Delta (EntryInductionDefinitions.BelowRaw H raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail param)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing headEntry annotation head)))
    (hlist : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode headEntry tailEntries))) :
    Nonempty (Derivation body Delta (TermAccepted H tau child gamma)) := by
  obtain ⟨_,_,hhead,hacc⟩ := SupportProof.consAccepted H types raw gamma annotation head tail requested tailTypes hc hf ha
  have hentries := SupportProof.consEntries raw param entries annotation head tail tailEntries headEntry listCode hc hv he hp hlist
  apply InternalApplicationValidityStackAppendInductionCoreProof.formulaCases (eqn headEntry entry)
  · exact acceptedHeadEntry H gamma headEntry entry annotation head tau child
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hp _) (withHyp hq _) (withHyp hhead _)
  · have hne : Nonempty (Derivation body ((eqn headEntry entry).not :: Delta) (equal headEntry entry).not) := by
      rw [equalEqn]
      exact ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hmTail := (PrimaryMembership.Proof.missGraph body alpha ((eqn headEntry entry).not :: Delta)
      entries headEntry tailEntries entry (numeral 1) (withHyp hentries _) hne).mp (withHyp hm _)
    exact EntryBindingProof.belowRawApply H raw tail tailTypes gamma param tailEntries entry tau child (withHyp ih _)
      (withHyp (CrossRootCacheCoherence.SupportProof.consTailStrict raw annotation head tail hc) _)
      (andIntro (andIntro (andIntro (withHyp hacc _) (withHyp he _)) hmTail) (withHyp hq _))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryValueProof
