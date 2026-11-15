module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.ConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.CoreProof
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
open OriginalContextInsertionSyntaxProof (lengthRename)
theorem consTag (H : Program 1) (types raw gamma param entries count index entry annotation child expected : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral 7) raw)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph count types)))
    (hb : Nonempty (Derivation body Delta (Below index count)))
    (hlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup entry index entries)))
    (htlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup expected index types)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry annotation child)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw)))
    : Nonempty (Derivation body Delta (eqn annotation expected ⊓ TermAccepted H expected child gamma)) := by
  apply OriginalRawSyntaxTransportInternalParserBinaryProof.consCases raw _ ht
  intro beta j Theta headAnnotation head tail hj hc
  simp only [conjunctionRename,eqnRelabel,termAcceptedRename]
  have haj := renameInto ha j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at haj
  have hvj := renameInto hv j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hvj
  have hlj := renameInto hl j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hlj
  have hbj := renameInto hb j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hbj
  have hlookj := renameInto hlook j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hlookj
  have htlookj := renameInto htlook j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at htlookj
  have hqj := renameInto hq j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hqj
  have ihj := renameInto ih j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at ihj
  exact ConsProof.consPosition H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (count.relabel j) (index.relabel j) (entry.relabel j) (annotation.relabel j) (child.relabel j) (expected.relabel j) headAnnotation head tail hc haj hvj hlj hbj hlookj htlookj hqj ihj

theorem notNil (H : Program 1) (types raw gamma param entries count index entry annotation child expected tag payload : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload raw)))
    (hn : Nonempty (Derivation body Delta ((eqn tag (numeral 6)).not)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph count types)))
    (hb : Nonempty (Derivation body Delta (Below index count)))
    (hlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup entry index entries)))
    (htlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup expected index types)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry annotation child)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw)))
    : Nonempty (Derivation body Delta (eqn annotation expected ⊓ TermAccepted H expected child gamma)) := by
  apply InternalApplicationValidityStackAppendInductionCoreProof.formulaCases (eqn tag (numeral 7))
  · have h7 := outputTransport InternalUnpair.left tag (numeral 7) (Fin.cons raw Fin.elim0)
      ⟨Derivation.hypothesis (body := body) (Gamma := eqn tag (numeral 7) :: Delta) List.mem_cons_self⟩ (withHyp ht _)
    exact consTag H types raw gamma param entries count index entry annotation child expected h7 (withHyp ha _) (withHyp hv _) (withHyp hl _) (withHyp hb _) (withHyp hlook _) (withHyp htlook _) (withHyp hq _) (withHyp ih _)
  · have hp' := reconstructPair raw tag payload (withHyp ht (eqn tag (numeral 7)).not) (withHyp hp _)
    have hn' := withHyp hn (eqn tag (numeral 7)).not
    have h7 : Nonempty (Derivation body ((eqn tag (numeral 7)).not :: Delta) (eqn tag (numeral 7)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hbad := OriginalTypedDecoderInternalAcceptanceRejectedProof.argumentsRejected H raw tag payload types gamma hp'
      (by simpa only [equalEqn] using andIntro hn' h7) (withHyp ha _)
    obtain ⟨hbad⟩ := hbad
    exact ⟨Derivation.explosion hbad⟩

theorem atSelectors (H : Program 1) (types raw gamma param entries count index entry annotation child expected tag payload : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload raw)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph count types)))
    (hb : Nonempty (Derivation body Delta (Below index count)))
    (hlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup entry index entries)))
    (htlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup expected index types)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry annotation child)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw)))
    : Nonempty (Derivation body Delta (eqn annotation expected ⊓ TermAccepted H expected child gamma)) := by
  apply InternalApplicationValidityStackAppendInductionCoreProof.formulaCases (eqn tag (numeral 6))
  · have h6 := outputTransport InternalUnpair.left tag (numeral 6) (Fin.cons raw Fin.elim0)
      ⟨Derivation.hypothesis (body := body) (Gamma := eqn tag (numeral 6) :: Delta) List.mem_cons_self⟩ (withHyp ht _)
    exact ValueProof.nilPosition H types raw gamma param entries count index entry annotation child expected payload
      (reconstructPair raw (numeral 6) payload h6 (withHyp hp _)) (withHyp ha _) (withHyp hv _) (withHyp hl _) (withHyp hb _)
  · exact notNil H types raw gamma param entries count index entry annotation child expected tag payload (withHyp ht _) (withHyp hp _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha _) (withHyp hv _) (withHyp hl _) (withHyp hb _) (withHyp hlook _) (withHyp htlook _) (withHyp hq _) (withHyp ih _)

theorem atTag (H : Program 1) (types raw gamma param entries count index entry annotation child expected tag : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph count types)))
    (hb : Nonempty (Derivation body Delta (Below index count)))
    (hlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup entry index entries)))
    (htlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup expected index types)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry annotation child)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw)))
    : Nonempty (Derivation body Delta (eqn annotation expected ⊓ TermAccepted H expected child gamma)) := by
  apply programCases InternalUnpair.right (Fin.cons raw Fin.elim0) _
  intro beta j Theta payload hj hp
  simp only [conjunctionRename,eqnRelabel,termAcceptedRename]
  simp only [consTermRename,emptyRename] at hp
  have htj := renameInto ht j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at htj
  have haj := renameInto ha j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at haj
  have hvj := renameInto hv j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hvj
  have hlj := renameInto hl j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hlj
  have hbj := renameInto hb j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hbj
  have hlookj := renameInto hlook j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hlookj
  have htlookj := renameInto htlook j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at htlookj
  have hqj := renameInto hq j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hqj
  have ihj := renameInto ih j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at ihj
  exact atSelectors H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (count.relabel j) (index.relabel j) (entry.relabel j) (annotation.relabel j) (child.relabel j) (expected.relabel j) (tag.relabel j) payload htj hp haj hvj hlj hbj hlookj htlookj hqj ihj

theorem close (H : Program 1) (types raw gamma param entries count index entry annotation child expected : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph count types)))
    (hb : Nonempty (Derivation body Delta (Below index count)))
    (hlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup entry index entries)))
    (htlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup expected index types)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry annotation child)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw)))
    : Nonempty (Derivation body Delta (eqn annotation expected ⊓ TermAccepted H expected child gamma)) := by
  apply programCases InternalUnpair.left (Fin.cons raw Fin.elim0) _
  intro beta j Theta tag hj ht
  simp only [conjunctionRename,eqnRelabel,termAcceptedRename]
  simp only [consTermRename,emptyRename] at ht
  have haj := renameInto ha j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at haj
  have hvj := renameInto hv j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hvj
  have hlj := renameInto hl j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hlj
  have hbj := renameInto hb j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hbj
  have hlookj := renameInto hlook j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hlookj
  have htlookj := renameInto htlook j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at htlookj
  have hqj := renameInto hq j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hqj
  have ihj := renameInto ih j Theta hj
  simp only [argumentsAcceptedRename,graph1Rename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at ihj
  exact atTag H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (count.relabel j) (index.relabel j) (entry.relabel j) (annotation.relabel j) (child.relabel j) (expected.relabel j) tag ht haj hvj hlj hbj hlookj htlookj hqj ihj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.CoreProof
