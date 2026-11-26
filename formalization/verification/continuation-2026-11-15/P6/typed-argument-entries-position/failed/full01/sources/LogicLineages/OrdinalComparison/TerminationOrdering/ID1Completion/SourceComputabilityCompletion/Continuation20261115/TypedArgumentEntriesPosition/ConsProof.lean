module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.IndexProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.ConsProof
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
theorem atValues (H : Program 1) (types raw gamma param entries count index entry annotation child expected headAnnotation head tail requested tailTypes tailEntries headEntry listCode tailCount : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw headAnnotation head tail)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph count types)))
    (hb : Nonempty (Derivation body Delta (Below index count)))
    (hlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup entry index entries)))
    (htlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup expected index types)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry annotation child)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail param)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing headEntry headAnnotation head)))
    (hlist : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode headEntry tailEntries)))
    (hlen : Nonempty (Derivation body Delta (lengthGraph tailCount tailTypes)))
    : Nonempty (Derivation body Delta (eqn annotation expected ⊓ TermAccepted H expected child gamma)) := by
  obtain ⟨htypes,hr,hhead,hacc⟩ := TypedArgumentEntriesContent.SupportProof.consAccepted H types raw gamma headAnnotation head tail requested tailTypes hc hf ha
  have hentries := TypedArgumentEntriesContent.SupportProof.consEntries raw param entries headAnnotation head tail tailEntries headEntry listCode hc hv he hp hlist
  exact IndexProof.atIndex H types raw gamma param entries count index entry annotation child expected headAnnotation head tail requested tailTypes
    tailEntries headEntry tailCount hc htypes hentries hacc he hl hb hlook htlook hq ih hlen hr hp hhead

theorem atList (H : Program 1) (types raw gamma param entries count index entry annotation child expected headAnnotation head tail requested tailTypes tailEntries headEntry listCode : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw headAnnotation head tail)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph count types)))
    (hb : Nonempty (Derivation body Delta (Below index count)))
    (hlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup entry index entries)))
    (htlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup expected index types)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry annotation child)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail param)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing headEntry headAnnotation head)))
    (hlist : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode headEntry tailEntries)))
    : Nonempty (Derivation body Delta (eqn annotation expected ⊓ TermAccepted H expected child gamma)) := by
  apply programCases OriginalContextInsertion.length (Fin.cons tailTypes Fin.elim0) _
  intro beta j Theta tailCount hj hx
  simp only [conjunctionRename,eqnRelabel,termAcceptedRename]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hcj
  have hfj := renameInto hf j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hfj
  have haj := renameInto ha j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at haj
  have hvj := renameInto hv j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hvj
  have hlj := renameInto hl j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hlj
  have hbj := renameInto hb j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hbj
  have hlookj := renameInto hlook j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hlookj
  have htlookj := renameInto htlook j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at htlookj
  have hqj := renameInto hq j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hqj
  have ihj := renameInto ih j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at ihj
  have hej := renameInto he j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hej
  have hpj := renameInto hp j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hpj
  have hlistj := renameInto hlist j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hlistj
  exact atValues H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (count.relabel j) (index.relabel j) (entry.relabel j) (annotation.relabel j) (child.relabel j) (expected.relabel j) (headAnnotation.relabel j) (head.relabel j) (tail.relabel j) (requested.relabel j) (tailTypes.relabel j) (tailEntries.relabel j) (headEntry.relabel j) (listCode.relabel j) tailCount hcj hfj haj hvj hlj hbj hlookj htlookj hqj ihj hej hpj hlistj hx

theorem atEntry (H : Program 1) (types raw gamma param entries count index entry annotation child expected headAnnotation head tail requested tailTypes tailEntries headEntry : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw headAnnotation head tail)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph count types)))
    (hb : Nonempty (Derivation body Delta (Below index count)))
    (hlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup entry index entries)))
    (htlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup expected index types)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry annotation child)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail param)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing headEntry headAnnotation head)))
    : Nonempty (Derivation body Delta (eqn annotation expected ⊓ TermAccepted H expected child gamma)) := by
  apply programCases InternalListCodec.consCode (Fin.cons headEntry (Fin.cons tailEntries Fin.elim0)) _
  intro beta j Theta listCode hj hx
  simp only [conjunctionRename,eqnRelabel,termAcceptedRename]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hcj
  have hfj := renameInto hf j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hfj
  have haj := renameInto ha j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at haj
  have hvj := renameInto hv j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hvj
  have hlj := renameInto hl j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hlj
  have hbj := renameInto hb j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hbj
  have hlookj := renameInto hlook j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hlookj
  have htlookj := renameInto htlook j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at htlookj
  have hqj := renameInto hq j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hqj
  have ihj := renameInto ih j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at ihj
  have hej := renameInto he j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hej
  have hpj := renameInto hp j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hpj
  exact atList H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (count.relabel j) (index.relabel j) (entry.relabel j) (annotation.relabel j) (child.relabel j) (expected.relabel j) (headAnnotation.relabel j) (head.relabel j) (tail.relabel j) (requested.relabel j) (tailTypes.relabel j) (tailEntries.relabel j) (headEntry.relabel j) listCode hcj hfj haj hvj hlj hbj hlookj htlookj hqj ihj hej hpj hx

theorem atTailEntries (H : Program 1) (types raw gamma param entries count index entry annotation child expected headAnnotation head tail requested tailTypes tailEntries : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw headAnnotation head tail)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph count types)))
    (hb : Nonempty (Derivation body Delta (Below index count)))
    (hlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup entry index entries)))
    (htlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup expected index types)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry annotation child)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail param)))
    : Nonempty (Derivation body Delta (eqn annotation expected ⊓ TermAccepted H expected child gamma)) := by
  apply programCases InternalPairing.pairing (Fin.cons headAnnotation (Fin.cons head Fin.elim0)) _
  intro beta j Theta headEntry hj hx
  simp only [conjunctionRename,eqnRelabel,termAcceptedRename]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hcj
  have hfj := renameInto hf j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hfj
  have haj := renameInto ha j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at haj
  have hvj := renameInto hv j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hvj
  have hlj := renameInto hl j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hlj
  have hbj := renameInto hb j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hbj
  have hlookj := renameInto hlook j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hlookj
  have htlookj := renameInto htlook j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at htlookj
  have hqj := renameInto hq j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hqj
  have ihj := renameInto ih j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at ihj
  have hej := renameInto he j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hej
  exact atEntry H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (count.relabel j) (index.relabel j) (entry.relabel j) (annotation.relabel j) (child.relabel j) (expected.relabel j) (headAnnotation.relabel j) (head.relabel j) (tail.relabel j) (requested.relabel j) (tailTypes.relabel j) (tailEntries.relabel j) headEntry hcj hfj haj hvj hlj hbj hlookj htlookj hqj ihj hej hx

theorem atTailValue (H : Program 1) (types raw gamma param entries count index entry annotation child expected headAnnotation head tail requested tailTypes tailValue : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw headAnnotation head tail)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph count types)))
    (hb : Nonempty (Derivation body Delta (Below index count)))
    (hlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup entry index entries)))
    (htlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup expected index types)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry annotation child)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract tailValue tail param)))
    : Nonempty (Derivation body Delta (eqn annotation expected ⊓ TermAccepted H expected child gamma)) := by
  have haTail := TypedArgumentEntriesDefined.SupportProof.tailAccepted H types raw gamma headAnnotation head tail requested tailTypes hc hf ha
  have hn := TypedArgumentEntriesDefined.Proof.typedDefined body H alpha Delta tailTypes tail gamma param tailValue haTail he
  apply zeroSuccessorCases Delta tailValue _
  · obtain ⟨hn⟩ := hn
    exact ⟨Derivation.explosion (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _)
      (Derivation.hypothesis List.mem_cons_self))⟩
  · intro beta j Theta tailEntries hj hsucc
    simp only [conjunctionRename,eqnRelabel,termAcceptedRename]
    have hcj := renameInto hc j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hcj
    have hfj := renameInto hf j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hfj
    have haj := renameInto ha j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at haj
    have hvj := renameInto hv j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hvj
    have hlj := renameInto hl j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hlj
    have hbj := renameInto hb j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hbj
    have hlookj := renameInto hlook j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hlookj
    have htlookj := renameInto htlook j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at htlookj
    have hqj := renameInto hq j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hqj
    have ihj := renameInto ih j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at ihj
    have hej := renameInto he j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hej
    have hex := outputTransport ArgumentEntriesRecursor.extract (tailValue.relabel j) (suc tailEntries)
      (Fin.cons (tail.relabel j) (Fin.cons (param.relabel j) Fin.elim0)) hsucc hej
    exact atTailEntries H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (count.relabel j) (index.relabel j) (entry.relabel j) (annotation.relabel j) (child.relabel j) (expected.relabel j) (headAnnotation.relabel j) (head.relabel j) (tail.relabel j) (requested.relabel j) (tailTypes.relabel j) tailEntries hcj hfj haj hvj hlj hbj hlookj htlookj hqj ihj hex

theorem atArrow (H : Program 1) (types raw gamma param entries count index entry annotation child expected headAnnotation head tail requested tailTypes : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw headAnnotation head tail)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph count types)))
    (hb : Nonempty (Derivation body Delta (Below index count)))
    (hlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup entry index entries)))
    (htlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup expected index types)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry annotation child)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw)))
    : Nonempty (Derivation body Delta (eqn annotation expected ⊓ TermAccepted H expected child gamma)) := by
  apply programCases ArgumentEntriesRecursor.extract (Fin.cons tail (Fin.cons param Fin.elim0)) _
  intro beta j Theta tailValue hj hx
  simp only [conjunctionRename,eqnRelabel,termAcceptedRename]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hcj
  have hfj := renameInto hf j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hfj
  have haj := renameInto ha j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at haj
  have hvj := renameInto hv j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hvj
  have hlj := renameInto hl j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hlj
  have hbj := renameInto hb j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hbj
  have hlookj := renameInto hlook j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hlookj
  have htlookj := renameInto htlook j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at htlookj
  have hqj := renameInto hq j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hqj
  have ihj := renameInto ih j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at ihj
  exact atTailValue H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (count.relabel j) (index.relabel j) (entry.relabel j) (annotation.relabel j) (child.relabel j) (expected.relabel j) (headAnnotation.relabel j) (head.relabel j) (tail.relabel j) (requested.relabel j) (tailTypes.relabel j) tailValue hcj hfj haj hvj hlj hbj hlookj htlookj hqj ihj hx

theorem consPosition (H : Program 1) (types raw gamma param entries count index entry annotation child expected headAnnotation head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw headAnnotation head tail)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph count types)))
    (hb : Nonempty (Derivation body Delta (Below index count)))
    (hlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup entry index entries)))
    (htlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup expected index types)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry annotation child)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw)))
    : Nonempty (Derivation body Delta (eqn annotation expected ⊓ TermAccepted H expected child gamma)) := by
  apply OriginalTypedDecoderTransportContextProof.arrowCases types _
  intro beta j Theta requested tailTypes hj hf
  simp only [conjunctionRename,eqnRelabel,termAcceptedRename]
  have hcj := renameInto hc j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hcj
  have haj := renameInto ha j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at haj
  have hvj := renameInto hv j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hvj
  have hlj := renameInto hl j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hlj
  have hbj := renameInto hb j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hbj
  have hlookj := renameInto hlook j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hlookj
  have htlookj := renameInto htlook j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at htlookj
  have hqj := renameInto hq j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at hqj
  have ihj := renameInto ih j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,Below,orderRename,stepArrowFieldsRename,InductionSyntaxProof.belowRawRename] at ihj
  exact atArrow H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (count.relabel j) (index.relabel j) (entry.relabel j) (annotation.relabel j) (child.relabel j) (expected.relabel j) (headAnnotation.relabel j) (head.relabel j) (tail.relabel j) requested tailTypes hcj hf haj hvj hlj hbj hlookj htlookj hqj ihj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.ConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.ConsProof
