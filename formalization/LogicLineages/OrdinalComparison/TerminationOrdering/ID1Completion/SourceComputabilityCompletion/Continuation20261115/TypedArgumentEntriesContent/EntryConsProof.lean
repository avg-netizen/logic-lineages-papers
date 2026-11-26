module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryConsProof
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

theorem atEntry (H : Program 1) (types raw gamma param entries entry tau child annotation head tail requested tailTypes tailEntries headEntry : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw annotation head tail)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) entries entry)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau child)))
    (ih : Nonempty (Derivation body Delta (EntryInductionDefinitions.BelowRaw H raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail param)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing headEntry annotation head)))
    : Nonempty (Derivation body Delta (TermAccepted H tau child gamma)) := by
  apply programCases InternalListCodec.consCode (Fin.cons headEntry (Fin.cons tailEntries Fin.elim0)) _
  intro beta j Theta listCode hj hx
  rw [termAcceptedRename]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hcj
  have hfj := renameInto hf j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hfj
  have haj := renameInto ha j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at haj
  have hvj := renameInto hv j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hvj
  have hmj := renameInto hm j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hmj
  have hqj := renameInto hq j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hqj
  have ihj := renameInto ih j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at ihj
  have hej := renameInto he j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hej
  have hpj := renameInto hp j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hpj
  exact EntryValueProof.consAtValues H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (entry.relabel j) (tau.relabel j) (child.relabel j) (annotation.relabel j) (head.relabel j) (tail.relabel j) (requested.relabel j) (tailTypes.relabel j) (tailEntries.relabel j) (headEntry.relabel j) listCode hcj hfj haj hvj hmj hqj ihj hej hpj hx

theorem atTailEntries (H : Program 1) (types raw gamma param entries entry tau child annotation head tail requested tailTypes tailEntries : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw annotation head tail)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) entries entry)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau child)))
    (ih : Nonempty (Derivation body Delta (EntryInductionDefinitions.BelowRaw H raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail param)))
    : Nonempty (Derivation body Delta (TermAccepted H tau child gamma)) := by
  apply programCases InternalPairing.pairing (Fin.cons annotation (Fin.cons head Fin.elim0)) _
  intro beta j Theta headEntry hj hx
  rw [termAcceptedRename]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hcj
  have hfj := renameInto hf j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hfj
  have haj := renameInto ha j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at haj
  have hvj := renameInto hv j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hvj
  have hmj := renameInto hm j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hmj
  have hqj := renameInto hq j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hqj
  have ihj := renameInto ih j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at ihj
  have hej := renameInto he j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hej
  exact atEntry H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (entry.relabel j) (tau.relabel j) (child.relabel j) (annotation.relabel j) (head.relabel j) (tail.relabel j) (requested.relabel j) (tailTypes.relabel j) (tailEntries.relabel j) headEntry hcj hfj haj hvj hmj hqj ihj hej hx

theorem atTailValue (H : Program 1) (types raw gamma param entries entry tau child annotation head tail requested tailTypes tailValue : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw annotation head tail)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) entries entry)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau child)))
    (ih : Nonempty (Derivation body Delta (EntryInductionDefinitions.BelowRaw H raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract tailValue tail param)))
    : Nonempty (Derivation body Delta (TermAccepted H tau child gamma)) := by
  have haTail := TypedArgumentEntriesDefined.SupportProof.tailAccepted H types raw gamma annotation head tail requested tailTypes hc hf ha
  have hn := TypedArgumentEntriesDefined.Proof.typedDefined body H alpha Delta tailTypes tail gamma param tailValue haTail he
  apply zeroSuccessorCases Delta tailValue _
  · obtain ⟨hn⟩ := hn
    exact ⟨Derivation.explosion (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _)
      (Derivation.hypothesis List.mem_cons_self))⟩
  · intro beta j Theta tailEntries hj hsucc
    rw [termAcceptedRename]
    have hcj := renameInto hc j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hcj
    have hfj := renameInto hf j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hfj
    have haj := renameInto ha j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at haj
    have hvj := renameInto hv j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hvj
    have hmj := renameInto hm j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hmj
    have hqj := renameInto hq j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hqj
    have ihj := renameInto ih j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at ihj
    have hej := renameInto he j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hej
    have hex := outputTransport ArgumentEntriesRecursor.extract (tailValue.relabel j) (suc tailEntries)
      (Fin.cons (tail.relabel j) (Fin.cons (param.relabel j) Fin.elim0)) hsucc hej
    exact atTailEntries H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (entry.relabel j) (tau.relabel j) (child.relabel j) (annotation.relabel j) (head.relabel j) (tail.relabel j) (requested.relabel j) (tailTypes.relabel j) tailEntries hcj hfj haj hvj hmj hqj ihj hex

theorem atArrow (H : Program 1) (types raw gamma param entries entry tau child annotation head tail requested tailTypes : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw annotation head tail)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) entries entry)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau child)))
    (ih : Nonempty (Derivation body Delta (EntryInductionDefinitions.BelowRaw H raw)))
    : Nonempty (Derivation body Delta (TermAccepted H tau child gamma)) := by
  apply programCases ArgumentEntriesRecursor.extract (Fin.cons tail (Fin.cons param Fin.elim0)) _
  intro beta j Theta tailValue hj hx
  rw [termAcceptedRename]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hcj
  have hfj := renameInto hf j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hfj
  have haj := renameInto ha j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at haj
  have hvj := renameInto hv j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hvj
  have hmj := renameInto hm j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hmj
  have hqj := renameInto hq j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hqj
  have ihj := renameInto ih j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at ihj
  exact atTailValue H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (entry.relabel j) (tau.relabel j) (child.relabel j) (annotation.relabel j) (head.relabel j) (tail.relabel j) (requested.relabel j) (tailTypes.relabel j) tailValue hcj hfj haj hvj hmj hqj ihj hx

theorem consEntry (H : Program 1) (types raw gamma param entries entry tau child annotation head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw annotation head tail)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) entries entry)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau child)))
    (ih : Nonempty (Derivation body Delta (EntryInductionDefinitions.BelowRaw H raw)))
    : Nonempty (Derivation body Delta (TermAccepted H tau child gamma)) := by
  apply OriginalTypedDecoderTransportContextProof.arrowCases types _
  intro beta j Theta requested tailTypes hj hf
  rw [termAcceptedRename]
  have hcj := renameInto hc j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hcj
  have haj := renameInto ha j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at haj
  have hvj := renameInto hv j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hvj
  have hmj := renameInto hm j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hmj
  have hqj := renameInto hq j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at hqj
  have ihj := renameInto ih j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename,stepArrowFieldsRename,EntryInductionSyntaxProof.belowRawRename] at ihj
  exact atArrow H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (entry.relabel j) (tau.relabel j) (child.relabel j) (annotation.relabel j) (head.relabel j) (tail.relabel j) requested tailTypes hcj hf haj hvj hmj hqj ihj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryConsProof
