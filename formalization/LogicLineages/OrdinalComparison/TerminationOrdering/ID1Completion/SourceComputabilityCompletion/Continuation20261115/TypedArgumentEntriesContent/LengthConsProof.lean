module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.LengthValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.LengthBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.LengthConsProof
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

open OriginalContextInsertionSyntaxProof (lengthRename)
theorem atEntryLength (H : Program 1) (types raw gamma param entries entryLength typeLength tau head tail requested tailTypes tailEntries entry listCode tailEntryLength : OTerm alpha)
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
    : Nonempty (Derivation body Delta (eqn entryLength typeLength)) := by
  apply programCases OriginalContextInsertion.length (Fin.cons tailTypes Fin.elim0) _
  intro beta j Theta tailTypeLength hj hx
  rw [eqnRelabel]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hcj
  have hfj := renameInto hf j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hfj
  have haj := renameInto ha j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at haj
  have hvj := renameInto hv j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hvj
  have hlj := renameInto hl j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hlj
  have htj := renameInto ht j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at htj
  have ihj := renameInto ih j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at ihj
  have hej := renameInto he j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hej
  have hpj := renameInto hp j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hpj
  have hlistj := renameInto hlist j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hlistj
  have hlej := renameInto hle j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hlej
  exact LengthValueProof.consAtValues H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (entryLength.relabel j) (typeLength.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (requested.relabel j) (tailTypes.relabel j) (tailEntries.relabel j) (entry.relabel j) (listCode.relabel j) (tailEntryLength.relabel j) tailTypeLength hcj hfj haj hvj hlj htj ihj hej hpj hlistj hlej hx

theorem atList (H : Program 1) (types raw gamma param entries entryLength typeLength tau head tail requested tailTypes tailEntries entry listCode : OTerm alpha)
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
    : Nonempty (Derivation body Delta (eqn entryLength typeLength)) := by
  apply programCases OriginalContextInsertion.length (Fin.cons tailEntries Fin.elim0) _
  intro beta j Theta tailEntryLength hj hx
  rw [eqnRelabel]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hcj
  have hfj := renameInto hf j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hfj
  have haj := renameInto ha j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at haj
  have hvj := renameInto hv j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hvj
  have hlj := renameInto hl j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hlj
  have htj := renameInto ht j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at htj
  have ihj := renameInto ih j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at ihj
  have hej := renameInto he j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hej
  have hpj := renameInto hp j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hpj
  have hlistj := renameInto hlist j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hlistj
  exact atEntryLength H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (entryLength.relabel j) (typeLength.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (requested.relabel j) (tailTypes.relabel j) (tailEntries.relabel j) (entry.relabel j) (listCode.relabel j) tailEntryLength hcj hfj haj hvj hlj htj ihj hej hpj hlistj hx

theorem atEntry (H : Program 1) (types raw gamma param entries entryLength typeLength tau head tail requested tailTypes tailEntries entry : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph entryLength entries)))
    (ht : Nonempty (Derivation body Delta (lengthGraph typeLength types)))
    (ih : Nonempty (Derivation body Delta (LengthInductionDefinitions.BelowRaw H raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail param)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau head)))
    : Nonempty (Derivation body Delta (eqn entryLength typeLength)) := by
  apply programCases InternalListCodec.consCode (Fin.cons entry (Fin.cons tailEntries Fin.elim0)) _
  intro beta j Theta listCode hj hx
  rw [eqnRelabel]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hcj
  have hfj := renameInto hf j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hfj
  have haj := renameInto ha j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at haj
  have hvj := renameInto hv j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hvj
  have hlj := renameInto hl j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hlj
  have htj := renameInto ht j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at htj
  have ihj := renameInto ih j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at ihj
  have hej := renameInto he j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hej
  have hpj := renameInto hp j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hpj
  exact atList H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (entryLength.relabel j) (typeLength.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (requested.relabel j) (tailTypes.relabel j) (tailEntries.relabel j) (entry.relabel j) listCode hcj hfj haj hvj hlj htj ihj hej hpj hx

theorem atTailEntries (H : Program 1) (types raw gamma param entries entryLength typeLength tau head tail requested tailTypes tailEntries : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph entryLength entries)))
    (ht : Nonempty (Derivation body Delta (lengthGraph typeLength types)))
    (ih : Nonempty (Derivation body Delta (LengthInductionDefinitions.BelowRaw H raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail param)))
    : Nonempty (Derivation body Delta (eqn entryLength typeLength)) := by
  apply programCases InternalPairing.pairing (Fin.cons tau (Fin.cons head Fin.elim0)) _
  intro beta j Theta entry hj hx
  rw [eqnRelabel]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hcj
  have hfj := renameInto hf j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hfj
  have haj := renameInto ha j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at haj
  have hvj := renameInto hv j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hvj
  have hlj := renameInto hl j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hlj
  have htj := renameInto ht j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at htj
  have ihj := renameInto ih j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at ihj
  have hej := renameInto he j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hej
  exact atEntry H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (entryLength.relabel j) (typeLength.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (requested.relabel j) (tailTypes.relabel j) (tailEntries.relabel j) entry hcj hfj haj hvj hlj htj ihj hej hx

theorem atTailValue (H : Program 1) (types raw gamma param entries entryLength typeLength tau head tail requested tailTypes tailValue : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph entryLength entries)))
    (ht : Nonempty (Derivation body Delta (lengthGraph typeLength types)))
    (ih : Nonempty (Derivation body Delta (LengthInductionDefinitions.BelowRaw H raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract tailValue tail param)))
    : Nonempty (Derivation body Delta (eqn entryLength typeLength)) := by
  have haTail := TypedArgumentEntriesDefined.SupportProof.tailAccepted H types raw gamma tau head tail requested tailTypes hc hf ha
  have hn := TypedArgumentEntriesDefined.Proof.typedDefined body H alpha Delta tailTypes tail gamma param tailValue haTail he
  apply zeroSuccessorCases Delta tailValue _
  · obtain ⟨hn⟩ := hn
    exact ⟨Derivation.explosion (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _)
      (Derivation.hypothesis List.mem_cons_self))⟩
  · intro beta j Theta tailEntries hj hsucc
    rw [eqnRelabel]
    have hcj := renameInto hc j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hcj
    have hfj := renameInto hf j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hfj
    have haj := renameInto ha j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at haj
    have hvj := renameInto hv j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hvj
    have hlj := renameInto hl j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hlj
    have htj := renameInto ht j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at htj
    have ihj := renameInto ih j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at ihj
    have hej := renameInto he j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hej
    have hex := outputTransport ArgumentEntriesRecursor.extract (tailValue.relabel j) (suc tailEntries)
      (Fin.cons (tail.relabel j) (Fin.cons (param.relabel j) Fin.elim0)) hsucc hej
    exact atTailEntries H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (entryLength.relabel j) (typeLength.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (requested.relabel j) (tailTypes.relabel j) tailEntries hcj hfj haj hvj hlj htj ihj hex

theorem atArrow (H : Program 1) (types raw gamma param entries entryLength typeLength tau head tail requested tailTypes : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph entryLength entries)))
    (ht : Nonempty (Derivation body Delta (lengthGraph typeLength types)))
    (ih : Nonempty (Derivation body Delta (LengthInductionDefinitions.BelowRaw H raw)))
    : Nonempty (Derivation body Delta (eqn entryLength typeLength)) := by
  apply programCases ArgumentEntriesRecursor.extract (Fin.cons tail (Fin.cons param Fin.elim0)) _
  intro beta j Theta tailValue hj hx
  rw [eqnRelabel]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hcj
  have hfj := renameInto hf j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hfj
  have haj := renameInto ha j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at haj
  have hvj := renameInto hv j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hvj
  have hlj := renameInto hl j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hlj
  have htj := renameInto ht j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at htj
  have ihj := renameInto ih j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at ihj
  exact atTailValue H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (entryLength.relabel j) (typeLength.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (requested.relabel j) (tailTypes.relabel j) tailValue hcj hfj haj hvj hlj htj ihj hx

theorem consLength (H : Program 1) (types raw gamma param entries entryLength typeLength tau head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hl : Nonempty (Derivation body Delta (lengthGraph entryLength entries)))
    (ht : Nonempty (Derivation body Delta (lengthGraph typeLength types)))
    (ih : Nonempty (Derivation body Delta (LengthInductionDefinitions.BelowRaw H raw)))
    : Nonempty (Derivation body Delta (eqn entryLength typeLength)) := by
  apply OriginalTypedDecoderTransportContextProof.arrowCases types _
  intro beta j Theta requested tailTypes hj hf
  rw [eqnRelabel]
  have hcj := renameInto hc j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hcj
  have haj := renameInto ha j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at haj
  have hvj := renameInto hv j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hvj
  have hlj := renameInto hl j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at hlj
  have htj := renameInto ht j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at htj
  have ihj := renameInto ih j Theta hj
  simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,stepArrowFieldsRename,LengthInductionSyntaxProof.belowRawRename] at ihj
  exact atArrow H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (entryLength.relabel j) (typeLength.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) requested tailTypes hcj hf haj hvj hlj htj ihj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.LengthConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.LengthConsProof
