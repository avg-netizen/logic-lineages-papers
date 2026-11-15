module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.ValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.IndexProof
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
theorem atIndex (H : Program 1) (types raw gamma param entries count index entry annotation child expected headAnnotation head tail requested tailTypes tailEntries headEntry tailCount : OTerm alpha)
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
    (hr : Nonempty (Derivation body Delta (eqn requested headAnnotation)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing headEntry headAnnotation head)))
    (hhead : Nonempty (Derivation body Delta (TermAccepted H headAnnotation head gamma)))
    : Nonempty (Derivation body Delta (eqn annotation expected ⊓ TermAccepted H expected child gamma)) := by
  apply zeroSuccessorCases Delta index _
  · have hindex : Nonempty (Derivation body (eqn index z :: Delta) (eqn index z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hel := headTransport InternalRawListRecursion.lookup entry index z (Fin.cons entries Fin.elim0) hindex (withHyp hlook _)
    have htl := headTransport InternalRawListRecursion.lookup expected index z (Fin.cons types Fin.elim0) hindex (withHyp htlook _)
    have heq := valueUnique InternalRawListRecursion.lookup entry headEntry (Fin.cons z (Fin.cons entries Fin.elim0)) hel
      (OriginalAllPositionContextDeleteBaseProof.lookupZero entries headEntry tailEntries (withHyp hentries _))
    have htq := valueUnique InternalRawListRecursion.lookup expected requested (Fin.cons z (Fin.cons types Fin.elim0)) htl
      (OriginalAllPositionContextDeleteBaseProof.lookupZero types requested tailTypes (withHyp htypes _))
    exact ValueProof.headPosition H gamma entry annotation child expected headEntry headAnnotation head requested heq htq
      (withHyp hr _) (withHyp hp _) (withHyp hq _) (withHyp hhead _)
  · intro beta j Theta pred hj hindex
    simp only [conjunctionRename,eqnRelabel,termAcceptedRename]
    have hcj := renameInto hc j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,OriginalTypedDecoderInternalScalarSyntaxProof.stepConsRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hcj
    have htypesj := renameInto htypes j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,OriginalTypedDecoderInternalScalarSyntaxProof.stepConsRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at htypesj
    have hentriesj := renameInto hentries j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,OriginalTypedDecoderInternalScalarSyntaxProof.stepConsRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hentriesj
    have haccj := renameInto hacc j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,OriginalTypedDecoderInternalScalarSyntaxProof.stepConsRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at haccj
    have hej := renameInto he j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,OriginalTypedDecoderInternalScalarSyntaxProof.stepConsRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hej
    have hlj := renameInto hl j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,OriginalTypedDecoderInternalScalarSyntaxProof.stepConsRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hlj
    have hbj := renameInto hb j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,OriginalTypedDecoderInternalScalarSyntaxProof.stepConsRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hbj
    have hlookj := renameInto hlook j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,OriginalTypedDecoderInternalScalarSyntaxProof.stepConsRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hlookj
    have htlookj := renameInto htlook j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,OriginalTypedDecoderInternalScalarSyntaxProof.stepConsRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at htlookj
    have hqj := renameInto hq j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,OriginalTypedDecoderInternalScalarSyntaxProof.stepConsRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hqj
    have ihj := renameInto ih j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,OriginalTypedDecoderInternalScalarSyntaxProof.stepConsRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at ihj
    have hlenj := renameInto hlen j Theta hj
    simp only [argumentsAcceptedRename,graph2Rename,graph3Rename,sucRelabel,lengthRename,OriginalTypedDecoderInternalScalarSyntaxProof.stepConsRename,Below,orderRename,InductionSyntaxProof.belowRawRename] at hlenj
    exact ValueProof.successorPosition H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j) (entries.relabel j) (count.relabel j) (index.relabel j) (entry.relabel j) (annotation.relabel j) (child.relabel j) (expected.relabel j) (headAnnotation.relabel j) (head.relabel j) (tail.relabel j) (requested.relabel j) (tailTypes.relabel j) (tailEntries.relabel j) (headEntry.relabel j) (tailCount.relabel j) pred hcj htypesj hentriesj haccj hej hlj hbj hlookj htlookj hqj ihj hlenj hindex

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.IndexProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.IndexProof
