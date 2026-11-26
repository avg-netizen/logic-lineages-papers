module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineInvariantBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.EntryFactsHeadProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.EntryCheckProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderTransportLogicalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open SpineInvariant SpineInvariantBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem source (n : Nat) (H : Program 1) (M W : Program 2)
    (raw annotation head tail types requested tailTypes entry entries tailEntries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw annotation head tail)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry annotation head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode entries entry tailEntries)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail z)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context))) :
    Nonempty (Derivation body Delta (EntryFacts.allGood H M W entries gamma context)) := by
  have hsmall := andRight (Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof.cons raw annotation head tail hc)
  obtain ⟨hr⟩ := belowRawApply n H M W raw tail tailTypes tailEntries gamma context ih hsmall
  obtain ⟨hd⟩ := andIntro hg he
  have hb := Derivation.implicationElimination hr hd
  have h := iffForward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.consIff H M W
    raw annotation head tail types requested tailTypes gamma context hc hf) ha
  obtain ⟨ht⟩ := andRight (andRight (andRight h))
  have htail : Nonempty (Derivation body Delta (EntryFacts.allGood H M W tailEntries gamma context)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hb) ht⟩
  have hhead := (EntryCheckProof.entryIff H M W entry annotation head gamma context hp).mpr
    (andLeft (andRight (andRight h)))
  exact EntryFactsConstructorProof.consAll H M W entries entry tailEntries gamma context hl hhead htail

theorem target (n : Nat) (H : Program 1) (M W : Program 2)
    (raw annotation head tail types requested tailTypes entry entries tailEntries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw annotation head tail)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry annotation head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode entries entry tailEntries)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail z)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (ha : Nonempty (Derivation body Delta (Plain H types raw gamma)))
    (hall : Nonempty (Derivation body Delta (EntryFacts.allGood H M W entries gamma context))) :
    Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context)) := by
  have hsmall := andRight (Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof.cons raw annotation head tail hc)
  obtain ⟨hr⟩ := belowRawApply n H M W raw tail tailTypes tailEntries gamma context ih hsmall
  obtain ⟨hd⟩ := andIntro hg he
  have hb := Derivation.implicationElimination hr hd
  have h := iffForward (OriginalTypedDecoderTransportBinaryAcceptanceProof.consIff H
    raw annotation head tail types requested tailTypes gamma hc hf) ha
  have ht := EntryFactsHeadProof.tailAll H M W entries entry tailEntries gamma context hl hall
  obtain ⟨hin⟩ := andIntro (andRight (andRight (andRight h))) ht
  have htail : Nonempty (Derivation body Delta (Accepted H M W true tailTypes tail gamma context)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hb) hin⟩
  have hhead := (EntryCheckProof.entryIff H M W entry annotation head gamma context hp).mp
    (EntryFactsHeadProof.headAccepted H M W entries entry tailEntries gamma context hl hall)
  exact iffBackward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.consIff H M W
    raw annotation head tail types requested tailTypes gamma context hc hf)
    (andIntro (andLeft h) (andIntro (andLeft (andRight h)) (andIntro hhead htail)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineConsProof
