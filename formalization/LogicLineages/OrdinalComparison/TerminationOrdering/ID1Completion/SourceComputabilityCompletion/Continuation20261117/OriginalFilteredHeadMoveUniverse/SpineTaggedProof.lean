module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineObservedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.ExtractionConsCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineAuxiliary.GuardPairProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineTaggedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport OriginalUniverseDecoderTransportSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open SpineInvariant SpineInvariantSyntaxProof EntryFactsSyntaxProof
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)

open InternalApplicationStepPeelSupportProof (andRight)
open SourceComputabilityFormulaSupportProof (numeral)

theorem source (n : Nat) (H : Program 1) (M W : Program 2)
    (raw types entries second gamma context : OTerm alpha)
    (htag : Nonempty (Derivation body Delta (graph1 rawTag (numeral 7) raw)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second raw)))
    (hex : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) second)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context))) :
    Nonempty (Derivation body Delta (EntryFacts.allGood H M W entries gamma context)) := by
  apply OriginalRawSyntaxTransportInternalParserBinaryProof.consCases raw _ htag
  intro beta j Theta typ head tail hj hc
  have hs' := renameInto hs j Theta hj
  rw [graph1Rename] at hs'
  have hg' := renameInto hg j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hg'
  have hf := OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof.consFields (raw.relabel j) typ head tail hc
  have heq := valueUnique (secondOf (.projection 0)) (second.relabel j) tail ![raw.relabel j]
    hs' (andRight (andRight hf))
  have htail := headTransport (OriginalCodeValidityGuard.check n) (suc z) (second.relabel j) tail Fin.elim0 heq hg'
  have hex' := renameInto hex j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hex'
  have ih' := renameInto ih j Theta hj
  rw [SpineInvariantSyntaxProof.belowRawRename] at ih'
  have ha' := renameInto ha j Theta hj
  rw [acceptedRename] at ha'
  rw [allGoodRename]
  exact SpineObservedProof.sourceCons n H M W (raw.relabel j) typ head tail 
    (types.relabel j) (entries.relabel j) (gamma.relabel j) (context.relabel j) hc hex' htail ih' ha'

theorem target (n : Nat) (H : Program 1) (M W : Program 2)
    (raw types entries second gamma context : OTerm alpha)
    (htag : Nonempty (Derivation body Delta (graph1 rawTag (numeral 7) raw)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second raw)))
    (hex : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) second)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (ha : Nonempty (Derivation body Delta (Plain H types raw gamma ⊓ EntryFacts.allGood H M W entries gamma context))) :
    Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context)) := by
  apply OriginalRawSyntaxTransportInternalParserBinaryProof.consCases raw _ htag
  intro beta j Theta typ head tail hj hc
  have hs' := renameInto hs j Theta hj
  rw [graph1Rename] at hs'
  have hg' := renameInto hg j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hg'
  have hf := OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof.consFields (raw.relabel j) typ head tail hc
  have heq := valueUnique (secondOf (.projection 0)) (second.relabel j) tail ![raw.relabel j]
    hs' (andRight (andRight hf))
  have htail := headTransport (OriginalCodeValidityGuard.check n) (suc z) (second.relabel j) tail Fin.elim0 heq hg'
  have hex' := renameInto hex j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hex'
  have ih' := renameInto ih j Theta hj
  rw [SpineInvariantSyntaxProof.belowRawRename] at ih'
  have ha' := renameInto ha j Theta hj
  simp only [conjunctionRename,plainRename,allGoodRename] at ha'
  rw [acceptedRename]
  exact SpineObservedProof.targetCons n H M W (raw.relabel j) typ head tail 
    (types.relabel j) (entries.relabel j) (gamma.relabel j) (context.relabel j) hc hex' htail ih' ha'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineTaggedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineTaggedProof
