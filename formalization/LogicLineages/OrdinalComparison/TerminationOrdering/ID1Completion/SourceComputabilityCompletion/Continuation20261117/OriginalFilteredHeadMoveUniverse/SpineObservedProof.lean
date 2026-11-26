module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.ExtractionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineObservedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport OriginalUniverseDecoderTransportSyntaxProof
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open SpineInvariant SpineInvariantSyntaxProof EntryFactsSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem sourceAtEntry (n : Nat) (H : Program 1) (M W : Program 2)
    (raw annotation head tail types entries gamma context tailEntries entry : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw annotation head tail)))
    (hex : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail z)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry annotation head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode entries entry tailEntries)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context))) :
    Nonempty (Derivation body Delta (EntryFacts.allGood H M W entries gamma context)) := by
  apply Continuation20261117.OriginalStructuralContextClosure.QueryProof.fields types _
  intro beta j Theta requested tailTypes hj hf
  rw [allGoodRename]
  have hc' := renameInto hc j Theta hj
  have hex' := renameInto hex j Theta hj
  have hg' := renameInto hg j Theta hj
  have ih' := renameInto ih j Theta hj
  have he' := renameInto he j Theta hj
  have hp' := renameInto hp j Theta hj
  have hl' := renameInto hl j Theta hj
  have ha' := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,sucRelabel,zRelabel,
    SpineInvariantSyntaxProof.belowRawRename,acceptedRename,plainRename,allGoodRename,conjunctionRename] at hc' hex' hg' ih' he' hp' hl' ha'
  exact SpineConsProof.source n H M W (raw.relabel j) (annotation.relabel j) (head.relabel j) (tail.relabel j) (types.relabel j) requested tailTypes (entry.relabel j) (entries.relabel j) (tailEntries.relabel j) (gamma.relabel j) (context.relabel j)
    hc' hf hp' hl' hg' he' ih' ha'

theorem targetAtEntry (n : Nat) (H : Program 1) (M W : Program 2)
    (raw annotation head tail types entries gamma context tailEntries entry : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw annotation head tail)))
    (hex : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail z)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry annotation head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode entries entry tailEntries)))
    (ha : Nonempty (Derivation body Delta (Plain H types raw gamma ⊓ EntryFacts.allGood H M W entries gamma context))) :
    Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context)) := by
  apply Continuation20261117.OriginalStructuralContextClosure.QueryProof.fields types _
  intro beta j Theta requested tailTypes hj hf
  rw [acceptedRename]
  have hc' := renameInto hc j Theta hj
  have hex' := renameInto hex j Theta hj
  have hg' := renameInto hg j Theta hj
  have ih' := renameInto ih j Theta hj
  have he' := renameInto he j Theta hj
  have hp' := renameInto hp j Theta hj
  have hl' := renameInto hl j Theta hj
  have ha' := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,sucRelabel,zRelabel,
    SpineInvariantSyntaxProof.belowRawRename,acceptedRename,plainRename,allGoodRename,conjunctionRename] at hc' hex' hg' ih' he' hp' hl' ha'
  exact SpineConsProof.target n H M W (raw.relabel j) (annotation.relabel j) (head.relabel j) (tail.relabel j) (types.relabel j) requested tailTypes (entry.relabel j) (entries.relabel j) (tailEntries.relabel j) (gamma.relabel j) (context.relabel j)
    hc' hf hp' hl' hg' he' ih' (andLeft ha') (andRight ha')

theorem sourceExtracted (n : Nat) (H : Program 1) (M W : Program 2)
    (raw annotation head tail types entries gamma context tailEntries : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw annotation head tail)))
    (hex : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail z)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context))) :
    Nonempty (Derivation body Delta (EntryFacts.allGood H M W entries gamma context)) := by
  apply LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.ExtractionConsCasesProof.atPositive raw annotation head tail entries tailEntries _ hc hex he
  intro beta j Theta entry hj hp hl
  rw [allGoodRename]
  have hc' := renameInto hc j Theta hj
  have hex' := renameInto hex j Theta hj
  have hg' := renameInto hg j Theta hj
  have ih' := renameInto ih j Theta hj
  have he' := renameInto he j Theta hj
  have ha' := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,sucRelabel,zRelabel,
    SpineInvariantSyntaxProof.belowRawRename,acceptedRename,plainRename,allGoodRename,conjunctionRename] at hc' hex' hg' ih' he' ha'
  exact sourceAtEntry n H M W (raw.relabel j) (annotation.relabel j) (head.relabel j) (tail.relabel j) (types.relabel j) (entries.relabel j) (gamma.relabel j) (context.relabel j) (tailEntries.relabel j) entry
    hc' hex' hg' ih' he' hp hl ha'

theorem targetExtracted (n : Nat) (H : Program 1) (M W : Program 2)
    (raw annotation head tail types entries gamma context tailEntries : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw annotation head tail)))
    (hex : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail z)))
    (ha : Nonempty (Derivation body Delta (Plain H types raw gamma ⊓ EntryFacts.allGood H M W entries gamma context))) :
    Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context)) := by
  apply LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.ExtractionConsCasesProof.atPositive raw annotation head tail entries tailEntries _ hc hex he
  intro beta j Theta entry hj hp hl
  rw [acceptedRename]
  have hc' := renameInto hc j Theta hj
  have hex' := renameInto hex j Theta hj
  have hg' := renameInto hg j Theta hj
  have ih' := renameInto ih j Theta hj
  have he' := renameInto he j Theta hj
  have ha' := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,sucRelabel,zRelabel,
    SpineInvariantSyntaxProof.belowRawRename,acceptedRename,plainRename,allGoodRename,conjunctionRename] at hc' hex' hg' ih' he' ha'
  exact targetAtEntry n H M W (raw.relabel j) (annotation.relabel j) (head.relabel j) (tail.relabel j) (types.relabel j) (entries.relabel j) (gamma.relabel j) (context.relabel j) (tailEntries.relabel j) entry
    hc' hex' hg' ih' he' hp hl ha'

theorem sourceCons (n : Nat) (H : Program 1) (M W : Program 2)
    (raw annotation head tail types entries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw annotation head tail)))
    (hex : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context))) :
    Nonempty (Derivation body Delta (EntryFacts.allGood H M W entries gamma context)) := by
  apply ExtractionProof.tailCases raw annotation head tail entries _ hc hex
  intro beta j Theta tailEntries hj he
  rw [allGoodRename]
  have hc' := renameInto hc j Theta hj
  have hex' := renameInto hex j Theta hj
  have hg' := renameInto hg j Theta hj
  have ih' := renameInto ih j Theta hj
  have ha' := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,sucRelabel,zRelabel,
    SpineInvariantSyntaxProof.belowRawRename,acceptedRename,plainRename,allGoodRename,conjunctionRename] at hc' hex' hg' ih' ha'
  exact sourceExtracted n H M W (raw.relabel j) (annotation.relabel j) (head.relabel j) (tail.relabel j) (types.relabel j) (entries.relabel j) (gamma.relabel j) (context.relabel j) tailEntries
    hc' hex' hg' ih' he ha'

theorem targetCons (n : Nat) (H : Program 1) (M W : Program 2)
    (raw annotation head tail types entries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw annotation head tail)))
    (hex : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (ha : Nonempty (Derivation body Delta (Plain H types raw gamma ⊓ EntryFacts.allGood H M W entries gamma context))) :
    Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context)) := by
  apply ExtractionProof.tailCases raw annotation head tail entries _ hc hex
  intro beta j Theta tailEntries hj he
  rw [acceptedRename]
  have hc' := renameInto hc j Theta hj
  have hex' := renameInto hex j Theta hj
  have hg' := renameInto hg j Theta hj
  have ih' := renameInto ih j Theta hj
  have ha' := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,sucRelabel,zRelabel,
    SpineInvariantSyntaxProof.belowRawRename,acceptedRename,plainRename,allGoodRename,conjunctionRename] at hc' hex' hg' ih' ha'
  exact targetExtracted n H M W (raw.relabel j) (annotation.relabel j) (head.relabel j) (tail.relabel j) (types.relabel j) (entries.relabel j) (gamma.relabel j) (context.relabel j) tailEntries
    hc' hex' hg' ih' he ha'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineObservedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineObservedProof
