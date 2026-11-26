module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineCountCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.ExtractionConsCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineExtractedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport OriginalUniverseDecoderTransportSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open TypedSpineInvariant TypedSpineInvariantSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem source (n : Nat) (H : Program 1) (M W : Program 2)
    (raw typ head tail count types entries tailEntries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw typ head tail)))
    (hex : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail z)))
    (hgt : Nonempty (Derivation body Delta
      (graph1 Continuation20261116.OriginalConcreteHeadSignature.groundList types count)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context))) :
    Nonempty (Derivation body Delta (invariant H M W count entries gamma context)) := by
  apply ExtractionConsCasesProof.atPositive raw typ head tail entries tailEntries _ hc hex he
  intro beta j Theta entry hj hp hl
  have hc' := renameInto hc j Theta hj
  rw [graph3Rename] at hc'
  have hg' := renameInto hg j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hg'
  have he' := renameInto he j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at he'
  have hgt' := renameInto hgt j Theta hj
  rw [graph1Rename] at hgt'
  have ih' := renameInto ih j Theta hj
  rw [belowRawRename] at ih'
  have ha' := renameInto ha j Theta hj
  rw [acceptedRename] at ha'
  rw [invariantRename]
  exact TypedSpineCountCasesProof.source n H M W (raw.relabel j) (typ.relabel j) (head.relabel j)
    (tail.relabel j) (count.relabel j) (types.relabel j) entry (entries.relabel j) (tailEntries.relabel j)
    (gamma.relabel j) (context.relabel j) hc' hp hl hg' he' hgt' ih' ha'

theorem target (n : Nat) (H : Program 1) (M W : Program 2)
    (raw typ head tail count types entries tailEntries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw typ head tail)))
    (hex : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail z)))
    (hgt : Nonempty (Derivation body Delta
      (graph1 Continuation20261116.OriginalConcreteHeadSignature.groundList types count)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (ha : Nonempty (Derivation body Delta (invariant H M W count entries gamma context))) :
    Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context)) := by
  apply ExtractionConsCasesProof.atPositive raw typ head tail entries tailEntries _ hc hex he
  intro beta j Theta entry hj hp hl
  have hc' := renameInto hc j Theta hj
  rw [graph3Rename] at hc'
  have hg' := renameInto hg j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hg'
  have he' := renameInto he j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at he'
  have hgt' := renameInto hgt j Theta hj
  rw [graph1Rename] at hgt'
  have ih' := renameInto ih j Theta hj
  rw [belowRawRename] at ih'
  have ha' := renameInto ha j Theta hj
  rw [invariantRename] at ha'
  rw [acceptedRename]
  exact TypedSpineCountCasesProof.target n H M W (raw.relabel j) (typ.relabel j) (head.relabel j)
    (tail.relabel j) (count.relabel j) (types.relabel j) entry (entries.relabel j) (tailEntries.relabel j)
    (gamma.relabel j) (context.relabel j) hc' hp hl hg' he' hgt' ih' ha'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineExtractedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineExtractedProof
