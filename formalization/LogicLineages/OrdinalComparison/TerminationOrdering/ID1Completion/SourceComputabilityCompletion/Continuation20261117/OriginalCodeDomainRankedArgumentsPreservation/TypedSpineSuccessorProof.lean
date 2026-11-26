module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.GroundListCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineConsZeroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineSuccessorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport OriginalUniverseDecoderTransportSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open TypedSpineInvariant TypedSpineInvariantSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem source (n : Nat) (H : Program 1) (M W : Program 2)
    (raw typ head tail count types entry entries tailEntries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw typ head tail)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry typ head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode entries entry tailEntries)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail z)))
    (hgt : Nonempty (Derivation body Delta
      (graph1 Continuation20261116.OriginalConcreteHeadSignature.groundList types (suc count))))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context))) :
    Nonempty (Derivation body Delta (invariant H M W (suc count) entries gamma context)) := by
  apply GroundListCasesProof.successorCases count types _ hgt
  intro beta j Theta tailTypes hj htail ht
  have hc' := renameInto hc j Theta hj
  rw [graph3Rename] at hc'
  have hp' := renameInto hp j Theta hj
  have hl' := renameInto hl j Theta hj
  rw [graph2Rename] at hp' hl'
  have hg' := renameInto hg j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hg'
  have he' := renameInto he j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at he'
  have ih' := renameInto ih j Theta hj
  rw [TypedSpineInvariantSyntaxProof.belowRawRename] at ih'
  have ha' := renameInto ha j Theta hj
  rw [acceptedRename] at ha'
  simp only [invariantRename,sucRelabel]
  exact TypedSpineConsProof.source n H M W (raw.relabel j) (typ.relabel j) (head.relabel j)
    (tail.relabel j) (count.relabel j) (types.relabel j) tailTypes (entry.relabel j) (entries.relabel j)
    (tailEntries.relabel j) (gamma.relabel j) (context.relabel j) hc' ht hp' hl' hg' he' htail ih' ha'

theorem target (n : Nat) (H : Program 1) (M W : Program 2)
    (raw typ head tail count types entry entries tailEntries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw typ head tail)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry typ head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode entries entry tailEntries)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail z)))
    (hgt : Nonempty (Derivation body Delta
      (graph1 Continuation20261116.OriginalConcreteHeadSignature.groundList types (suc count))))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (ha : Nonempty (Derivation body Delta (invariant H M W (suc count) entries gamma context))) :
    Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context)) := by
  apply GroundListCasesProof.successorCases count types _ hgt
  intro beta j Theta tailTypes hj htail ht
  have hc' := renameInto hc j Theta hj
  rw [graph3Rename] at hc'
  have hp' := renameInto hp j Theta hj
  have hl' := renameInto hl j Theta hj
  rw [graph2Rename] at hp' hl'
  have hg' := renameInto hg j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hg'
  have he' := renameInto he j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at he'
  have ih' := renameInto ih j Theta hj
  rw [TypedSpineInvariantSyntaxProof.belowRawRename] at ih'
  have ha' := renameInto ha j Theta hj
  simp only [invariantRename,sucRelabel] at ha'
  rw [acceptedRename]
  exact TypedSpineConsProof.target n H M W (raw.relabel j) (typ.relabel j) (head.relabel j)
    (tail.relabel j) (count.relabel j) (types.relabel j) tailTypes (entry.relabel j) (entries.relabel j)
    (tailEntries.relabel j) (gamma.relabel j) (context.relabel j) hc' ht hp' hl' hg' he' htail ih' ha'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineSuccessorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineSuccessorProof
