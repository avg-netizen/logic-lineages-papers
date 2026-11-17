module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineTaggedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.ExtractionConsCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineAuxiliary.GuardPairProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineChoicePreservingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineNilProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport OriginalUniverseDecoderTransportSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open SpineInvariant SpineInvariantSyntaxProof EntryFactsSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)

open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)


theorem source (n : Nat) (H : Program 1) (M W : Program 2)
    (raw types entries tag payload first second head gamma context : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second raw)))
    (hex : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (hallowed : Nonempty (Derivation body Delta
      (OriginalCodeValidityConstructors.Targets.allowed n tag payload first second head)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context))) :
    Nonempty (Derivation body Delta (EntryFacts.allGood H M W entries gamma context)) := by
  apply LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineChoicePreservingProof.eliminate n raw z entries tag payload first second head _ hp hex hallowed
  · let C := eqn tag (numeral 6) ⊓ eqn payload z
    have hh : Nonempty (Derivation body (C :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hc := LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineAuxiliary.GuardPairProof.nil raw tag payload (withHyp hp C) (andLeft hh) (andRight hh)
    obtain ⟨h⟩ := SpineNilProof.source H M W raw entries gamma context hc
      (withHyp hex C)
    exact ⟨Derivation.implicationIntroduction h⟩
  · let C := eqn tag (numeral 7) ⊓ (graph1 (OriginalCodeValidityGuard.check n) (suc z) first ⊓
      graph1 (OriginalCodeValidityGuard.check n) (suc z) second)
    have hh : Nonempty (Derivation body (C :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ht := LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineAuxiliary.GuardPairProof.tagLiteral raw tag payload 7 (withHyp hp C) (andLeft hh)
    obtain ⟨h⟩ := SpineTaggedProof.source n H M W raw types entries second gamma context
      ht (withHyp hs C) (withHyp hex C) (andRight (andRight hh)) (withHyp ih C) (withHyp ha C)
    exact ⟨Derivation.implicationIntroduction h⟩

theorem target (n : Nat) (H : Program 1) (M W : Program 2)
    (raw types entries tag payload first second head gamma context : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second raw)))
    (hex : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (hallowed : Nonempty (Derivation body Delta
      (OriginalCodeValidityConstructors.Targets.allowed n tag payload first second head)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (ha : Nonempty (Derivation body Delta (Plain H types raw gamma ⊓ EntryFacts.allGood H M W entries gamma context))) :
    Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context)) := by
  apply LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineChoicePreservingProof.eliminate n raw z entries tag payload first second head _ hp hex hallowed
  · let C := eqn tag (numeral 6) ⊓ eqn payload z
    have hh : Nonempty (Derivation body (C :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hc := LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineAuxiliary.GuardPairProof.nil raw tag payload (withHyp hp C) (andLeft hh) (andRight hh)
    obtain ⟨h⟩ := SpineNilProof.target H M W raw types gamma context hc (andLeft (withHyp ha C))
    exact ⟨Derivation.implicationIntroduction h⟩
  · let C := eqn tag (numeral 7) ⊓ (graph1 (OriginalCodeValidityGuard.check n) (suc z) first ⊓
      graph1 (OriginalCodeValidityGuard.check n) (suc z) second)
    have hh : Nonempty (Derivation body (C :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ht := LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineAuxiliary.GuardPairProof.tagLiteral raw tag payload 7 (withHyp hp C) (andLeft hh)
    obtain ⟨h⟩ := SpineTaggedProof.target n H M W raw types entries second gamma context
      ht (withHyp hs C) (withHyp hex C) (andRight (andRight hh)) (withHyp ih C) (withHyp ha C)
    exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineDispatchProof
