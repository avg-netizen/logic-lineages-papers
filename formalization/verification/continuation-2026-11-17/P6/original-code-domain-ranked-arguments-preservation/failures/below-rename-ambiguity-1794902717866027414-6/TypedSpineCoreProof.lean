module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.ExtractionConsCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineAuxiliary.GuardPairProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineChoicePreservingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineAuxiliary.GuardObservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport OriginalUniverseDecoderTransportSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open TypedSpineInvariant TypedSpineInvariantSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)

open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)



theorem source (n : Nat) (H : Program 1) (M W : Program 2)
    (raw count types entries gamma context : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (domain n raw count types entries)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context))) :
    Nonempty (Derivation body Delta (invariant H M W count entries gamma context)) := by
  apply SpineAuxiliary.GuardObservationProof.cases n raw _ (andLeft hd)
  intro beta j Theta tag payload first second head hj hp _hf hs _hh hallowed
  have hd' := renameInto hd j Theta hj
  rw [domainRename] at hd'
  have ih' := renameInto ih j Theta hj
  rw [belowRawRename] at ih'
  have ha' := renameInto ha j Theta hj
  rw [acceptedRename] at ha'
  rw [invariantRename]
  exact TypedSpineDispatchProof.source n H M W (raw.relabel j) (count.relabel j) (types.relabel j)
    (entries.relabel j) tag payload first second head (gamma.relabel j) (context.relabel j)
    hp hs (andLeft (andRight hd')) hallowed (andRight (andRight hd')) ih' ha'

theorem target (n : Nat) (H : Program 1) (M W : Program 2)
    (raw count types entries gamma context : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (domain n raw count types entries)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (ha : Nonempty (Derivation body Delta (invariant H M W count entries gamma context))) :
    Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context)) := by
  apply SpineAuxiliary.GuardObservationProof.cases n raw _ (andLeft hd)
  intro beta j Theta tag payload first second head hj hp _hf hs _hh hallowed
  have hd' := renameInto hd j Theta hj
  rw [domainRename] at hd'
  have ih' := renameInto ih j Theta hj
  rw [belowRawRename] at ih'
  have ha' := renameInto ha j Theta hj
  rw [invariantRename] at ha'
  rw [acceptedRename]
  exact TypedSpineDispatchProof.target n H M W (raw.relabel j) (count.relabel j) (types.relabel j)
    (entries.relabel j) tag payload first second head (gamma.relabel j) (context.relabel j)
    hp hs (andLeft (andRight hd')) hallowed (andRight (andRight hd')) ih' ha'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineCoreProof
