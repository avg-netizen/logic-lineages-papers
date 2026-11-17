module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineInvariantProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.EntryFactsTransferProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.OptionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.PermutationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andIntro)
open OriginalUniverseDecoderTransport OriginalUniverseDecoderTransportSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open SpineInvariant SpineInvariantSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem withLists (n : Nat) (H : Program 1) (M W : Program 2)
    (sourceTypes targetTypes base target left right gamma context : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) base)))
    (ht : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) target)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true sourceTypes base gamma context)))
    (hp : Nonempty (Derivation body Delta (Plain H targetTypes target gamma)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc left) base z)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc right) target z)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentCountComparison.permutation (suc z) left right))) :
    Nonempty (Derivation body Delta (Accepted H M W true targetTypes target gamma context)) := by
  have hi := SpineInvariantProof.source n H M W base sourceTypes left gamma context (andIntro hb hl) ha
  have hagree := OriginalArgumentPermutationClosure.AllQueryProof.permutationAgreement left right he
  have hj := EntryFactsTransferProof.transferAll H M W left right gamma context hagree hi
  exact SpineInvariantProof.target n H M W target targetTypes right gamma context (andIntro ht hr) hp hj

theorem preserved (n : Nat) (H : Program 1) (M W : Program 2)
    (sourceTypes targetTypes base target gamma context : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) base)))
    (ht : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) target)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true sourceTypes base gamma context)))
    (hplain : Nonempty (Derivation body Delta (Plain H targetTypes target gamma)))
    (hp : Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (suc z) base target))) :
    Nonempty (Derivation body Delta (Accepted H M W true targetTypes target gamma context)) := by
  apply OriginalArgumentPermutationClosure.OptionProof.bothCases base target _ hp
  intro beta j Theta left right hj hl hr hperm
  have hb' := renameInto hb j Theta hj
  have ht' := renameInto ht j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hb' ht'
  have ha' := renameInto ha j Theta hj
  rw [acceptedRename] at ha'
  have hp' := renameInto hplain j Theta hj
  rw [plainRename] at hp'
  rw [acceptedRename]
  exact withLists n H M W (sourceTypes.relabel j) (targetTypes.relabel j)
    (base.relabel j) (target.relabel j) left right (gamma.relabel j) (context.relabel j)
    hb' ht' ha' hp' hl hr hperm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.PermutationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.PermutationProof
