module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.EntryDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardObservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.EntryCoreProof
open Continuation20261116 Continuation20261116.OriginalExchangeBoundsPreservation
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Entry EntrySyntaxProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open Continuation20261114 Continuation20261115

theorem atRaw (n : Nat) (raw param entries value : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hf : Nonempty (Derivation body Delta (graph1 (Fold.weighted rankWeight) value entries)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n raw))) :
    Nonempty (Derivation body Delta (graph1 rawRankCode value raw)) := by
  apply OriginalEnumerationMembership.GuardObservationProof.cases n raw _ hg
  intro beta j Theta tag payload first second head hj hp _hfirst _hsecond _hhead ha
  rw [graph1Rename]
  have hgj := renameInto hg j Theta hj
  have hej := renameInto he j Theta hj
  have hfj := renameInto hf j Theta hj
  have ihj := renameInto ih j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hgj hfj
  simp only [graph2Rename,sucRelabel] at hej
  rw [belowRawRename] at ihj
  exact EntryDispatchProof.atAllowed n (raw.relabel j) (param.relabel j) (entries.relabel j) (value.relabel j)
    tag payload first second head hp hgj hej hfj ihj ha
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.EntryCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.EntryCoreProof
