module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedAgreementProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.OriginalEntryPermutationFoldProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem actualFold (weight : Program 1) (left right leftEntries rightEntries ls rs : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (suc z) left right)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc leftEntries) left z)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc rightEntries) right z)))
    (hls : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) ls leftEntries)))
    (hrs : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) rs rightEntries))) :
    Nonempty (Derivation body Delta (eqn ls rs)) :=
  WeightedAgreementProof.permutationFold weight leftEntries rightEntries ls rs
    ((OriginalArgumentPermutation.InternalProof.internalSome body alpha Delta left right leftEntries rightEntries (suc z) hl hr).mp ha)
    hls hrs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.OriginalEntryPermutationFoldProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.OriginalEntryPermutationFoldProof
