module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.UnsortedChildDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.UnsortedChildTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
/-- Actual sort and original in-range INPUT lookup imply entry≤OUTPUT code.
No supplied permutation, sorted membership, sum value, or desired bound. -/
def ActualSortedEntryBound : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (raw sorted count index value : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 OriginalNumericListSort.sort sorted raw)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count raw)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.Below index count)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value index raw)) →
 Nonempty (Derivation body Delta (InternalPairingSumBounds.weakBound value sorted))
/-- Genuine UNSORTED original BASE child descends below its full evaluator
code. Literal sort output is the SAME row selected from the original positive
tag4/tag5 recursive-root payload. No native membership oracle or bound premise. -/
def ActualUnsortedChildDescent : Prop := ∀ (kind : UnsortedChildDefinitions.BaseSlot)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (out base inner recursive rows payload raw sorted count index typed typ child : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out base inner)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner recursive rows)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing recursive (numeral (UnsortedChildDefinitions.tag kind)) payload)) →
 Nonempty (Derivation body Delta (graph1 (ObservationDescentDefinitions.select
   (ObservationDescentDefinitions.listPath (UnsortedChildDefinitions.slot kind))) sorted payload)) →
 Nonempty (Derivation body Delta (graph1 OriginalNumericListSort.sort sorted raw)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count raw)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.Below index count)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup typed index raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ child)) →
 Nonempty (Derivation body Delta (InternalLessThan.strictLess child out))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.UnsortedChildTargets
