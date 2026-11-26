module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open ObservationDescentDefinitions
/-- Every actual finite original-unpair selector is weakly bounded by its input. -/
def ActualSelectorBound : Prop := ∀ (path : List Bool) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha)) (input selected : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 (select path) selected input)) →
 Nonempty (Derivation body Delta (InternalPairingSumBounds.weakBound selected input))
/-- Genuine in-range membership in the unchanged numeric list codec. In
particular this applies to the actual SORTED BASE row, not native membership. -/
def ActualTypedLookupDescent : Prop := ∀ (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha)) (list count index typed typ child : OTerm alpha),
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count list)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.Below index count)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup typed index list)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ child)) →
 Nonempty (Derivation body Delta (InternalLessThan.strictLess child list))
/-- Exact lambda/function/argument codecs under the original E envelope. This
uses a positive constructor tag; it does NOT assert that code zero has rank0.
An admitted variable can have E-code zero and the proposed decoder base is1. -/
def ActualDirectChildDescent : Prop := ∀ (slot : DirectSlot) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha)) (out base inner recursive rows payload typed typ child : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out base inner)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner recursive rows)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing recursive (numeral (directTag slot)) payload)) →
 Nonempty (Derivation body Delta (graph1 (select (directPath slot)) typed payload)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ child)) →
 Nonempty (Derivation body Delta (InternalLessThan.strictLess child out))
/-- In-range typed entries of the literal stored BASE/extras row are strictly
smaller than the containing evaluator code. Sorting is not replaced by a
membership oracle: the lookup is in the actual row selected from that code.
This theorem makes no source-rank/evaluator equivalence assumption. -/
def ActualStoredChildDescent : Prop := ∀ (slot : ListSlot) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha))
 (out base inner recursive rows tag payload list count index typed typ child : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out base inner)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner recursive rows)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing recursive tag payload)) →
 Nonempty (Derivation body Delta (graph1 (select (listPath slot)) list payload)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count list)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.Below index count)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup typed index list)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ child)) →
 Nonempty (Derivation body Delta (InternalLessThan.strictLess child out))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentTargets
