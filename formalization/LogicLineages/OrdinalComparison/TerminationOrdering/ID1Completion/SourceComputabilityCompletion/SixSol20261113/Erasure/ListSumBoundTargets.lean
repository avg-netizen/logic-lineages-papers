module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListSumBoundDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListSumBoundTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
/-- Pairing bounds and actual internal list recursion establish this for EVERY
numeric list code, without a semantic/nonnegativity or desired-bound premise. -/
def ActualSumBound : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (raw sum : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 ListSumBoundDefinitions.sum sum raw)) →
 Nonempty (Derivation body Delta (InternalPairingSumBounds.weakBound sum raw))
/-- A genuine original in-range lookup is bounded by the actual identity-weight
sum. No native membership or already bounded-entry premise is supplied. -/
def ActualEntryBound : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (raw count index value sum : OTerm alpha),
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count raw)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.Below index count)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value index raw)) →
 Nonempty (Derivation body Delta (graph1 ListSumBoundDefinitions.sum sum raw)) →
 Nonempty (Derivation body Delta (InternalPairingSumBounds.weakBound value sum))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListSumBoundTargets
