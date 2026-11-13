module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorErasureDefinitions
/-- Actual original erasure preserves source admission AND the full unchanged
evaluator relation. The common output after erasure is bound internally, never
assumed. Literal in-range lookup/delete selectors derive insertion geometry.
No transformed fold, target admission, evaluator equality after deletion,
selected-tuple replacement, or canonical Object equality is a premise. -/
def ActualErasureCongruence : Prop := ∀ (R : Program 2) (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (left right erasedLeft erasedRight parameter erasedParameter c gamma deleted count cutoff d : OTerm alpha),
 Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erasedParameter c deleted)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count gamma)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff count)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup d cutoff gamma)) →
 Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff gamma)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedLeft d cutoff left)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedRight d cutoff right)) →
 Nonempty (Derivation body Delta (AdmittedPair R H G M W erasedLeft erasedRight erasedParameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureTargets
