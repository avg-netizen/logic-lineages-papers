module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalStructuralKeyIteration

/-- Generic internal iterator supplier. The caller must prove preservation,
closure and validity; this contract alone does not prove structural leaf K-preservation. -/
def ActualOriginalStructuralKeySelectedIteration : Prop :=
  ∀ (data : Data), Validity data → Closure data → Preservation data →
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input parameter indicator : OTerm alpha),
  Nonempty (Derivation body Delta (activeGraph data input parameter)) →
  Nonempty (Derivation body Delta
    (graph2 (InternalOriginalUniformDescentSelection.fallbackRepresentative
      data.representative data.valid) out input parameter)) →
  Nonempty (Derivation body Delta
    ((markGraph data indicator out parameter).iff
      (markGraph data indicator input parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationTargets
