module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverIterationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverIterationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalIndexedObserverIteration
open OriginalIndexedObserverDefinitions (ActualRange)
/-- Only iteration lifting of independently supplied INTERNAL step laws.
No chosen minimum, wrapper, sidecar or final traversal is asserted to meet
these suppliers. The actual parameter and cutoff stay fixed through repeat. -/
def ActualIndexedObserverIteration : Prop :=
  ∀ (data : Data), Closure data → Preservation data →
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out count input parameter mark cutoff : OTerm alpha),
  Nonempty (Derivation body Delta
    ((InternalParameterizedNumericIteration.repeatGraph (step data) out count input parameter ⊓
      (activeGraph data input parameter ⊓ ActualRange cutoff parameter)).imp
      ((markGraph data mark out parameter cutoff).iff (markGraph data mark input parameter cutoff))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverIterationTargets
