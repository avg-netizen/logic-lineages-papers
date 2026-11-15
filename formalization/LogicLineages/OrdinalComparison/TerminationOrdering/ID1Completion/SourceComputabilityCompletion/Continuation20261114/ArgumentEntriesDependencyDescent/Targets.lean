module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontier.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBoundsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesDependencyDescent.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- Strict descent of every actual dependency, including all malformed raw
inputs. The conclusion is an internal arithmetic relation, not a native fact. -/
def InternalDependencyDescent : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw param deps child : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesFrontier.dependency deps raw param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)) →
  Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesDependencyDescent.Targets
