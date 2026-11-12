module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationInheritedTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalOriginalOrderSyntaxProof (ltF)
/-- Beyond the genuine raw-child prefix, annotation inherits actual role/type.
The branch decision is derived from arithmetic, not supplied as a guard graph. -/
def ActualInherited : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (index role typ raw arity annotation : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) arity raw)) →
 Nonempty (Derivation body Delta (ltF index arity).not) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotation role typ)) →
 Nonempty (Derivation body Delta (graph4 OriginalHereditaryAnnotatedExpansion.annotation annotation index role typ raw))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationInheritedTargets
