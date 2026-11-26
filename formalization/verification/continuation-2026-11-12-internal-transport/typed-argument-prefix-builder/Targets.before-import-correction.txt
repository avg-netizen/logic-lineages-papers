module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedArgumentPrefixBuilder OriginalTypedArgumentObservations
/-- Effective raw-prefix observation append, arbitrary actual packed cells and
raw suffix. This is not extraction from an original BASE permutation checker. -/
def ActualAppend : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (front suffix built parameter mappedValue suffixValue total : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 build built front suffix)) →
 Nonempty (Derivation body Delta (graph2 (mapped R) mappedValue front parameter)) →
 Nonempty (Derivation body Delta (graph2 (argumentObservations R) suffixValue suffix parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append total mappedValue suffixValue)) →
 Nonempty (Derivation body Delta (graph2 (argumentObservations R) total built parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderTargets
