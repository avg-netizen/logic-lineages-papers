module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
/-- L ≤ W+2, written internally as L < succ(succ(succ W)). The literal
annotated expansion and actual weight suffice on all raw jobs. This is a
branching bound, not runtime completion for malformed roles or return tags. -/
def ActualLengthBound : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (parent jobs count W : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs parent)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count jobs)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)) →
 Nonempty (Derivation body Delta (InternalOriginalOrderSyntaxProof.ltF count (suc (suc (suc W)))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthTargets
