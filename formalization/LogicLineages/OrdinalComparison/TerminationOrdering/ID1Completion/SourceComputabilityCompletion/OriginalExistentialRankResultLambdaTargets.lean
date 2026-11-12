module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultLambdaTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalExistentialRankResultDefinitions
/-- Arbitrary ORIGINAL child rank witnesses lift through the same literal lambda
constructor. Actual parent ranks are derived, not assumed. No certificate law. -/
def ActualLambdaLift : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (input out d e child childOut : OTerm alpha),
 Nonempty (Derivation body Delta ((graph3 OriginalLambdaConstructor.constructor input d e child ⊓
  (graph3 OriginalLambdaConstructor.constructor out d e childOut ⊓ RankWitness child childOut)).imp
    (RankWitness input out)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultLambdaTargets
