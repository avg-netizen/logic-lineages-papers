module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaStoppedTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Genuine internal stopped-state acceptance for every original raw path,
not just the empty certificate and not native evaluation reflection. -/
def ActualStoppedGuard : Prop := ∀ (oldStep : Program 4)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter : OTerm alpha),
 Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.stop InternalOriginalStepGuard.one s t cert parameter)) →
 Nonempty (Derivation body Delta (graph4 (OriginalHereditaryLambda.guard oldStep) InternalOriginalStepGuard.one s t cert parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaStoppedTargets
