module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyDomainClosureTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyApplicationDomainTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open UniformCertificateCompletion EvaluatorKeyPut
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Original source/target/window admission of BOTH actual application children
at the SAME runtime parameter, for the explicitly new evaluator-aware tuple.
Neither child source nor child window nor E-equality is a supplied premise. -/
def ActualApplicationDomain : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (parent parameter domain codomain fn arg : OTerm alpha),
 Nonempty (Derivation body Delta (Domain p H G W parent parameter)) →
 Nonempty (Derivation body Delta
   (OriginalLambdaTraversalInternal.ApplicationFields parent domain codomain fn arg)) →
 Nonempty (Derivation body Delta
   (Domain p H G W fn parameter ⊓ Domain p H G W arg parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyApplicationDomainTargets
