module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyDomainClosureTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion EvaluatorKeyPut
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual active source/target/window admission descends to the lambda child
at its actual extended parameter. No child admission or calibration premise. -/
def ActualLambdaDomain : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (parent parameter domain codomain child childParameter : OTerm alpha),
 Nonempty (Derivation body Delta (Domain p H G W parent parameter)) →
 Nonempty (Derivation body Delta
   (OriginalLambdaTraversalInternal.LambdaFields parent domain codomain child parameter childParameter)) →
 Nonempty (Derivation body Delta (Domain p H G W child childParameter))
/-- Actual arbitrary-position deletion transports the SAME new tuple's active
domain. Literal insertion and both paired parameters preserve the outer context.
This is domain closure only, not C/erasure commutation or Object cancellation. -/
def ActualErasureDomain : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (packed out d cutoff gamma extended c oldParameter newParameter : OTerm alpha),
 Nonempty (Derivation body Delta (Domain p H G W packed oldParameter)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.Insert d cutoff gamma extended)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing oldParameter c extended)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParameter c gamma)) →
 Nonempty (Derivation body Delta
   (graph3 OriginalRawSyntaxTransport.erasePackedRaw out d cutoff packed)) →
 Nonempty (Derivation body Delta (Domain p H G W out newParameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyDomainClosureTargets
