module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherLeafTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorKeyPut
/-- Literal selected OTHER-leaf extensionality at the explicitly NEW tuple.
Both original domain admissions and a common actual evaluator output are
supplied, not candidate guards, rank equality, minimum equality or fixedness.
No full traversal congruence or Object cancellation is asserted. -/
def ActualOtherLeafEquality : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (left right leftOut rightOut parameter : OTerm alpha),
 let r := refined p H G W P
 let L := OriginalLambdaTraversalSelection.leaf r.base r.window
 Nonempty (Derivation body Delta (Domain p H G W left parameter)) →
 Nonempty (Derivation body Delta (Domain p H G W right parameter)) →
 Nonempty (Derivation body Delta (Same p H G W left right parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one left)) →
 Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one right)) →
 Nonempty (Derivation body Delta (graph2 L leftOut left parameter)) →
 Nonempty (Derivation body Delta (graph2 L rightOut right parameter)) →
 Nonempty (Derivation body Delta (equal leftOut rightOut))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherLeafTargets
