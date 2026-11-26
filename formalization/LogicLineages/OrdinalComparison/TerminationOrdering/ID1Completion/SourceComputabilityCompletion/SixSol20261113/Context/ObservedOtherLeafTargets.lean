module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedNormalizationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherLeafTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Equality of actual selected OTHER-leaf outputs at the SAME observed tuple.
Only initial domain, literal accepted relation, actual OTHER tags and leaf
runs are premises. Candidate domain, guards, rank/type agreement, minimum
agreement and bounded normalization must all be proved. This is not full
traversal congruence, arbitrary constructor inheritance, or Object fixedness. -/
def ActualOtherLeafEquality : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (left right leftOut rightOut parameter : OTerm alpha),
 let q := ObservedNormalizationTargets.preminimum p H G W
 let r := Erasure.ObservedPut.refined p H G W P
 let L := OriginalLambdaTraversalSelection.leaf r.base r.window
 Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain q H G W left parameter)) →
 Nonempty (Derivation body Delta (OriginalAllPositionMinimumCoherenceTargets.Accepted q H G W P left right parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one left)) →
 Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one right)) →
 Nonempty (Derivation body Delta (graph2 L leftOut left parameter)) →
 Nonempty (Derivation body Delta (graph2 L rightOut right parameter)) →
 Nonempty (Derivation body Delta (equal leftOut rightOut))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherLeafTargets
