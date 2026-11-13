module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherLeafTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherPreservationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Context.EvaluatorKeyPut
/-- Forward preservation by the literal selected OTHER leaf at the SAME NEW
evaluator-key tuple. Actual output-domain admission and original E relation are
conclusions, not minimum-hit, guard or canonical-fixedness assumptions. This is
not preservation by the whole lambda traversal or final application-only fold. -/
def ActualOtherPreservation : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input output parameter : OTerm alpha),
 let r := refined p H G W P
 let L := OriginalLambdaTraversalSelection.leaf r.base r.window
 Nonempty (Derivation body Delta (Domain p H G W input parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one input)) →
 Nonempty (Derivation body Delta (graph2 L output input parameter)) →
 Nonempty (Derivation body Delta
   (Domain p H G W output parameter ⊓ Same p H G W input output parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherPreservationTargets
