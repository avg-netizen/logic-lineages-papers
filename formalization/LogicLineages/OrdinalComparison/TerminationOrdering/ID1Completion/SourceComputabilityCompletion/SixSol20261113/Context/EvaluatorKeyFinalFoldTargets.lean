module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalFoldDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalFoldTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorKeyPut
/-- Actual original final-fold equality on NEW admitted evaluator fibres.
Final window/source/type conditions must be derived, not supplied. This is
not E preservation, fixedness, or Object erase/shift cancellation. -/
def ActualFinalFoldEquality : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (left right leftOut rightOut parameter : OTerm alpha),
 Nonempty (Derivation body Delta (Domain p H G W left parameter)) →
 Nonempty (Derivation body Delta (Domain p H G W right parameter)) →
 Nonempty (Derivation body Delta (Same p H G W left right parameter)) →
 Nonempty (Derivation body Delta (graph2 (EvaluatorKeyFinalFoldDefinitions.fold p H G W P) leftOut left parameter)) →
 Nonempty (Derivation body Delta (graph2 (EvaluatorKeyFinalFoldDefinitions.fold p H G W P) rightOut right parameter)) →
 Nonempty (Derivation body Delta (equal leftOut rightOut))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalFoldTargets
