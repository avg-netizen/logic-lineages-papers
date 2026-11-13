module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorKeyPut
/-- Extensionality of literal original C at the explicitly NEW refined tuple
on original source/domain-admitted fibres of the unchanged hereditary evaluator.
No child relation, rebuilt output equality, fixedness, or E-preservation premise.
This is not the finalData application fold or Object cancellation. -/
def ActualCanonicalEquality : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (left right leftOut rightOut parameter : OTerm alpha),
 let r := refined p H G W P
 let C := OriginalLambdaTraversalSelection.canonical r.base r.window
 Nonempty (Derivation body Delta (Domain p H G W left parameter)) →
 Nonempty (Derivation body Delta (Domain p H G W right parameter)) →
 Nonempty (Derivation body Delta (Same p H G W left right parameter)) →
 Nonempty (Derivation body Delta (graph2 C leftOut left parameter)) →
 Nonempty (Derivation body Delta (graph2 C rightOut right parameter)) →
 Nonempty (Derivation body Delta (equal leftOut rightOut))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalTargets
