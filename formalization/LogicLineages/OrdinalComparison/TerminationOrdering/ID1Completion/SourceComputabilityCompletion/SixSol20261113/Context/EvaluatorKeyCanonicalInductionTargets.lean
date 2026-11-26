module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalInductionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorKeyCanonicalInductionDefinitions
/-- Local induction step only: smaller-left-payload IH explicit. -/
def ActualStep : Prop := ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (payload left right leftOut rightOut parameter : OTerm alpha),
 Nonempty (Derivation body Delta (belowPayload p H G W P payload)) →
 Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload left)) →
 Nonempty (Derivation body Delta (Premises p H G W P left right leftOut rightOut parameter)) →
 Nonempty (Derivation body Delta (equal leftOut rightOut))
/-- The internal strong induction closes the entire IH without an external bound. -/
def ActualAll : Prop := ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (payload : OTerm alpha),
 Nonempty (Derivation body Delta (atPayload p H G W P payload))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalInductionTargets
