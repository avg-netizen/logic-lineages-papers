module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyMinimumTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorKeyPut
/-- SAME explicitly new evaluator-aware bounded minimum. Independent seed bounds
are permitted; only original domain admissions, common actual E output and
actual minimum computations are supplied. No full-fold equality is claimed. -/
def ActualMinimumEquality : Prop :=
  ∀ (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right out otherOut parameter : OTerm alpha),
  Nonempty (Derivation body Delta (Domain p H G W left parameter)) →
  Nonempty (Derivation body Delta (Domain p H G W right parameter)) →
  Nonempty (Derivation body Delta (Same p H G W left right parameter)) →
  Nonempty (Derivation body Delta
    (graph2 (minimumInputs p H G W P).base.oldRepresentative out left parameter)) →
  Nonempty (Derivation body Delta
    (graph2 (minimumInputs p H G W P).base.oldRepresentative otherOut right parameter)) →
  Nonempty (Derivation body Delta (equal out otherOut))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyMinimumTargets
