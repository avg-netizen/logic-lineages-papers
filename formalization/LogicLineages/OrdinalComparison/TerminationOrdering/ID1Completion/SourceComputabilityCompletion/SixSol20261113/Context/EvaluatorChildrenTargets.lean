module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SixSol20261113.Erasure.EvaluatorErasureDefinitions

/-- Inverse ordered application inheritance for the UNCHANGED computed evaluator.
ApplicationFields are actual tag/domain/type/function/argument selector graphs;
child admission and child evaluator agreement must be derived, not supplied.
This is not congruence of the existing canonical tuple or its class relation. -/
def ActualApplication : Prop :=
  ∀ (R : Program 2) (H G : Program 1) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right domain codomain fn arg otherFn otherArg parameter : OTerm alpha),
  Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)) →
  Nonempty (Derivation body Delta
    (OriginalLambdaTraversalInternal.ApplicationFields left domain codomain fn arg)) →
  Nonempty (Derivation body Delta
    (OriginalLambdaTraversalInternal.ApplicationFields right domain codomain otherFn otherArg)) →
  Nonempty (Derivation body Delta
    (AdmittedPair R H G M W fn otherFn parameter ⊓
     AdmittedPair R H G M W arg otherArg parameter))

/-- Inverse lambda inheritance at the ACTUAL common extended parameter.
The two LambdaFields retain actual childParameter graphs. No child source,
child evaluator output, base-R equality, or bound-zero erasure fact is assumed.
Once obtained, the existing erasure theorem can apply to this child pair at
cutoff zero, rather than trying to recover it from a shifted parent scan. -/
def ActualLambda : Prop :=
  ∀ (R : Program 2) (H G : Program 1) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right domain codomain child otherChild parameter childParameter : OTerm alpha),
  Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)) →
  Nonempty (Derivation body Delta
    (OriginalLambdaTraversalInternal.LambdaFields left domain codomain child parameter childParameter)) →
  Nonempty (Derivation body Delta
    (OriginalLambdaTraversalInternal.LambdaFields right domain codomain otherChild parameter childParameter)) →
  Nonempty (Derivation body Delta (AdmittedPair R H G M W child otherChild childParameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenTargets
