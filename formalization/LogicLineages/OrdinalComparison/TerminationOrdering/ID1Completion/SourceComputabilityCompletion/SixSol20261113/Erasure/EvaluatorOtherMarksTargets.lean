module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorErasureDefinitions
/-- Original admitted variable rigidity from the unchanged evaluator relation.
Only the left actual packed variable tag is supplied; neither right tag nor
whole-input equality nor structural-key equality is an assumption. -/
def ActualVariableRigidity : Prop :=
 ∀ (R : Program 2) (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (left right parameter : OTerm alpha),
 Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 0) left)) →
 Nonempty (Derivation body Delta (equal left right))
/-- All five LITERAL original observer graph equivalences for an admitted
same-evaluator OTHER pair at the same parameter. OTHER includes variables and
bottom, not only ordinary/numbered heads. No structural-key, selected minimum,
rank equality, candidate guard, or canonical Object premise is supplied. -/
def ActualOtherMarks : Prop :=
 ∀ (R : Program 2) (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (left right parameter mark : OTerm alpha),
 Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one left)) →
 Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one right)) →
 Nonempty (Derivation body Delta (OriginalLambdaTraversalObserver.observations left right mark))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksTargets
