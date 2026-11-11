module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonicalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonicalSelectionProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative OriginalLambdaCanonical
open OriginalLambdaCanonicalTargets OriginalLambdaCanonicalSupportProof

theorem actualOriginalLambdaCanonicalBodySelection : ActualOriginalLambdaCanonicalBodySelection := by
  intro n arity symbols S hc Gamma sigma tau body hlambda
  obtain ⟨body',hbody',hmem,he,hfixed,hl⟩ :=
    typedLambdaRepresentative n arity symbols S hc Gamma sigma tau body hlambda
  refine ⟨body',hbody',hmem,he,hfixed,hl,?_,?_⟩
  · rw [hl,he]
    simpa only [lambdaPacked] using
      (OriginalLambdaConstructorEvaluationProof.actualOriginalLambdaConstructorTypedCalibration
        n arity Gamma sigma tau body').2.2.2
  · rw [he,hl]
    simpa only [lambdaPacked] using
      (OriginalLambdaConstructorEvaluationProof.actualOriginalLambdaConstructorTypedCalibration
        n arity Gamma sigma tau body').1

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonicalSelectionProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonicalSelectionProof
