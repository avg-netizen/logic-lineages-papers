module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardProof
open InternalOriginalUniformStepGuard InternalOriginalUniformStepGuardTargets
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualParameterizedGuardedStepAtSourceTag : ActualParameterizedGuardedStepAtSourceTag :=
  InternalOriginalUniformStepGuardSupportProof.actualParameterizedGuardedStepAtSourceTag

theorem actualParameterizedCanonicalStepAtSourceTag : ActualParameterizedCanonicalStepAtSourceTag :=
  InternalOriginalUniformStepGuardSupportProof.actualParameterizedCanonicalStepAtSourceTag

theorem actualOriginalUniformGuardedStepCalibration : ActualOriginalUniformGuardedStepCalibration :=
  InternalOriginalUniformStepGuardEvaluationProof.actualOriginalUniformGuardedStepCalibration

theorem actualOriginalUniformCanonicalStepCalibration : ActualOriginalUniformCanonicalStepCalibration :=
  InternalOriginalUniformStepGuardEvaluationProof.actualOriginalUniformCanonicalStepCalibration

theorem actualParameterizedCanonicalStepApplication : ActualParameterizedCanonicalStepApplication :=
  InternalOriginalUniformStepGuardApplicationProof.actualParameterizedCanonicalStepApplication

theorem internalLaws (data : Data) (oldStep : Program 4) : InternalLaws data oldStep := by
  intro body α Delta
  exact ⟨actualParameterizedCanonicalStepAtSourceTag body data oldStep α Delta,
    actualParameterizedCanonicalStepApplication body data oldStep α Delta⟩

/-- The one original step leaf precedes every window, Gamma and symbolic
calculus. All constructed wrappers use that same leaf and unchanged Data. -/
theorem actualOriginalUniformCanonicalStepSelection : ActualOriginalUniformCanonicalStepSelection := by
  intro n arity data hc
  obtain ⟨oldStep,hleaf,_⟩ :=
    InternalOriginalUniformApplicationStepSelectionEvaluationProof.actualOriginalUniformStepLeafProgram n arity
  exact ⟨oldStep,hleaf,
    actualOriginalUniformGuardedStepCalibration n arity data oldStep hc hleaf,
    actualOriginalUniformCanonicalStepCalibration n arity data oldStep hc hleaf,
    internalLaws data oldStep⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardProof
