module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldProof
open Source InternalOriginalUniformCanonicalResultFold InternalOriginalUniformCanonicalResultFoldTargets

/-- Select the original four binary leaves once. Their existing internal
descent laws, the independently proved generic canonical-fold laws, and
all-input source calibration hold for that same tuple at every window. -/
theorem actualOriginalUniformCanonicalResultFoldSelection :
    ActualOriginalUniformCanonicalResultFoldSelection := by
  intro n arity
  obtain ⟨data,hc,hi,hs⟩ :=
    InternalOriginalUniformDescentSelectionProof.actualOriginalUniformDescentSelection n arity
  refine ⟨data,hc,hi,InternalParameterizedCanonicalResultFoldProof.internalLaws data,?_⟩
  intro symbols S Gamma table hS
  exact ⟨hs symbols S Gamma table hS,
    InternalOriginalUniformCanonicalResultFoldEvaluationProof.actualOriginalUniformCanonicalResultFoldCalibration
      n arity data hc symbols S Gamma table hS⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldProof
