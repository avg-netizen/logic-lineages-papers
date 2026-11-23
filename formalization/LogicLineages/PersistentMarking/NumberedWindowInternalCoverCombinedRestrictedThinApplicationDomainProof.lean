module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedThinApplicationDomainTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperReportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedThinApplicationDomainProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverCombinedRestrictedWrappedAuxProof (exact_OpenCoverCombinedWrappedAuxFormation)
open NumberedWindowInternalCoverCombinedRestrictedWrapperReportProof (exact_OpenCoverThinMatchingWindowReport)
open NumberedWindowInternalCoverCombinedRestrictedThinApplicationDomainTargets

theorem exact_OpenCoverApplicationHasLeastFromWindow : ExactOpenCoverApplicationHasLeastFromWindow := by
  intro V TV M M0 B T X s body α Γ ctx dom cod f arg P W tv termTypes argument function
  have formed := exact_OpenCoverCombinedWrappedAuxFormation V TV M M0 B T s body α Γ
    ctx dom cod f arg tv termTypes function argument
  obtain ⟨checked⟩ := exact_OpenCoverThinMatchingWindowReport P.cover P.W P.V X s body α Γ
    ctx cod (auxiliaryTerm dom cod f arg) formed
  exact ⟨Derivation.conjunctionRight checked⟩

#print axioms exact_OpenCoverApplicationHasLeastFromWindow
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedThinApplicationDomainProof
