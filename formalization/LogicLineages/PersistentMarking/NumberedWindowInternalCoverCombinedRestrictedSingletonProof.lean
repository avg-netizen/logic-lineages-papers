module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedSingletonTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedSingletonCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRawHopLocalProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRawHopProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperReportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedSingletonProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalCoverCombinedRestrictedRawHopLocalProof (typedRawChildWindows)
open NumberedWindowInternalCoverCombinedRestrictedRawHopProof (exact_OpenCoverCombinedRestrictedRawHop)
open NumberedWindowInternalCoverCombinedRestrictedWrapperReportProof (exact_OpenCoverThinMatchingWindowReport)
open NumberedWindowInternalCoverCombinedRestrictedSingletonCoreProof (exact_OpenCoverThinSingletonFromAvailableLeast)
open NumberedWindowInternalCoverCombinedRestrictedSingletonTargets

theorem exact_OpenCoverCombinedRestrictedSingleton : ExactOpenCoverCombinedRestrictedSingleton := by
  intro V TV M M0 B T root other X s body α Γ ctx dom cod fn child next arg P W raw syn types input substep
  let src := auxiliaryTerm dom cod fn arg
  let dst := auxiliaryTerm dom cod next arg
  let wr := functionWitnessTerm child
  have lifted := exact_OpenCoverCombinedRestrictedRawHop V TV M M0 B T root other s body α Γ
    ctx dom cod fn child next arg syn types input substep
  have ends := typedRawChildWindows root other W P.V ctx cod src wr dst lifted
  obtain ⟨initial⟩ := exact_OpenCoverThinMatchingWindowReport P.cover P.W P.V X s body α Γ ctx cod src ends.1
  obtain ⟨final⟩ := exact_OpenCoverThinMatchingWindowReport P.cover P.W P.V X s body α Γ ctx cod dst ends.2
  exact exact_OpenCoverThinSingletonFromAvailableLeast P.cover X W s raw body α Γ ctx cod src wr dst
    lifted ⟨Derivation.conjunctionRight initial⟩ ⟨Derivation.conjunctionRight final⟩

#print axioms exact_OpenCoverCombinedRestrictedSingleton

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedSingletonProof
