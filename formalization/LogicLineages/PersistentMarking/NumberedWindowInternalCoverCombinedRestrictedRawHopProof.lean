module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRawHopTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRawHopLocalProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRawHopProof
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalCoverCombinedRestrictedWrappedAuxProof (exact_OpenCoverCombinedWrappedAuxFormation)
open NumberedWindowInternalCoverCombinedRestrictedRawHopLocalProof (typedRawChildWindows actualWrappedRawLift)
open NumberedWindowInternalCoverCombinedRestrictedRawHopTargets

theorem exact_OpenCoverCombinedRestrictedRawHop : ExactOpenCoverCombinedRestrictedRawHop := by
  intro V TV M M0 B T root other s body α Γ ctx dom cod fn child next arg P W raw syn types input substep
  have ends := typedRawChildWindows root other W P.V ctx (rawCons dom cod) fn child next substep
  have start := exact_OpenCoverCombinedWrappedAuxFormation V TV M M0 B T s body α Γ
    ctx dom cod fn arg syn types ends.1 input
  have target := exact_OpenCoverCombinedWrappedAuxFormation V TV M M0 B T s body α Γ
    ctx dom cod next arg syn types ends.2 input
  exact actualWrappedRawLift P.cover P.W root other P.V s ctx dom cod fn child next arg substep start target

#print axioms exact_OpenCoverCombinedRestrictedRawHop

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRawHopProof
