module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopComposeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedSingletonProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopProof
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalCoverCombinedRestrictedSingletonProof (exact_OpenCoverCombinedRestrictedSingleton)
open NumberedWindowInternalCoverCombinedRestrictedTwoHopComposeProof (exact_OpenCoverThinTwoHop)
open NumberedWindowInternalCoverCombinedRestrictedTwoHopTargets

theorem exact_OpenCoverCombinedRestrictedTwoHop : ExactOpenCoverCombinedRestrictedTwoHop := by
  intro V TV M M0 B T root other X s body α Γ ctx dom cod fn first middle second next arg P W raw syn types input hop1 hop2
  have one := exact_OpenCoverCombinedRestrictedSingleton V TV M M0 B T root other X s body α Γ
    ctx dom cod fn first middle arg syn types input hop1
  have two := exact_OpenCoverCombinedRestrictedSingleton V TV M M0 B T root other X s body α Γ
    ctx dom cod middle second next arg syn types input hop2
  exact exact_OpenCoverThinTwoHop P.cover X W s raw body α Γ ctx cod (auxiliaryTerm dom cod fn arg)
    (functionWitnessTerm first) (auxiliaryTerm dom cod middle arg) (functionWitnessTerm second)
    (auxiliaryTerm dom cod next arg) one two

#print axioms exact_OpenCoverCombinedRestrictedTwoHop
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopProof
