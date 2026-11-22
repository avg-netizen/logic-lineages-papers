module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFinitePathTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFinitePathPrependProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFinitePathProof
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalCoverCombinedRestrictedFinitePathPrependProof
  (singletonToSuppliedPath prependThinProvided)
open NumberedWindowInternalCoverCombinedRestrictedFinitePathTargets

theorem exact_OpenCoverThinFinitePath : ExactOpenCoverThinFinitePath := by
  intro C X W s raw body α Γ ctx cod src dst chain
  induction chain with
  | last wr actual => exact singletonToSuppliedPath C X W s raw ctx cod _ wr _ actual
  | more wr actual _ ih => exact prependThinProvided C X W s raw ctx cod _ wr _ _ actual ih

theorem exact_OpenCoverCombinedRestrictedFinitePath : ExactOpenCoverCombinedRestrictedFinitePath := by
  intro V TV M M0 B T root other X s body α Γ ctx dom cod arg fn next P W raw chain
  induction chain with
  | last child actual => exact singletonToSuppliedPath P.cover X W s raw ctx cod _
      (functionWitnessTerm child) _ actual
  | more child actual _ ih => exact prependThinProvided P.cover X W s raw ctx cod _
      (functionWitnessTerm child) _ _ actual ih

#print axioms exact_OpenCoverThinFinitePath
#print axioms exact_OpenCoverCombinedRestrictedFinitePath
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFinitePathProof
