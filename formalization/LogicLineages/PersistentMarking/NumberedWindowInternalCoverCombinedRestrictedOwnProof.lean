module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedMixedListScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedLambdaGuardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaAuxFragmentOwnProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedOwnProof
open NumberedWindowInternalCoverRestrictedLambdaFragmentTargets (lambdaFragmentBase)
open NumberedWindowInternalCoverRestrictedMixedListScratchProof
  (exact_OpenCoverRestrictedOrdinaryMixedScratch exact_OpenCoverRestrictedNumberedMixedScratch)
open NumberedWindowInternalCoverCombinedRestrictedLambdaGuardProof (exact_OpenCoverCombinedRestrictedLambdaGuard)
open NumberedWindowInternalCoverLambdaAuxFragmentOwnProof (exact_OpenCoverLambdaAuxFragmentOwnScratch)
open NumberedWindowInternalCoverNamedLeafMeasureTargets (namedSharedMeasure)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentMeasure)
open NumberedWindowInternalCoverCombinedRestrictedTargets

theorem exact_OpenCoverCombinedRestrictedOrdinaryOwn : ExactOpenCoverCombinedRestrictedOrdinaryOwn := by
  intro V TV M M0 B T s body α Γ h a p vertices ctx result row
  exact exact_OpenCoverRestrictedOrdinaryMixedScratch V TV M M0 (lambdaFragmentBase B) T s body α Γ
    h a p vertices ctx result row

theorem exact_OpenCoverCombinedRestrictedNumberedOwn : ExactOpenCoverCombinedRestrictedNumberedOwn := by
  intro V TV M M0 B T s body α Γ h ty k l r p vertices ctx result row
  exact exact_OpenCoverRestrictedNumberedMixedScratch V TV M M0 (lambdaFragmentBase B) T s body α Γ
    h ty k l r p vertices ctx result row

theorem exact_OpenCoverCombinedRestrictedLambdaOwn : ExactOpenCoverCombinedRestrictedLambdaOwn := by
  intro V TV M M0 B T s body α Γ dom q p vertices ctx result row
  let D := combinedCallback s B
  let A := argumentMeasure (namedSharedMeasure M0)
  have guard := exact_OpenCoverCombinedRestrictedLambdaGuard s B T body α Γ ctx dom q result row.typed
  exact exact_OpenCoverLambdaAuxFragmentOwnScratch V TV M A D T s body α Γ
    dom q p vertices ctx result row guard

#print axioms exact_OpenCoverCombinedRestrictedOrdinaryOwn
#print axioms exact_OpenCoverCombinedRestrictedNumberedOwn
#print axioms exact_OpenCoverCombinedRestrictedLambdaOwn

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedOwnProof
