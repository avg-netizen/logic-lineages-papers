module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedMixedListTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMixedLeafHeadProviderProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGuardedOrdinaryListProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGuardedNumberedListProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedMixedListScratchProof
open NumberedWindowInternalCoverNamedLeafMeasureTargets (namedSharedMeasure)
open NumberedWindowInternalCoverMixedLeafArgumentTargets (mixedLeafHead)
open NumberedWindowInternalCoverMixedLeafHeadProviderProof (exact_OpenCoverMixedLeafHeadProvider)
open NumberedWindowInternalCoverRestrictedListWindowTargets (restrictedListBase)
open NumberedWindowInternalCoverRestrictedListWindowReportsProof
  (exact_OpenCoverRestrictedOrdinaryListReport exact_OpenCoverRestrictedNumberedListReports)
open NumberedWindowInternalCoverGuardedOrdinaryListProof (exact_OpenCoverGuardedOrdinaryListScratch)
open NumberedWindowInternalCoverGuardedNumberedListProof (exact_OpenCoverGuardedNumberedListScratch)
open NumberedWindowInternalCoverRestrictedMixedListTargets

theorem exact_OpenCoverRestrictedOrdinaryMixedScratch : ExactOpenCoverRestrictedOrdinaryMixedScratch := by
  intro V TV M M0 B T s body α Γ h a p vertices ctx result row
  let G := mixedLeafHead s
  let F := namedSharedMeasure M0
  have guard := exact_OpenCoverRestrictedOrdinaryListReport s G B T body α Γ ctx h a result row.typed
  have provider := exact_OpenCoverMixedLeafHeadProvider s M0 body
  exact exact_OpenCoverGuardedOrdinaryListScratch V TV M F G (restrictedListBase G B) T
    s body α Γ h a p vertices ctx result row provider guard

theorem exact_OpenCoverRestrictedNumberedMixedScratch : ExactOpenCoverRestrictedNumberedMixedScratch := by
  intro V TV M M0 B T s body α Γ h ty k l r p vertices ctx result row
  let G := mixedLeafHead s
  let F := namedSharedMeasure M0
  have guards := exact_OpenCoverRestrictedNumberedListReports s G B T body α Γ ctx h ty k l r result row.typed
  have provider := exact_OpenCoverMixedLeafHeadProvider s M0 body
  exact exact_OpenCoverGuardedNumberedListScratch V TV M F G (restrictedListBase G B) T
    s body α Γ h ty k l r p vertices ctx result row provider guards.1 guards.2

#print axioms exact_OpenCoverRestrictedOrdinaryMixedScratch
#print axioms exact_OpenCoverRestrictedNumberedMixedScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedMixedListScratchProof
