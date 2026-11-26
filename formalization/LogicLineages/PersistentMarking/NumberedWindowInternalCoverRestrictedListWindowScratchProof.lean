module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGuardedOrdinaryListProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGuardedNumberedListProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowScratchProof
open NumberedWindowInternalCoverTypeOnlyArgumentListTargets (typeOnlyHeadGuard)
open NumberedWindowInternalCoverRestrictedListWindowReportsProof
  (exact_OpenCoverRestrictedOrdinaryListReport exact_OpenCoverRestrictedNumberedListReports)
open NumberedWindowInternalCoverGuardedOrdinaryListProof (exact_OpenCoverTypeOnlyOrdinaryListScratch)
open NumberedWindowInternalCoverGuardedNumberedListProof (exact_OpenCoverTypeOnlyNumberedListScratch)
open NumberedWindowInternalCoverRestrictedListWindowTargets

theorem exact_OpenCoverRestrictedOrdinaryTypeOnlyScratch : ExactOpenCoverRestrictedOrdinaryTypeOnlyScratch := by
  intro V TV M M0 B T s body α Γ h a p vertices ctx result row
  let G := typeOnlyHeadGuard s
  have guard := exact_OpenCoverRestrictedOrdinaryListReport s G B T body α Γ ctx h a result row.typed
  exact exact_OpenCoverTypeOnlyOrdinaryListScratch V TV M M0 (restrictedListBase G B) T
    s body α Γ h a p vertices ctx result row guard

theorem exact_OpenCoverRestrictedNumberedTypeOnlyScratch : ExactOpenCoverRestrictedNumberedTypeOnlyScratch := by
  intro V TV M M0 B T s body α Γ h ty k l r p vertices ctx result row
  let G := typeOnlyHeadGuard s
  have guards := exact_OpenCoverRestrictedNumberedListReports s G B T body α Γ ctx h ty k l r result row.typed
  exact exact_OpenCoverTypeOnlyNumberedListScratch V TV M M0 (restrictedListBase G B) T
    s body α Γ h ty k l r p vertices ctx result row guards.1 guards.2

#print axioms exact_OpenCoverRestrictedOrdinaryTypeOnlyScratch
#print axioms exact_OpenCoverRestrictedNumberedTypeOnlyScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowScratchProof
