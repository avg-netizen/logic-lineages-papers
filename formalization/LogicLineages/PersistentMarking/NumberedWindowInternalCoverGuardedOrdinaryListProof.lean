module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGuardedOrdinaryListTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredOrdinaryListProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeOnlyArgumentListProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverGuardedOrdinaryListProof
open NumberedWindowInternalCoverTypeLeafMeasureTargets (typeLeafSharedMeasure)
open NumberedWindowInternalCoverTypeOnlyArgumentListProof (exact_OpenCoverTypeOnlyArgumentList)
open NumberedWindowInternalCoverArgumentGrammarInductionProof (exact_OpenCoverArgumentGrammarInduction)
open NumberedWindowInternalCoverMeasuredOrdinaryListProof (exact_OpenCoverMeasuredOrdinaryListScratch)
open NumberedWindowInternalCoverGuardedOrdinaryListTargets

theorem exact_OpenCoverGuardedOrdinaryListScratch : ExactOpenCoverGuardedOrdinaryListScratch := by
  intro V TV M F G B T s body α Γ h a p vertices ctx result actual provider guard
  have payload := exact_OpenCoverArgumentGrammarInduction F G s body α Γ a provider guard
  exact exact_OpenCoverMeasuredOrdinaryListScratch V TV M F B T s body α Γ h a p vertices ctx result actual payload

theorem exact_OpenCoverTypeOnlyOrdinaryListScratch : ExactOpenCoverTypeOnlyOrdinaryListScratch := by
  intro V TV M M0 B T s body α Γ h a p vertices ctx result actual guard
  have payload := exact_OpenCoverTypeOnlyArgumentList s M0 body α Γ a guard
  exact exact_OpenCoverMeasuredOrdinaryListScratch V TV M (typeLeafSharedMeasure M0) B T
    s body α Γ h a p vertices ctx result actual payload

#print axioms exact_OpenCoverGuardedOrdinaryListScratch
#print axioms exact_OpenCoverTypeOnlyOrdinaryListScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverGuardedOrdinaryListProof
