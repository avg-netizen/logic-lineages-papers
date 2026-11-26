module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGuardedNumberedListTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredNumberedListProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeOnlyArgumentListProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverGuardedNumberedListProof
open NumberedWindowInternalCoverTypeLeafMeasureTargets (typeLeafSharedMeasure)
open NumberedWindowInternalCoverTypeOnlyArgumentListProof (exact_OpenCoverTypeOnlyArgumentList)
open NumberedWindowInternalCoverArgumentGrammarInductionProof (exact_OpenCoverArgumentGrammarInduction)
open NumberedWindowInternalCoverMeasuredNumberedListProof (exact_OpenCoverMeasuredNumberedListScratch)
open NumberedWindowInternalCoverGuardedNumberedListTargets

theorem exact_OpenCoverGuardedNumberedListScratch : ExactOpenCoverGuardedNumberedListScratch := by
  intro V TV M F G B T s body α Γ h ty k l r p vertices ctx result row provider gl gr
  have left := exact_OpenCoverArgumentGrammarInduction F G s body α Γ l provider gl
  have right := exact_OpenCoverArgumentGrammarInduction F G s body α Γ r provider gr
  exact exact_OpenCoverMeasuredNumberedListScratch V TV M F B T s body α Γ h ty k l r p vertices ctx result
    row left right

theorem exact_OpenCoverTypeOnlyNumberedListScratch : ExactOpenCoverTypeOnlyNumberedListScratch := by
  intro V TV M M0 B T s body α Γ h ty k l r p vertices ctx result row gl gr
  have left := exact_OpenCoverTypeOnlyArgumentList s M0 body α Γ l gl
  have right := exact_OpenCoverTypeOnlyArgumentList s M0 body α Γ r gr
  exact exact_OpenCoverMeasuredNumberedListScratch V TV M (typeLeafSharedMeasure M0) B T s body α Γ
    h ty k l r p vertices ctx result row left right

#print axioms exact_OpenCoverGuardedNumberedListScratch
#print axioms exact_OpenCoverTypeOnlyNumberedListScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverGuardedNumberedListProof
