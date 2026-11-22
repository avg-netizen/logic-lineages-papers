module
public import LogicLineages.PersistentMarking.NumberedWindowInternalGuardedMatchingInstallationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseIntrinsicInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalGuardedMatchedPathChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalOwnCoverReportsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureStepChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalGuardedMatchingInstallationChecks
open NumberedWindowInternalGuardedMatchingInstallationTargets
open NumberedWindowInternalSparseIntrinsicInstallationChecks (exact_InstallIntrinsicPrograms)
open NumberedWindowInternalOwnCoverReportsTargets (syntaxFlag)
open NumberedWindowInternalOwnCoverReportsChecks (exact_SyntaxFlagCalibration)
open NumberedWindowInternalFactoredCoverChecks (exact_SelectedFactoredCover exact_FactoredCoverCalibration)
open NumberedWindowInternalAuxMeasureStepChecks (exact_CombineProgram exact_PhysicalAuxMeasure)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalGuardedMatchedPathChecks (exact_GuardedPath)

theorem exact_GuardedMatchingInstallation : ExactGuardedMatchingInstallation := by
  obtain ⟨baseV,baseM,G,hV,hM,hG,_⟩ := exact_SelectedFactoredCover
  obtain ⟨P,hP⟩ := exact_CombineProgram
  let V := syntaxFlag baseV
  let M := selectedMeasure (measureUpdate baseM P)
  have flag := exact_SyntaxFlagCalibration baseV hV
  have measure := exact_PhysicalAuxMeasure baseM P hM hP
  have cover := exact_FactoredCoverCalibration V M G flag measure hG
  refine ⟨baseV,baseM,P,G,flag,hM,hP,hG,cover,?_⟩
  intro _ _ _ entries s W valid symmetric covered
  obtain ⟨i,j,cv,tv,base,intrinsicBase,T,d,oldCore,oldLeast,root,other,v,hr,ho,hb,hi,ht,
    hk,openK,hx,hw,hl,hs,old,new,same,installed,carriers,oc,me,pw,ec,em,mme,ee,values,fe,sing,path⟩ :=
    exact_InstallIntrinsicPrograms V baseM P G flag hM hP hG entries s W valid symmetric covered
  exact ⟨i,j,cv,tv,base,intrinsicBase,T,d,oldCore,oldLeast,root,other,v,hr,ho,hb,hi,ht,hk,openK,
    hx,hw,hl,hs,old,new,same,installed,carriers,oc,me,pw,ec,em,mme,ee,values,fe,sing,
    exact_GuardedPath baseV M G s intrinsicBase T _ _ path⟩

#print axioms exact_GuardedMatchingInstallation
end LogicLineages.PersistentMarking.NumberedWindowInternalGuardedMatchingInstallationChecks
