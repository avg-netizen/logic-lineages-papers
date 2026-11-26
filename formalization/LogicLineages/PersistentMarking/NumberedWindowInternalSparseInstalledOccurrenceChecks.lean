module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseInstalledOccurrenceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseInstalledOccurrenceChecks
open NumberedWindowInternalSparseInstalledOccurrenceTargets

theorem exact_UnconditionalCoverOccurrence : ExactUnconditionalCoverOccurrence :=
  NumberedWindowInternalSparseCoverOccurrenceChecks.exact_PackedLeastOccurrenceFromPass
    NumberedWindowInternalSparsePackedLeastOpenChecks.exact_OpenPackedLeastPoolOccurrence
    NumberedWindowInternalSparseFilterInclusionChecks.exact_DirectedPassInclusion

theorem exact_InstalledCoverOccurrence : ExactInstalledCoverOccurrence := by
  obtain ⟨C,cover,tuples⟩ := NumberedWindowInternalSparseLeastInstallationChecks.exact_PhysicalLeastInstalledTuple
  refine ⟨C,cover,?_⟩
  intro entries s W valid
  obtain ⟨i,j,cv,tv,syntaxProg,X,d,oldCore,oldLeast,root,other,windowProg,v,hRoot,hOther,
    hSyntax,hWindow,hExchange,hLeast,old,withLeast,chosen,installed⟩ := tuples entries s W valid
  exact ⟨i,j,cv,tv,syntaxProg,X,d,oldCore,oldLeast,root,other,windowProg,v,hRoot,hOther,
    hSyntax,hWindow,hExchange,hLeast,old,withLeast,chosen,installed,
    exact_UnconditionalCoverOccurrence C X windowProg s⟩

#print axioms exact_UnconditionalCoverOccurrence
#print axioms exact_InstalledCoverOccurrence
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseInstalledOccurrenceChecks
