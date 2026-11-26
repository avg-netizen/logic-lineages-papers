module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedInstallationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseInstalledOccurrenceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersClosureChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgeChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedInstallationChecks
open NumberedWindowInternalSparseDirectedInstallationTargets
open NumberedWindowInternalSparseRetainedScanChecks (exact_RetainedPredecessor)
open NumberedWindowInternalSparseMembersClosureChecks (exact_LengthStableFromPredecessor exact_MembersEdgeClosure)
open NumberedWindowInternalSparseInstalledOccurrenceChecks (exact_InstalledCoverOccurrence)
open NumberedWindowInternalSparseMinimumEdgeChecks (exact_MinimumEdgeBound)
open NumberedWindowInternalSparsePositiveWindowChecks (exact_PhysicalPositiveWindowsFromRetained)

theorem exact_LengthCutoff : ExactLengthCutoff :=
  exact_LengthStableFromPredecessor exact_RetainedPredecessor

theorem exact_DirectedMembersClosure : ExactDirectedMembersClosure :=
  exact_MembersEdgeClosure exact_RetainedPredecessor

theorem exact_DirectedInstallation : ExactDirectedInstallation := by
  obtain ⟨C,cover,tuples⟩ := exact_InstalledCoverOccurrence
  refine ⟨C,cover,?_⟩
  intro entries s W valid
  obtain ⟨i,j,cv,tv,syntaxProg,X,d,oldCore,oldLeast,root,other,windowProg,v,hRoot,hOther,
    hSyntax,hWindow,hExchange,hLeast,old,withLeast,chosen,installed,openCover⟩ := tuples entries s W valid
  exact ⟨i,j,cv,tv,syntaxProg,X,d,oldCore,oldLeast,root,other,windowProg,v,hRoot,hOther,
    hSyntax,hWindow,hExchange,hLeast,old,withLeast,chosen,installed,openCover,
    exact_MinimumEdgeBound exact_RetainedPredecessor C X windowProg s,
    exact_PhysicalPositiveWindowsFromRetained exact_RetainedPredecessor C X windowProg root other syntaxProg s⟩

#print axioms exact_LengthCutoff
#print axioms exact_DirectedMembersClosure
#print axioms exact_DirectedInstallation
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedInstallationChecks
