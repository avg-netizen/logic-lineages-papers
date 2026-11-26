module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverInstallationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverInstallationEdgeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseInstalledOccurrenceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgeChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverInstallationChecks
open NumberedWindowInternalSparseCoverInstallationTargets
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeChecks (exact_GuardedExchangeCalibration)
open NumberedWindowInternalSparseDirectedInstallationChecks (exact_DirectedInstallation)
open NumberedWindowInternalSparseRetainedScanChecks (exact_RetainedPredecessor)
open NumberedWindowInternalSparseInstalledOccurrenceChecks (exact_UnconditionalCoverOccurrence)
open NumberedWindowInternalSparseLeastInstallationChecks (exact_ReinstallCalibratedLeast)
open NumberedWindowInternalSparseApplicationReinstallChecks (exact_ReinstallGuardedApplicationTuple)
open NumberedWindowInternalSparsePackedLeastNumericChecks (exact_PackedLeastComposition)
open NumberedWindowInternalSparseMinimumEdgeChecks (exact_MinimumEdgeBound)
open NumberedWindowInternalSparsePositiveWindowChecks (exact_PhysicalPositiveWindowsFromRetained)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)

theorem exact_GuardedEdgeCover : ExactGuardedEdgeCover :=
  NumberedWindowInternalSparseCoverInstallationEdgeProof.edgeCover

theorem exact_CoverInstallation : ExactCoverInstallation := by
  obtain ⟨C,cover,tuples⟩ := exact_DirectedInstallation
  refine ⟨C,cover,?_⟩
  intro entries s W valid
  obtain ⟨i,j,cv,tv,syntaxProg,baseX,d,oldCore,oldLeast,root,other,windowProg,v,hRoot,hOther,
    hSyntax,hWindow,hBase,_,typedTuple,_⟩ := tuples entries s W valid
  let X := guardedExchange C s baseX
  let raw := typedRaw5 root other windowProg syntaxProg
  let least := packedLeastProgram C X windowProg s
  have exchange := exact_GuardedExchangeCalibration C s baseX cover hBase
  have cal := exact_PackedLeastComposition s C X windowProg cover exchange hWindow
  have precise := exact_ReinstallCalibratedLeast entries s W valid i j cv tv d oldCore
    raw oldLeast least v typedTuple cal
  obtain ⟨chosen,updated⟩ := exact_ReinstallGuardedApplicationTuple entries s W valid i j cv tv d oldCore raw least v precise
  exact ⟨i,j,cv,tv,syntaxProg,baseX,d,oldCore,oldLeast,root,other,windowProg,v,hRoot,hOther,
    hSyntax,hWindow,hBase,exchange,cal,typedTuple,precise,chosen,updated,
    exact_UnconditionalCoverOccurrence C X windowProg s,
    exact_MinimumEdgeBound exact_RetainedPredecessor C X windowProg s,
    exact_PhysicalPositiveWindowsFromRetained exact_RetainedPredecessor C X windowProg root other syntaxProg s,
    exact_GuardedEdgeCover C s baseX windowProg⟩

#print axioms exact_GuardedEdgeCover
#print axioms exact_CoverInstallation
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverInstallationChecks
