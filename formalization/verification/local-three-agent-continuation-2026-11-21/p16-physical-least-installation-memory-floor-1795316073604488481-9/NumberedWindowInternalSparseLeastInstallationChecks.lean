module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationReinstallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSelectedLeastChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationChecks
open NumberedWindowInternalSparseLeastInstallationTargets
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)

theorem exact_ReinstallCalibratedLeast : ExactReinstallCalibratedLeast :=
  NumberedWindowInternalSparseLeastInstallationReinstallProof.reinstall

theorem exact_PhysicalLeastInstalledTuple : ExactPhysicalLeastInstalledTuple := by
  obtain ⟨C,cover,_⟩ := NumberedWindowInternalSparseSelectedLeastChecks.exact_SelectedPackedLeast
  refine ⟨C,cover,?_⟩
  intro entries s W valid
  obtain ⟨i,j,cv,tv,d,oldCore,_,oldLeast,v,root,other,windowProg,syntaxProg,
      _,hRoot,hOther,hSyntax,hWindow,typedTuple⟩ :=
    NumberedWindowInternalSparseTypedRawInstallationChecks.exact_ConcreteSparseTypedRawInstalledTuple
      entries s W valid
  obtain ⟨X,_,hExchange,_,_⟩ :=
    NumberedWindowInternalSparseScalarEdgeNumericChecks.exact_SelectedPackedScalarEdge s
  let raw := typedRaw5 root other windowProg syntaxProg
  let least := packedLeastProgram C X windowProg s
  have hLeast := NumberedWindowInternalSparsePackedLeastNumericChecks.exact_PackedLeastComposition
    s C X windowProg cover hExchange hWindow
  have leastTuple := exact_ReinstallCalibratedLeast entries s W valid i j cv tv d oldCore
    raw oldLeast least v typedTuple hLeast
  have updated := NumberedWindowInternalSparseApplicationReinstallChecks.exact_ReinstallGuardedApplicationTuple
    entries s W valid i j cv tv d oldCore raw least v leastTuple
  exact ⟨i,j,cv,tv,syntaxProg,X,d,oldCore,oldLeast,root,other,windowProg,v,
    hRoot,hOther,hSyntax,hWindow,hExchange,hLeast,typedTuple,leastTuple,updated⟩

#print axioms exact_ReinstallCalibratedLeast
#print axioms exact_PhysicalLeastInstalledTuple
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationChecks
