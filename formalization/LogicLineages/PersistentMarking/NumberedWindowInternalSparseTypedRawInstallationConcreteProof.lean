module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawInstallationReinstallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawSelectionChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawInstallationConcreteProof
open NumberedWindowInternalSparseTupleChecks (exact_ConcreteInstalledTuple)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawSelectionChecks (exact_ConcreteTypedRaw5)
open NumberedWindowInternalSparseTypedRawInstallationReinstallProof (reinstall)
open NumberedWindowInternalSparseTypedRawInstallationTargets

theorem concrete : ExactConcreteSparseTypedRawInstalledTuple := by
  intro entries s W valid
  obtain ⟨i,j,cv,tv,d,p₀,oldRaw,least,v,old⟩ := exact_ConcreteInstalledTuple entries s W valid
  obtain ⟨root,other,windowProg,syntaxProg,rootCal,otherCal,syntaxCal,windowCal,newCal⟩ :=
    exact_ConcreteTypedRaw5 entries s
  have installedNew := reinstall entries s W valid i j cv tv d p₀ oldRaw
    (typedRaw5 root other windowProg syntaxProg) least v old newCal
  exact ⟨i,j,cv,tv,d,p₀,oldRaw,least,v,root,other,windowProg,syntaxProg,
    old,rootCal,otherCal,syntaxCal,windowCal,installedNew⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawInstallationConcreteProof
