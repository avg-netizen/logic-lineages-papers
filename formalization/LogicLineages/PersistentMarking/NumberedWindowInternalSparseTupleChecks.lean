module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleTypedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleReportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleChecks
open NumberedWindowInternalSparseTupleTargets
open NumberedWindowInternalSparseTuplePresentationProof (select)
open NumberedWindowInternalSparseTupleTypedProof (selectTyped)
open NumberedWindowInternalSparseTupleReportProof (installed)
open NumberedWindowInternalSparseAddressPositive (addressPositive)

theorem exact_InstalledPositiveReport : ExactInstalledPositiveReport := installed

theorem exact_ConcreteInstalledTuple : ExactConcreteInstalledTuple := by
  intro xs s W valid
  obtain ⟨i,j,cv,tv,d,raw,least,pr,callbacks⟩ := select xs s
  let r := addressPositive cv tv raw least
  obtain ⟨p₀,v,tuple,guarded⟩ := selectTyped xs s W valid i j r d pr
  exact ⟨i,j,cv,tv,d,p₀,raw,least,v,tuple,guarded,callbacks,installed i j cv tv d raw least⟩

#print axioms exact_InstalledPositiveReport
#print axioms exact_ConcreteInstalledTuple
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleChecks
