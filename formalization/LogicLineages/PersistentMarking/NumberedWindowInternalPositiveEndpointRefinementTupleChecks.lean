module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTupleTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTuplePresentationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTupleReinstallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTupleChecks
open NumberedWindowInternalPositiveEndpointRefinementTupleTargets
open NumberedWindowInternalPositiveEndpointRefinementTuplePresentationProof (freshPresentation)
open NumberedWindowInternalPositiveEndpointRefinementTupleReinstallProof (sameTuple)
open NumberedWindowInternalSparseTupleChecks (exact_ConcreteInstalledTuple)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalSparseAddressPositive (addressPositive)

theorem exact_EndpointRefinedPresentation : ExactEndpointRefinedPresentation := freshPresentation
theorem exact_ReinstallEndpointRefinedTuple : ExactReinstallEndpointRefinedTuple := sameTuple

theorem exact_ConcreteEndpointRefinedInstalledTuple : ExactConcreteEndpointRefinedInstalledTuple := by
  intro xs s W valid
  obtain ⟨i,j,cv,tv,d,p₀,raw,least,v,installed⟩ := exact_ConcreteInstalledTuple xs s W valid
  let original := addressPositive cv tv raw least
  have old : TupleAt xs s W i j original d v := installed.1
  exact ⟨i,j,cv,tv,d,p₀,raw,least,v,installed,sameTuple xs s W valid i j original d v old⟩

#print axioms exact_EndpointRefinedPresentation
#print axioms exact_ReinstallEndpointRefinedTuple
#print axioms exact_ConcreteEndpointRefinedInstalledTuple

end LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTupleChecks
