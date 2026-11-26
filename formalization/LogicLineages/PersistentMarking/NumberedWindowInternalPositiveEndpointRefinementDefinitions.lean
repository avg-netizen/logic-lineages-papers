module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinement
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeDispatchProgram (bothOne)
open NumberedWindowInternalAtomicRefinement (atSource atTarget)

/-- An actual normalized conjunction of the same original three-slot
positive tape with the same scalar program on its two endpoint slots.
The middle slot remains the caller's original supplied witness. -/
def withEndpointCarriers (i : Program 1) (r : Program 3) : Program 3 :=
  bothOne r (bothOne (atSource i) (atTarget i))

end LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinement
