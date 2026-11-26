module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstall
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)

/-- The sole changed Inputs field is the actual application guard.
In particular the independent probe scalar and option application
are not reselected. -/
def frontendInputs (i : Program 1) (least : Program 3) (v : Inputs) : Inputs :=
  { v with applicationGuard := applicationGuard i least }

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstall
