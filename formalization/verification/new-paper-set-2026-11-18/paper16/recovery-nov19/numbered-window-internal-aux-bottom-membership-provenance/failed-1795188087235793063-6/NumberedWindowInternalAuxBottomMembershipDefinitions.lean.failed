module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomMembership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalAuxBottomRefinement (refineAuxBottom)

/-- Same actual original r leaf is first refined for bare atoms and then
for a bottom-headed auxiliary target. This is one literal new AST. -/
def augmented (i : Program 1) (r : Program 3) : Program 3 :=
  refineAuxBottom i (refined i r)

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomMembership
