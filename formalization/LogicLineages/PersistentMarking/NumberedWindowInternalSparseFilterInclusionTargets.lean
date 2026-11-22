module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundsInclusionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseRoundsInclusionTargets (PassIncluded)

/-- Actual internal containment of the physical directed filter. The
candidate and original ordered vertices are the same on both sides. -/
def ExactDirectedPassInclusion : Prop := ∀ E : Program 4, PassIncluded E

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionTargets
