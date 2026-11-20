module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceCalibrationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceCallbackProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceNumericChecks
open NumberedWindowInternalSparsePathAdvanceTargets
open NumberedWindowInternalSparsePathAdvanceCalibrationProof (composition)
open NumberedWindowInternalSparsePathAdvanceCallbackProof (rawWitness leastWitness)

theorem exact_AdvanceComposition : AdvanceComposition := composition

theorem exact_ConcreteAdvance : ConcreteAdvance := by
  intro entries s
  obtain ⟨raw,hr⟩ := rawWitness entries s
  obtain ⟨least,hl⟩ := leastWitness s
  exact ⟨raw,least,hr,hl,composition entries s raw least hr hl⟩

#print axioms exact_AdvanceComposition
#print axioms exact_ConcreteAdvance
end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceNumericChecks
