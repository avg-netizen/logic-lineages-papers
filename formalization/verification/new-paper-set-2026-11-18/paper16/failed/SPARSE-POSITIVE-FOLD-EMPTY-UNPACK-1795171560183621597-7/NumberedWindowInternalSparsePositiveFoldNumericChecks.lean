module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldCoreCalibrationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceNumericChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldNumericChecks
open NumberedWindowInternalSparsePositiveFoldTargets
open NumberedWindowInternalSparsePositiveFoldCoreCalibrationProof (composition)
open NumberedWindowInternalSparsePathAdvanceNumericChecks (exact_ConcreteAdvance)

theorem exact_FoldComposition : FoldComposition := composition

theorem exact_ConcretePositive : ConcretePositive := by
  intro entries s
  obtain ⟨raw,least,hr,hl,ha⟩ := exact_ConcreteAdvance entries s
  obtain ⟨hf,hp⟩ := composition entries s raw least ha
  exact ⟨raw,least,hr,hl,ha,hf,hp⟩

#print axioms exact_FoldComposition
#print axioms exact_ConcretePositive
end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldNumericChecks
