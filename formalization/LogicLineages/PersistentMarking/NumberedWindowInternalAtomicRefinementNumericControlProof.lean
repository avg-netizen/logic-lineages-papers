module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericControlProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowInternalAtomicRefinement NumberedWindowInternalAtomicRefinementNumericTargets
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (compositeTwo compareEvaluation bothEvaluation branchEvaluation zeroEvaluation)
open NumberedWindowInternalAtomicRefinementNumericFieldsProof (sourceValue targetValue)
open NumberedWindowInternalFreshProbeDispatchProgram (bothOne)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)

theorem runBoth (p q : Program 1) (x : Nat) :
    run (bothOne p q) x = if run p x = 1 ∧ run q x = 1 then 1 else 0 :=
  bothEvaluation p q (x ::ᵥ nil)

theorem bothTrue (p q : Program 1) (x : Nat) :
    run (bothOne p q) x = 1 ↔ run p x = 1 ∧ run q x = 1 := by
  rw [runBoth]
  split <;> simp_all

theorem fitsTrue (x : Nat) :
    run storedTypeFits x = 1 ↔ run rawResult x = run storedType x := by
  unfold run storedTypeFits
  rw [compositeTwo,compareEvaluation]
  split <;> simp_all

theorem exactBranches : ExactNumericRefinedBranches := by
  intro i r x w y
  rw [refined,branchEvaluation,branchEvaluation,sourceValue,sourceValue,zeroEvaluation,
    bothEvaluation,bothEvaluation,targetValue]
  by_cases h : evaluate bottomTarget (x ::ᵥ w ::ᵥ y ::ᵥ nil) = 1
  · by_cases g : run i y = 1 <;> simp [h,g]
  · simp [h]

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericControlProof
