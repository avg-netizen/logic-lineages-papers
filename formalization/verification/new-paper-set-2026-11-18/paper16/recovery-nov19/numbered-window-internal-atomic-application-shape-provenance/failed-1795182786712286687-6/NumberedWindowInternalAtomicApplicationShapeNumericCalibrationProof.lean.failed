module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeNumericFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericRecognizeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeNumericCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalAtomicApplicationShape NumberedWindowInternalAtomicApplicationShapeNumericTargets
open NumberedWindowInternalAtomicApplicationShapeNumericFieldsProof (exactCoordinates)
open NumberedWindowInternalAtomicRefinement (atSource freeSource bottomSource)
open NumberedWindowInternalAtomicRefinementNumericRecognizeProof (exactRecognizers)
open NumberedWindowInternalAtomicRefinementNumericFieldsProof (sourceValue)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (branchEvaluation bothEvaluation)
open NumberedWindowAtomicApplicationTargets (AtomHead)
open NumberedWindowAtomicPositiveTargets (packedAddress freeAddress bottomAddress)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowAddressApplication (graph)
open NumberedWindowInternalSparsePathEnvelope (run)

private theorem atomValue (s : Settings) (p : Program 3) c t k u y (h : AtomHead k)
    (old : ∀ f u y, evaluate p (f ::ᵥ u ::ᵥ y ::ᵥ nil) = (graph s f u y).toNat) :
    evaluate (atomBranch p) (packedAddress c t k ::ᵥ u ::ᵥ y ::ᵥ nil) =
      (graph s (packedAddress c t k) u y).toNat := by
  let f := packedAddress c t k
  cases accepted : graph s f u y with
  | false =>
    rw [atomBranch,bothEvaluation,old,accepted]
    simp
  | true =>
    have checked := exactCoordinates s c t k u y h accepted
    dsimp only at checked
    rw [atomBranch,bothEvaluation,old,accepted,atomicChecks,bothEvaluation,bothEvaluation]
    simp [checked.1,checked.2.1,checked.2.2]

theorem exactPreserved : ExactOriginalShapeRefinedApplication := by
  intro s p old f u y
  rw [refinedApplication,branchEvaluation,sourceValue]
  obtain ⟨⟨freeHit,freeBit⟩,⟨bottomHit,bottomBit⟩⟩ := exactRecognizers f
  rcases freeBit with freeZero | freeOne
  · rw [if_pos freeZero,branchEvaluation,sourceValue]
    rcases bottomBit with bottomZero | bottomOne
    · rw [if_pos bottomZero,old]
    · have nonzero : run bottomSource f ≠ 0 := by rw [bottomOne]; exact Nat.one_ne_zero
      rw [if_neg nonzero]
      obtain ⟨c,t,shape⟩ := bottomHit.mp bottomOne
      rw [shape]
      exact atomValue s p c t _ u y (.bottom t) old
  · have nonzero : run freeSource f ≠ 0 := by rw [freeOne]; exact Nat.one_ne_zero
    rw [if_neg nonzero]
    obtain ⟨c,t,n,shape⟩ := freeHit.mp freeOne
    rw [shape]
    exact atomValue s p c t _ u y (.free t n) old

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeNumericCalibrationProof
