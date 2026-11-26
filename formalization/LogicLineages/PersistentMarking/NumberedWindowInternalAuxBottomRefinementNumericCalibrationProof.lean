module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementNumericRecognitionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementNumericTerminalProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementNumericCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalAuxBottomRefinement NumberedWindowInternalAuxBottomRefinementNumericTargets
open NumberedWindowInternalAuxBottomRefinementNumericRecognitionProof (exactRecognizer)
open NumberedWindowInternalAuxBottomRefinementNumericTerminalProof (exactTerminal)
open NumberedWindowInternalAtomicRefinement (bottomTarget)
open NumberedWindowInternalAtomicRefinementNumericFieldsProof (exactBottomTarget sourceValue targetValue)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (branchEvaluation bothEvaluation)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowConcreteCheckers (positive)

theorem exactPreserved : ExactOriginalAuxBottomRefinement := by
  intro xs s i r scalarCal old x w y
  rw [refineAuxBottom,branchEvaluation,sourceValue]
  obtain ⟨shape,bit⟩ := exactRecognizer x
  rcases bit with miss | hit
  · rw [if_pos miss,old]
  · have nonzero : run sourceFlag x ≠ 0 := by rw [hit]; exact Nat.one_ne_zero
    rw [if_neg nonzero,acceptedTerminal,bothEvaluation,bothEvaluation,targetValue,old,scalarCal]
    cases ok : positive xs s x w y with
    | false => simp
    | true =>
      obtain ⟨c,dom,cod,stored,a,hx⟩ := shape.mp hit
      obtain ⟨_,_,_,_,_,bottom,_,_,carried⟩ := exactTerminal xs s c dom cod stored a w y (hx ▸ ok)
      have checked : evaluate bottomTarget (x ::ᵥ w ::ᵥ y ::ᵥ nil) = 1 := by
        rw [hx,packedAuxBottom,exactBottomTarget.2,if_pos bottom]
      simp [checked,carried]

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementNumericCalibrationProof
