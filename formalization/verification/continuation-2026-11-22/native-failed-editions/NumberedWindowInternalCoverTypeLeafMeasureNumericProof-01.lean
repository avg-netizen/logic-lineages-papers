module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafMeasureTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMeasureNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafMeasureNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalPairing (pairing)
open InternalPairingEvaluationProof (exactPairingEvaluation)
open NumberedWindowCoverBoundsAlgorithm (bounds termNext termMeasure table)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo literalEvaluation)
open NumberedWindowInternalCoverHeaderFieldsNumericProof (exact_CoverHeaderUnpackNode)
open NumberedWindowInternalCoverSharedMeasureNumericProof (exact_CoverSharedMeasure)
open NumberedWindowInternalCoverTypeLeafMeasureTargets

private theorem pairValue (raw : Nat) :
    evaluate leafPair10 (raw ::ᵥ nil) = Encodable.encode ((1,0) : Nat × Nat) := by
  rw [leafPair10,compositeTwo,literalEvaluation]
  have zero : evaluate (constantZero 1) (raw ::ᵥ nil) = 0 := rfl
  rw [zero,exactPairingEvaluation] <;> simp only [Encodable.encode_prod_val,Encodable.encode_nat]

theorem exact_CoverTypeLeafMeasureBase : ExactCoverTypeLeafMeasureBase := by
  intro M calibrated n
  change evaluate (leafMeasureBase M) (n ::ᵥ nil) = Encodable.encode (bounds n).1
  rw [leafMeasureBase,evalBranch]
  by_cases leaf : run (header 3 1) n = 1
  · obtain ⟨fields,parse,len⟩ := (exact_CoverHeaderUnpackNode 3 1 n).mp leaf
    rcases fields with _ | ⟨ty,_ | ⟨extra,rest⟩⟩ <;> simp at len
    have exactBounds : (bounds n).1 = ((1,0) : Nat × Nat) := by
      simp only [bounds,termNext,parse,Option.map_some,Option.getD_some,termMeasure]
    change evaluate (header 3 1) (n ::ᵥ nil) = 1 at leaf
    rw [leaf,if_neg (by decide),pairValue,exactBounds]
  · by_cases zero : evaluate (header 3 1) (n ::ᵥ nil) = 0
    · rw [if_pos zero]
      exact calibrated n
    · have bits : evaluate (header 3 1) (n ::ᵥ nil) = 0 ∨ evaluate (header 3 1) (n ::ᵥ nil) = 1 := by
        unfold header NumberedWindowInternalSparsePathEnvelope.nodeGood
        rw [InternalAcceptanceCalibrationProof.actualConjunctionEvaluation]
        split <;> simp
      exact False.elim (bits.elim zero (fun one => leaf one))

theorem exact_CoverTypeLeafSharedMeasure : ExactCoverTypeLeafSharedMeasure := by
  intro M calibrated
  exact exact_CoverSharedMeasure (leafMeasureBase M) (exact_CoverTypeLeafMeasureBase M calibrated)

#print axioms exact_CoverTypeLeafMeasureBase
#print axioms exact_CoverTypeLeafSharedMeasure

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafMeasureNumericProof
