module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedRecursionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureMemoChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureStepChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineNumericProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMeasureNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalRawListRecursion (lookup)
open NumberedWindowCoverBoundsAlgorithm (bounds)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)
open NumberedWindowRawExchangeVerticesCodecProof (nodeBounds)
open NumberedWindowInternalCoverLambdaMeasureRowNumericProof (exact_CoverLambdaMeasureStepCalibration)
open NumberedWindowInternalAuxMeasureMemoTargets
open NumberedWindowInternalAuxMeasureMemoChecks (exact_AuxMeasureRecurrence)
open NumberedWindowInternalAuxMeasureStepChecks (exact_PhysicalAuxMeasureStep)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalChosenAuxMeasureCombineNumericProof (exact_ChosenAuxMeasureCombine)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalSparseFieldParserTableEvaluationProof (rowZero rowSucc lookupAt)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeThree)
open NumberedWindowInternalCoverSharedRecursionTargets

private theorem stepCorrect (base : Program 1) (cal : TermMeasureCalibrated base) (i old : Nat)
    (prior : ∀ n, n < i+1 →
      evaluate lookup ((i-n) ::ᵥ old ::ᵥ nil) = Encodable.encode (bounds n).1) :
    measureStepValue base i old = Encodable.encode (bounds (i+1)).1 := by
  unfold measureStepValue
  split
  next dom cod fn arg read =>
    have fnBelow := (nodeBounds read).2 fn (by simp)
    have argBelow := (nodeBounds read).2 arg (by simp)
    rw [if_pos ⟨fnBelow,argBelow⟩,prior fn fnBelow,prior arg argBelow]
    simp only [combine,readMeasure,Encodable.encodek,Option.getD_some,
      exact_AuxMeasureRecurrence (i+1) dom cod fn arg read]
  next => exact cal (i+1)

theorem exact_CoverSharedMeasureStep : ExactCoverSharedMeasureStep := by
  intro M cm i old previous
  rw [sharedMeasureUpdate,sharedUpdate,evalBranch]
  split
  · rw [exact_PhysicalAuxMeasureStep M chosenCombine exact_ChosenAuxMeasureCombine i old]
    exact stepCorrect M cm i old previous
  · exact exact_CoverLambdaMeasureStepCalibration M cm i old previous

private theorem selectedRow (M : Program 1) (cm : TermMeasureCalibrated M) (n : Nat) :
    evaluate (scratchRow (constantZero 2) (sharedMeasureUpdate M)) (n ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) =
      Encodable.encode (bounds n).1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => rw [rowZero]; rfl
    | succ i =>
      rw [rowSucc]
      apply exact_CoverSharedMeasureStep M cm
      intro child small
      rw [lookupAt (constantZero 2) (sharedMeasureUpdate M) (0 ::ᵥ 0 ::ᵥ nil)
        i child (Nat.le_of_lt_succ small)]
      exact ih child small

theorem exact_CoverSharedMeasure : ExactCoverSharedMeasure := by
  intro M cm n
  unfold sharedMeasure
  rw [selectedMeasure,compositeThree]
  exact selectedRow M cm n

#print axioms exact_CoverSharedMeasureStep
#print axioms exact_CoverSharedMeasure

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMeasureNumericProof
