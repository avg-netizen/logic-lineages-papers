module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureMemoTargets
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesBoundsTableProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureMemoChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalRawListRecursion (lookup)
open NumberedWindowCoverBoundsAlgorithm (bounds table termMeasure)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)
open NumberedWindowRawExchangeVerticesBoundsTableProof (termBounds previous)
open NumberedWindowRawExchangeVerticesCodecProof (nodeBounds)
open NumberedWindowInternalSparseFieldParser (scratchRow scratchTable)
open NumberedWindowInternalSparseFieldParserTableEvaluationProof (rowZero rowSucc lookupAt)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeThree)
open NumberedWindowInternalAuxMeasureMemoTargets

theorem exact_AuxMeasureRecurrence : ExactAuxMeasureRecurrence := by
  intro raw dom cod fn arg read
  have fnBelow := (nodeBounds read).2 fn (by simp)
  have argBelow := (nodeBounds read).2 arg (by simp)
  rw [termBounds read]
  change auxiliaryMeasure ((table raw).getD fn default).1 ((table raw).getD arg default).1 = _
  rw [previous fnBelow,previous argBelow]

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

private theorem rowCorrect (base : Program 1) (R : Program 4) (cal : TermMeasureCalibrated base)
    (step : MeasureStepCalibrated base R) (n : Nat) :
    evaluate (scratchRow (constantZero 2) R) (n ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) = Encodable.encode (bounds n).1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => rw [rowZero]; rfl
    | succ i =>
      rw [rowSucc,step]
      apply stepCorrect base cal
      intro child earlier
      rw [lookupAt (constantZero 2) R (0 ::ᵥ 0 ::ᵥ nil) i child (Nat.le_of_lt_succ earlier)]
      exact ih child earlier

theorem exact_AuxMeasureCalibration : ExactAuxMeasureCalibration := by
  intro base R cal step n
  rw [selectedMeasure,compositeThree]
  exact rowCorrect base R cal step n

#print axioms exact_AuxMeasureRecurrence
#print axioms exact_AuxMeasureCalibration

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureMemoChecks
