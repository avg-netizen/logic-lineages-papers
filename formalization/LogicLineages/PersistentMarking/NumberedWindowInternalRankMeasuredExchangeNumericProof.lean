module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowRawExchangeSymmetryTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredExchangeDefinitions
import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineExchangeRankProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredPairedGuardedThinNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredExchangeNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalEqualityTest (equalityTest)
open InternalEqualityTestEvaluationProof (exactEqualityEvaluation)
open InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowExchangeAlgorithm (bits)
open NumberedWindowNeutralSpineExchangeRankProof (exact_OriginalNeutralSpineBitsRank)
open NumberedWindowInternalRankMeasuredExchange
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (exact_LiteralPairedCalibration)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorOne vectorTwo)
open NumberedWindowInternalMeasuredExchangeThinDefinitions

private theorem slotValue (M : Program 1) (i : Fin 2) (xs : List.Vector Nat 2) :
    evaluate (atSlot M i) xs = evaluate M (xs.get i ::ᵥ nil) := by
  change evaluate M (List.Vector.ofFn fun _ : Fin 1 => xs.get i) = _
  rw [vectorOne]

private theorem compareValue (M : Program 1) (a b : Nat) :
    evaluate (compareMeasurements M) (a ::ᵥ b ::ᵥ nil) =
      if evaluate M (a ::ᵥ nil) = evaluate M (b ::ᵥ nil) then 1 else 0 := by
  let xs := a ::ᵥ b ::ᵥ nil
  change evaluate equalityTest (List.Vector.ofFn
    (fun i => evaluate ((![atSlot M 0,atSlot M 1] : Fin 2 → Program 2) i) xs)) = _
  rw [vectorTwo]
  change evaluate equalityTest (evaluate (atSlot M 0) xs ::ᵥ evaluate (atSlot M 1) xs ::ᵥ nil) = _
  rw [slotValue,slotValue,exactEqualityEvaluation] <;> rfl

theorem exact_RankMeasuredDirectedCalibration (s : Settings) (rank : Program 1) (D : Program 2)
    (fit : RankFit rank) (base : ActualTermExchange s D) :
    ActualTermExchange s (measuredExchange rank D) := by
  intro a b
  have acceptedBase := base a b
  rw [vectorTwo] at acceptedBase ⊢
  change evaluate D (a ::ᵥ b ::ᵥ nil) = _ at acceptedBase
  change evaluate (measuredExchange rank D) (a ::ᵥ b ::ᵥ nil) = _
  rw [measuredExchange,actualConjunctionEvaluation,acceptedBase,compareValue]
  cases bit : (bits s.equivalentHeads a b).1 with
  | false => simp
  | true =>
    have same := exact_OriginalNeutralSpineBitsRank s.equivalentHeads a b bit
    have equal : evaluate rank (a ::ᵥ nil) = evaluate rank (b ::ᵥ nil) :=
      (fit a).trans (same.symm.trans (fit b).symm)
    simp [equal]

/-- The existing measured directed D can be passed unchanged, so both
the existing size-measure guard and the new raw-rank guard remain. -/
theorem exact_RankMeasuredFactoredCalibration (C : Program 3) (s : Settings)
    (rank : Program 1) (D : Program 2) (fit : RankFit rank) (base : ActualTermExchange s D)
    (symmetric : HeadPairsSymmetric s.equivalentHeads) (cover : ActualSelectedCoverOutput C) :
    ActualTermExchange s (rankedExchange C s rank D) := by
  have inserted := exact_RankMeasuredDirectedCalibration s rank D fit base
  have paired := exact_LiteralPairedCalibration s (measuredExchange rank D) symmetric inserted
  exact NumberedWindowInternalSparseCoverGuardedExchangeNumericProof.calibration
    C s _ cover paired

#print axioms exact_RankMeasuredDirectedCalibration
#print axioms exact_RankMeasuredFactoredCalibration
end LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredExchangeNumericProof
