module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredExchangeDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSpineRankProgramProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSpineRankedExchangeProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalEqualityTest (equalityTest)
open InternalEqualityTestEvaluationProof (exactEqualityEvaluation)
open InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowExchangeAlgorithm (bits)
open NumberedWindowInternalFactoredCoverNumericProof (invariance)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorOne vectorTwo)
open NumberedWindowInternalMeasuredExchangeThinDefinitions
open NumberedWindowInternalLiteralExchangeSpineRankProof (exact_LiteralExchangeSpineRank)
open NumberedWindowInternalLiteralSpineRankProgramProof (spineRankLeaf exact_LiteralSpineRankProgram)
open NumberedWindowInternalTransparentAuxRankTargets (auxRank)
open NumberedWindowInternalRankMeasuredExchange (RankFit rankedExchange)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange exact_LiteralPairedCalibration)
open NumberedWindowInternalSparseCoverGuardedExchangeNumericProof (calibration)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowScalarAlgorithm (Settings)

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

theorem exact_LiteralSpineMeasuredExchange (s : Settings) (M : Program 1) (X : Program 2)
    (rank : RankFit M) (exchange : ActualTermExchange s X) : ActualTermExchange s (measuredExchange M X) := by
  intro a b
  have acceptedBase := exchange a b
  rw [vectorTwo] at acceptedBase ⊢
  change evaluate X (a ::ᵥ b ::ᵥ nil) = _ at acceptedBase
  change evaluate (measuredExchange M X) (a ::ᵥ b ::ᵥ nil) = _
  rw [measuredExchange,actualConjunctionEvaluation,acceptedBase,compareValue]
  cases bit : (bits s.equivalentHeads a b).1 with
  | false => simp
  | true =>
    have same := exact_LiteralExchangeSpineRank s.equivalentHeads a b bit
    simp [rank a,rank b,same]

/-- The extra rank guard is now an actual calibrated component, so it
does not alter the Boolean exchange of the original checker. -/
theorem exact_LiteralSpineRankedExchange (C : Program 3) (s : Settings) (D : Program 2)
    (cover : ActualSelectedCoverOutput C) (symmetric : HeadPairsSymmetric s.equivalentHeads)
    (fit : ActualTermExchange s D) :
    ActualTermExchange s (rankedExchange C s (auxRank spineRankLeaf) D) := by
  apply calibration C s (pairedExchange (measuredExchange (auxRank spineRankLeaf) D)) cover
  apply exact_LiteralPairedCalibration s _ symmetric
  exact exact_LiteralSpineMeasuredExchange s (auxRank spineRankLeaf) D exact_LiteralSpineRankProgram fit

#print axioms exact_LiteralSpineMeasuredExchange
#print axioms exact_LiteralSpineRankedExchange
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSpineRankedExchangeProof
