module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAddressRankDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankCalibrationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelope
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterAddressProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAddressRankNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
  (evalBranch)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatch (constant)
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowInternalNeutralAddressRank (addressRank)
open NumberedWindowInternalAtomicRefinement (freeSource bottomSource)
open NumberedWindowInternalAtomicRefinementNumericChecks (exact_NumericAtomicRecognizers)
open NumberedWindowInternalAtomicRefinementNumericFieldsProof (literalFields)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawLeast)
open NumberedWindowInternalFreshProbeParsedEmitterAddressProof (addressCoordinates)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowAtomicPositiveTargets (freeAddress bottomAddress)
open NumberedWindowAtomicRawStep (freeRaw bottomRaw)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowNeutralSpineRawRankProof (NeutralSpineRank)
open NumberedWindowNeutralSpineRankCalibrationProof (exact_RawNeutralRankFromShape)

/-- The actual selected rank access follows the original physical raw
least field even at a sparse address. Explicit bare overrides agree
with the same pure numerical rank; no type condition is inferred from
an unparsed integer. -/
theorem exact_OriginalAddressNeutralRank (raw : Program 1)
    (fit : ∀ k, run raw k = rawRank k)
    (q : Nat) (ctx : List Nat) (ty k : Nat) (parsed : addressView q = some (ctx,ty,k)) :
    run (addressRank raw) q = rawRank k := by
  obtain ⟨_,valid,_,_,payload⟩ := addressCoordinates parsed
  obtain ⟨⟨freerec,freebit⟩,⟨bottomrec,bottombit⟩⟩ := exact_NumericAtomicRecognizers q
  change evaluate (addressRank raw) (q ::ᵥ nil) = _
  rw [addressRank,evalBranch]
  change (if run freeSource q = 0 then _ else _) = _
  by_cases f : run freeSource q = 0
  · rw [if_pos f,evalBranch]
    change (if run bottomSource q = 0 then _ else _) = _
    by_cases b : run bottomSource q = 0
    · rw [if_pos b,evalBranch]
      change (if run addressGood q = 0 then _ else _) = _
      rw [valid,if_neg (by decide : (1 : Nat) ≠ 0)]
      change run _ q = _
      rw [applyValue,payload,fit]
    · rw [if_neg b]
      have yes := bottombit.resolve_left b
      obtain ⟨c,t,lit⟩ := bottomrec.mp yes
      have fields : run rawLeast q = bottomRaw t := by
        rw [lit]
        exact (literalFields c t (bottomRaw t)).2.2
      have same := payload.symm.trans fields
      rw [same, exact_RawNeutralRankFromShape (NeutralSpineRank.bottom t)]
      rfl
  · rw [if_neg f]
    have yes := freebit.resolve_left f
    obtain ⟨c,t,n,lit⟩ := freerec.mp yes
    have fields : run rawLeast q = freeRaw t n := by
      rw [lit]
      exact (literalFields c t (freeRaw t n)).2.2
    have same := payload.symm.trans fields
    rw [same, exact_RawNeutralRankFromShape (NeutralSpineRank.free t n)]
    rfl

#print axioms exact_OriginalAddressNeutralRank
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAddressRankNumericProof
