module
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldFuelProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPositiveFoldInvariantProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvanceNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPositiveFoldDecodeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (packOfUnpack)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathAdvanceTargets
  (packedOriginalAdvance ActualAdvanceCalibration encodeState decodeState)
open NumberedWindowInternalSparsePositiveFoldTargets (originalFold)
open NumberedWindowInternalParameterizedPositiveFold (evalPhysicalAdvance foldPhysical)
open NumberedWindowInternalZeroRankAdvance (zeroOutput)
open NumberedWindowInternalZeroRankAdvanceNumericProof (exact_OriginalZeroRankAdvanceNumeric)
open NumberedWindowInternalZeroRankPositiveFoldInvariantProof

private theorem decodeEncode (a : Option Nat) : decodeState (encodeState a) = a := by
  cases a <;> rfl

/-- Numerically the exact original physical advance executes the exact
original ordered option fold on the same parser, without extra tests. -/
theorem exact_ParameterizedOriginalFold (xs : Entries) (s : Settings) (raw : Program 5) (L : Program 3)
    (actual : ActualAdvanceCalibration xs s raw L) (c ty start certificate : Nat) :
    foldPhysical (advance raw L) c ty start certificate = originalFold xs s c ty start certificate := by
  have step (state : Option Nat) (hop : Nat) :
      decodeState (evalPhysicalAdvance (advance raw L) c ty (encodeState state) hop) =
        packedOriginalAdvance xs s c ty (encodeState state) hop := by
    unfold evalPhysicalAdvance
    rw [actual,decodeEncode]
  simp only [foldPhysical,originalFold,step]

/-- On a genuinely positive-length certificate, the literal per-hop rank
filter equals filtering the final result of that exact original certificate. -/
theorem exact_OriginalZeroRankPhysicalFold (xs : Entries) (s : Settings)
    (g : Program 1) (raw : Program 5) (L : Program 3)
    (actual : ActualAdvanceCalibration xs s raw L)
    (gFit : ∀ q, evaluate g (q ::ᵥ nil) = rawRank q)
    (c ty start certificate : Nat) (positive : certificate ≠ 0) :
    foldPhysical (zeroOutput g (advance raw L)) c ty start certificate =
      (originalFold xs s c ty start certificate).filter retainsZero := by
  have guarded (state : Option Nat) (hop : Nat) :
      decodeState (evalPhysicalAdvance (zeroOutput g (advance raw L)) c ty (encodeState state) hop) =
        (packedCallback xs s c ty state hop).filter retainsZero := by
    unfold evalPhysicalAdvance
    rw [exact_OriginalZeroRankAdvanceNumeric xs s g raw L actual gFit,decodeEncode] <;> rfl
  cases found : unpack certificate with
  | none =>
    simp only [foldPhysical,originalFold,found,Option.bind_eq_bind,Option.bind_none] <;> rfl
  | some hops =>
    cases hops with
    | nil => exact False.elim (positive (packOfUnpack certificate found))
    | cons hop tail =>
      simp only [foldPhysical,originalFold,found,Option.bind_eq_bind,Option.bind_some,guarded]
      exact exact_OriginalPackedZeroFilterFold xs s c ty hop tail (decodeState start)

#print axioms exact_ParameterizedOriginalFold
#print axioms exact_OriginalZeroRankPhysicalFold

end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPositiveFoldDecodeProof
