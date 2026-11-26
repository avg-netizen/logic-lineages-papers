module
public import LogicLineages.PermittedControl.ActualRawMixedFamilyCeilingTargets
import LogicLineages.PermittedControl.ActualRawSignedCleanupProof
import LogicLineages.PermittedControl.ActualRawSignedStaticCeilingProof
import LogicLineages.PermittedControl.ActualBitFamilyRawReadCeilingProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawMixedFamilyCeiling
open MixedSameRankResidue (WeightedOperand encodeWeighted weightedTailCode operandTailCode)
open ActualRawSignedStaticCeiling (encodeSyntax exactRawSignedStaticMajorant)
open ActualRawSignedCleanup (cleanupCalibration cleanupCode)
open ActualBitFamilyRawReadCeiling (rowCode rowCalibration)
open ActualBitFamilyRawLayout (encodeBitRow encodeFamily)
open HeterogeneousSignedMatrixSlice (encodeRow)
open ActualGuardedResidualBitFamily (Family)
open OriginalPrintedTerminalBitClauses (BitRow)
open ActualPaidOrderedSyntaxReads (readCeiling)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualInitialSignedCountCleanup (cleanup)
open ActualGreatestCongruenceRoute (modulusMinimum)
open OriginalRankedLiteralClauseHigh (rowNeed clauseNeed familyNeed)
open OriginalPrintedLiteralRowBridge (properClauses)

private theorem modTape (B m : Nat) (ts : List WeightedOperand) :
    weightedTailCode B m (ts.map encodeWeighted) =
      ts.foldr (fun t n => max (weightedTailCode B m [encodeWeighted t]) n) 0 := by
  induction ts with
  | nil => rfl
  | cons head tail ih =>
      change max (operandTailCode B m head.2.code) (weightedTailCode B m (tail.map encodeWeighted)) =
        max (max (operandTailCode B m head.2.code) 0)
          (tail.foldr (fun t n => max (weightedTailCode B m [encodeWeighted t]) n) 0)
      rw [max_eq_left (Nat.zero_le _),ih]

theorem modCalibration (B m : Nat) (s : SyntaxState) :
    weightedTailCode B m (s.terms.map encodeWeighted) = modulusMinimum B m s :=
  modTape B m s.terms

theorem exactRowBound (B r : Nat) (row : BitRow) :
    rowNeed B r row ≤ rowBound B r (encodeBitRow row) := by
  rcases row with ⟨⟨test,c,ts⟩,bit⟩
  let s : SyntaxState := ⟨c,ts⟩
  have read : readCeiling ts ≤ rowCode (encodeRow (test,c,ts)) :=
    le_of_eq (rowCalibration (test,c,ts)).symm
  have hi := exactRawSignedStaticMajorant B r (cleanup s)
  rw [← cleanupCalibration] at hi
  cases test with
  | equalZero => exact max_le_max read hi
  | nonnegative => exact max_le_max read hi
  | positive => exact max_le_max read hi
  | congruence m =>
    have hm : modulusMinimum B m s ≤ weightedTailCode B m (ts.map encodeWeighted) :=
      le_of_eq (modCalibration B m s).symm
    exact max_le_max read hm

theorem exactClauseBound (B r : Nat) (rows : List BitRow) :
    clauseNeed B r rows ≤ clauseBound B r (rows.map encodeBitRow) := by
  induction rows with
  | nil => exact Nat.le_refl _
  | cons row tail ih => exact max_le_max (exactRowBound B r row) ih

/-- Any literal source filter can only omit row costs. This raw bound
does not decide the actual typed proper-clause filter. -/
private theorem anyFilterBound (B r : Nat) (p : List BitRow → Bool) (family : Family) :
    (family.filter p).foldr (fun rows n => max (clauseNeed B r rows) n) 0 ≤
      familyBound B r (encodeFamily family) := by
  induction family with
  | nil => exact Nat.le_refl _
  | cons rows tail ih =>
    change ((rows :: tail).filter p).foldr (fun rs n => max (clauseNeed B r rs) n) 0 ≤
      max (clauseBound B r (rows.map encodeBitRow)) (familyBound B r (encodeFamily tail))
    rw [List.filter_cons]
    split
    · exact max_le_max (exactClauseBound B r rows) ih
    · exact ih.trans (le_max_right _ _)

theorem exactFamilyBound (B r : Nat) (family : Family) :
    familyNeed B r family ≤ familyBound B r (encodeFamily family) := by
  unfold familyNeed properClauses
  exact anyFilterBound B r _ family

theorem exactRawMixedRowMajorants : ExactRawMixedRowMajorants := ⟨modCalibration,exactRowBound⟩
theorem exactRawMixedFamilyMajorants : ExactRawMixedFamilyMajorants := ⟨exactClauseBound,exactFamilyBound⟩

end LogicLineages.PermittedControl.ActualRawMixedFamilyCeiling
