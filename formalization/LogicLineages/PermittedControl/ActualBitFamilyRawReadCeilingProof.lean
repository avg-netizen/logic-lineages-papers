module
public import LogicLineages.PermittedControl.ActualBitFamilyRawReadCeilingTargets
import LogicLineages.PermittedControl.ThresholdNoteCodeProof
import LogicLineages.PermittedControl.ActualPaidOrderedSyntaxReadsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawReadCeiling
open OrdinalComparison
open PreparedProjection (LowerOperand)
open MixedSameRankResidue (WeightedOperand encodeWeighted)
open ActualPaidOrderedSyntaxReads (operandMinimum intervalMinimum readCeiling exactPaidOrderedSyntaxReads)
open HeterogeneousSignedMatrixSlice (Row encodeRow)
open OriginalPrintedTerminalBitClauses (BitRow)
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyRawLayout (encodeBitRow encodeFamily)
open ActualBitFamilyLowSlices (coordinates originalRows)
open OriginalMatrixLowDimension (supportSet)
open OriginalMatrixDenseRanks (support)

theorem operandCalibration (op : LowerOperand) : operandCode op.code = operandMinimum op := by
  cases op with
  | coordinate k => rfl
  | ordinary k field =>
      cases field with
      | iterate a => rfl
      | entry a lam mu =>
        change max 2 (max (rawNormCode (rawNoteEncode lam.1)) (rawNormCode (rawNoteEncode mu.1))) =
          intervalMinimum lam mu
        rw [normal_norm_code,normal_norm_code] <;> rfl
  | count k lam mu =>
    change max 2 (max (rawNormCode (rawNoteEncode lam.1)) (rawNormCode (rawNoteEncode mu.1))) =
        intervalMinimum lam mu
    rw [normal_norm_code,normal_norm_code] <;> rfl

theorem termsCalibration (terms : List WeightedOperand) :
    termsCode (terms.map encodeWeighted) = readCeiling terms := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    change max (operandCode t.2.code) (termsCode (ts.map encodeWeighted)) =
      max (operandMinimum t.2) (readCeiling ts)
    rw [operandCalibration,ih]

theorem rowCalibration (r : Row) : rowCode (encodeRow r) = readCeiling r.2.2 :=
  termsCalibration r.2.2

private theorem clauseCalibration (rs : List BitRow) :
    clauseCode (rs.map encodeBitRow) =
      rs.foldr (fun r acc => max (readCeiling r.1.2.2) acc) 0 := by
  induction rs with
  | nil => rfl
  | cons head tail ih =>
      change max (rowCode (encodeRow head.1)) (clauseCode (tail.map encodeBitRow)) =
        max (readCeiling head.1.2.2) (tail.foldr (fun r n => max (readCeiling r.1.2.2) n) 0)
      rw [rowCalibration,ih]

theorem familyCalibration (family : Family) :
    familyCode (encodeFamily family) = familyCeiling family := by
  induction family with
  | nil => rfl
  | cons head tail ih =>
      change max (clauseCode (head.map encodeBitRow)) (familyCode (encodeFamily tail)) =
        max (head.foldr (fun r n => max (readCeiling r.1.2.2) n) 0) (familyCeiling tail)
      rw [clauseCalibration,ih]

theorem exactReadCeilingCalibration : ExactReadCeilingCalibration :=
  ⟨operandCalibration,termsCalibration,rowCalibration,familyCalibration⟩

private theorem costLe {α : Type} (cost : α → Nat)
    (xs : List α) (a : α) (used : a ∈ xs) :
    cost a ≤ xs.foldr (fun x n => max (cost x) n) 0 := by
  induction xs with
  | nil => cases used
  | cons head tail ih =>
      change cost a ≤ max (cost head) (tail.foldr (fun x n => max (cost x) n) 0)
      rcases List.mem_cons.mp used with first | later
      · subst a
        exact le_max_left _ _
      · exact (ih later).trans (le_max_right _ _)

theorem exactRawReadFunding : ExactRawReadFunding := by
  intro f B selected ρ family paid clause inFamily r inClause proper
  have bound : readCeiling r.1.2.2 ≤ familyCode (encodeFamily family) := by
    rw [familyCalibration]
    exact (costLe (fun row : BitRow => readCeiling row.1.2.2) clause r inClause).trans
      (costLe (fun rows : List BitRow =>
        rows.foldr (fun row n => max (readCeiling row.1.2.2) n) 0) family clause inFamily)
  apply exactPaidOrderedSyntaxReads f B selected ρ ⟨r.1.2.1,r.1.2.2⟩ proper
  intro t used
  have k : t.2.rank ∈ coordinates family := by
    change t.2.rank ∈ (support (family.flatMap originalRows)).toFinset
    apply List.mem_toFinset.mpr
    exact List.mem_flatMap.mpr ⟨r.1,
      List.mem_flatMap.mpr ⟨clause,inFamily,List.mem_map.mpr ⟨r,inClause,rfl⟩⟩,
      List.mem_map.mpr ⟨t,used,rfl⟩⟩
  exact bound.trans (paid t.2.rank k)

end LogicLineages.PermittedControl.ActualBitFamilyRawReadCeiling
