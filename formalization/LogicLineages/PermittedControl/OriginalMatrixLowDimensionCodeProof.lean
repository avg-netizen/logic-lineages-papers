module
public import LogicLineages.PermittedControl.OriginalMatrixLowDimensionCodeTargets
import LogicLineages.PermittedControl.OriginalMatrixLowDimensionProof
import LogicLineages.PermittedControl.HeterogeneousSignedMatrixLowStripsCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixLowDimensionCode
open PreparedProjection (LowerOperand)
open MixedSameRankResidue (WeightedOperand encodeWeighted)
open HeterogeneousSignedMatrixSlice (RowResult Row RawRow HitRows encodeTest encodeRow encodeResult)
open HeterogeneousSignedMatrixLowStrips (branches encodeBranch)
open OriginalMatrixLowDimension (supportSet dimension exactLowFamilyDimension)
open OriginalMatrixDenseRanks (support)

private theorem one (terms : List WeightedOperand) :
    (terms.map encodeWeighted).map (fun t => t.2.2.1) = terms.map (fun t => t.2.rank) := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
      rcases t with ⟨w,op⟩
      cases op <;> exact congrArg (List.cons _) ih

theorem exactRawSupport (rs : List Row) : rawSupport (rs.map encodeRow) = support rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      change ((r.2.2.map encodeWeighted).map (fun t => t.2.2.1)) ++ rawSupport (rs.map encodeRow) =
        r.2.2.map (fun t => t.2.rank) ++ support rs
      rw [one,ih]

private theorem encodeHit (status : List RowResult) (rs : List Row) (h : HitRows status rs) :
    RawHitRows (status.map encodeResult) (rs.map encodeRow) := by
  induction h with
  | nil => exact .nil
  | cons _ ih => exact .cons ih

private theorem decodeHit (status : List RowResult) (rs : List RawRow)
    (h : RawHitRows (status.map encodeResult) rs) :
    ∃ typed : List Row, HitRows status typed ∧ rs = typed.map encodeRow := by
  induction status generalizing rs with
  | nil =>
      cases h
      exact ⟨[],HitRows.nil,rfl⟩
  | cons head tail ih =>
      rcases head with ⟨test,status⟩
      cases status with
      | none =>
          change RawHitRows ((encodeTest test,none) :: tail.map encodeResult) rs at h
          cases h
      | some status =>
          cases status with
          | none =>
              change RawHitRows ((encodeTest test,some none) :: tail.map encodeResult) rs at h
              cases h
          | some output =>
              rcases output with ⟨b,ts⟩
              change RawHitRows ((encodeTest test,some (some (b,ts.map encodeWeighted))) ::
                tail.map encodeResult) rs at h
              cases h with
              | cons rest =>
                  obtain ⟨typed,hits,eq⟩ := ih _ rest
                  refine ⟨(test,b,ts) :: typed,.cons hits,?_⟩
                  exact congrArg (List.cons (encodeRow (test,b,ts))) eq

theorem exactRawShape : ExactRawShape := ⟨exactRawSupport,encodeHit,decodeHit⟩

theorem exactCodedLowFamilyDimension : ExactCodedLowFamilyDimension := by
  have code := HeterogeneousSignedMatrixLowStrips.codeExact
  refine ⟨code,?_⟩
  intro f rank bound source used branch member rs hits
  rw [code.2.2 f rank bound source] at member
  obtain ⟨typed,ht,rfl⟩ := List.mem_map.mp member
  obtain ⟨child,live,rfl⟩ := decodeHit typed.2 rs hits
  have decrease := exactLowFamilyDimension f rank bound source used typed ht child live
  refine ⟨⟨typed,ht,rfl,child,live,rfl⟩,?_,?_⟩
  · simpa only [rawSupportSet,exactRawSupport,supportSet] using decrease.1
  · simpa only [rawDimension,rawSupportSet,exactRawSupport,dimension,supportSet] using decrease.2

end LogicLineages.PermittedControl.OriginalMatrixLowDimensionCode
