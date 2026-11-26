module
public import LogicLineages.PermittedControl.OriginalMatrixLowDimensionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixLowDimensionCode
open HeterogeneousSignedMatrixSlice (TestCode Row RawRow RowResult RawResult HitRows encodeRow encodeResult)
open HeterogeneousSignedMatrixLowStrips (branches branchesCode encodeBranch)
open MixedSameRankResidue (WeightedCode)
open OriginalMatrixLowDimension (supportSet dimension)
open OriginalMatrixDenseRanks (support)

inductive RawHitRows : List RawResult → List RawRow → Prop where
  | nil : RawHitRows [] []
  | cons {test : TestCode} {b : Int} {terms : List WeightedCode}
      {statuses : List RawResult} {rows : List RawRow} :
      RawHitRows statuses rows →
        RawHitRows ((test,some (some (b,terms))) :: statuses) ((test,b,terms) :: rows)

def rawSupport (rs : List RawRow) : List Nat :=
  rs.flatMap (fun r => r.2.2.map (fun t => t.2.2.1))

def rawSupportSet (rs : List RawRow) : Finset Nat := (rawSupport rs).toFinset

abbrev rawDimension (rs : List RawRow) : Nat := (rawSupportSet rs).card

def ExactRawShape : Prop :=
  (∀ rs : List Row, rawSupport (rs.map encodeRow) = support rs) ∧
  (∀ (status : List RowResult) (rs : List Row), HitRows status rs →
    RawHitRows (status.map encodeResult) (rs.map encodeRow)) ∧
  ∀ (status : List RowResult) (rs : List RawRow), RawHitRows (status.map encodeResult) rs →
    ∃ typed : List Row, HitRows status typed ∧ rs = typed.map encodeRow

/-- Keep the checked code family's very same status list. Only all-hit
branches have children; no decoding default turns a failure into a row. -/
def ExactCodedLowFamilyDimension : Prop :=
  HeterogeneousSignedMatrixLowStrips.CodeExact ∧
  ∀ (f : Nat → Nat) (rank bound : Nat) (source : List Row),
    rank ∈ support source →
    ∀ branch ∈ branchesCode f (rank,bound,source.map encodeRow), ∀ rs : List RawRow,
      RawHitRows branch.2 rs →
        (∃ typed ∈ branches f rank bound source, branch = encodeBranch typed ∧
          ∃ residual : List Row, HitRows typed.2 residual ∧ rs = residual.map encodeRow) ∧
        rawSupportSet rs = (rawSupportSet (source.map encodeRow)).erase rank ∧
        rawDimension rs < rawDimension (source.map encodeRow)

def FullOriginalMatrixLowDimensionCode : Prop := ExactRawShape ∧ ExactCodedLowFamilyDimension

end LogicLineages.PermittedControl.OriginalMatrixLowDimensionCode
