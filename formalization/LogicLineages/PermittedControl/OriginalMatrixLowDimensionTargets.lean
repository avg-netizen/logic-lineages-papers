module
public import LogicLineages.PermittedControl.OriginalMatrixDenseRanksTargets
public import LogicLineages.PermittedControl.HeterogeneousSignedMatrixLowStripsTargets
public import Mathlib.Data.Finset.Card

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixLowDimension
open HeterogeneousSignedMatrixSlice (Row HitRows sliceRows)
open HeterogeneousSignedMatrixLowStrips (branches)
open OriginalMatrixDenseRanks (support)

def supportSet (rs : List Row) : Finset Nat := (support rs).toFinset

abbrev dimension (rs : List Row) : Nat := (supportSet rs).card

/-- Every unselected operand stays at the original location relative to
other unselected operands; its signed coefficient and field label stay
literal. A row may become constant, without dropping the original test. -/
def ExactResidualSupportErase : Prop :=
  ∀ (f : Nat → Nat) (rank a : Nat) (source residual : List Row),
    HitRows (sliceRows f rank a source) residual →
    residual.map Prod.fst = source.map Prod.fst ∧
    residual.map (fun r => r.2.2) =
      source.map (fun r => SignedRowCoordinateSlice.untouched rank r.2.2) ∧
    support residual = (support source).filter (fun k => decide (k ≠ rank)) ∧
    supportSet residual = (supportSet source).erase rank

def ExactLowFamilyDimension : Prop :=
  ∀ (f : Nat → Nat) (rank bound : Nat) (source : List Row),
    rank ∈ support source →
    ∀ branch ∈ branches f rank bound source, ∀ residual : List Row,
      HitRows branch.2 residual →
        supportSet residual = (supportSet source).erase rank ∧ dimension residual < dimension source

def FullOriginalMatrixLowDimension : Prop := ExactResidualSupportErase ∧ ExactLowFamilyDimension

end LogicLineages.PermittedControl.OriginalMatrixLowDimension
