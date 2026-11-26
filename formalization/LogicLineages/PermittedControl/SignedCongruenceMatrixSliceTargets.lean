module
public import LogicLineages.PermittedControl.SignedCongruenceMatrixTargets
public import LogicLineages.PermittedControl.SignedRowCoordinateSliceTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SignedCongruenceMatrixSlice
open PreparedProjection
open MixedRankNamedResidueRow (RawArgs)
open SharedRankResidueRow (SourceRow encodeRow)
open SignedRowCoordinateSlice (Result slice sliceCode encodeResidual)
open SignedCongruenceMatrix (actualRows)

abbrev Args := Nat × Nat × List RawArgs
abbrev RowResult := Nat × Result LowerOperand
abbrev RawResult := Nat × Result LowerOperandCode

noncomputable def sliceRowsCode (f : Nat → Nat) (p : Args) : List RawResult :=
  p.2.2.map (fun r => (r.1,sliceCode f (p.1,p.2.1,r.2.1,r.2.2)))

noncomputable def sliceRows (f : Nat → Nat) (rank a : Nat) (rows : List SourceRow) : List RowResult :=
  rows.map (fun r => (r.1,slice f rank a r.2.1 r.2.2))

def encodeResult (r : RowResult) : RawResult := (r.1,r.2.map (Option.map encodeResidual))

/-- A residual row list is supplied only by actual hits in every slot.
The original order and each original modulus are carried into the rows. -/
inductive HitRows : List RowResult → List SourceRow → Prop where
  | nil : HitRows [] []
  | cons {m : Nat} {b : Int} {rest : List MixedSameRankResidue.WeightedOperand}
      {statuses : List RowResult} {rows : List SourceRow} :
      HitRows statuses rows → HitRows ((m,some (some (b,rest))) :: statuses) ((m,b,rest) :: rows)

def CodeExact : Prop :=
  (∀ f : Nat → Nat, Computable f → Computable (sliceRowsCode f)) ∧
  (∀ (f : Nat → Nat) (p : Args), (sliceRowsCode f p).map Prod.fst = p.2.2.map Prod.fst) ∧
  ∀ (f : Nat → Nat) (rank a : Nat) (rows : List SourceRow),
    sliceRowsCode f (rank,a,rows.map encodeRow) = (sliceRows f rank a rows).map encodeResult

def ResidualRanks : Prop :=
  ∀ (f : Nat → Nat) (rank a : Nat) (rows residual : List SourceRow),
    HitRows (sliceRows f rank a rows) residual →
    ∀ r ∈ residual, ∀ t ∈ r.2.2, t.2.rank ≠ rank

/-- The fixed raw value is shared by every original row. Raw values at
every other rank remain arbitrary throughout the residual conjunction. -/
def ActualJointSlice : Prop :=
  ∀ (f ρ : Nat → Nat) (rank a : Nat) (rows : List SourceRow), ρ rank = a →
    (∀ r ∈ rows, 0 < r.1) →
    ((∃ values : List (List Nat), actualRows f ρ rows values) ↔
      ∃ residual : List SourceRow, HitRows (sliceRows f rank a rows) residual ∧
        ∃ values : List (List Nat), actualRows f ρ residual values)

def FullSignedCongruenceMatrixSlice : Prop := CodeExact ∧ ResidualRanks ∧ ActualJointSlice

end LogicLineages.PermittedControl.SignedCongruenceMatrixSlice
