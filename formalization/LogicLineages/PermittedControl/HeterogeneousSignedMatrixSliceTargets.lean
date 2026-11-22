module
public import LogicLineages.PermittedControl.SignedRowGuardedTestTargets

@[expose] public section
namespace LogicLineages.PermittedControl.HeterogeneousSignedMatrixSlice
open PreparedProjection
open MixedSameRankResidue (WeightedOperand WeightedCode encodeWeighted)
open SignedRowCoordinateSlice (Result slice sliceCode encodeResidual untouched)
open SignedRowGuardedTest (Test)
open SignedRowSliceValue (valueAt)

abbrev Row := Test × Int × List WeightedOperand
abbrev TestCode := Nat × Nat
abbrev RawRow := TestCode × Int × List WeightedCode
abbrev RowResult := Test × Result LowerOperand
abbrev RawResult := TestCode × Result LowerOperandCode
abbrev Args := Nat × Nat × List RawRow
abbrev Snapshot := List (Int × Bool)

def encodeTest : Test → TestCode
  | .equalZero => (0,0)
  | .nonnegative => (1,0)
  | .positive => (2,0)
  | .congruence m => (3,m)

def encodeRow (r : Row) : RawRow := (encodeTest r.1,r.2.1,r.2.2.map encodeWeighted)

noncomputable def sliceRowsCode (f : Nat → Nat) (p : Args) : List RawResult :=
  p.2.2.map (fun r => (r.1,sliceCode f (p.1,p.2.1,r.2.1,r.2.2)))

noncomputable def sliceRows (f : Nat → Nat) (rank a : Nat) (rows : List Row) : List RowResult :=
  rows.map (fun r => (r.1,slice f rank a r.2.1 r.2.2))

def encodeResult (r : RowResult) : RawResult :=
  (encodeTest r.1,r.2.map (Option.map encodeResidual))

inductive HitRows : List RowResult → List Row → Prop where
  | nil : HitRows [] []
  | cons {test : Test} {b : Int} {terms : List WeightedOperand}
      {statuses : List RowResult} {rows : List Row} :
      HitRows statuses rows → HitRows ((test,some (some (b,terms))) :: statuses) ((test,b,terms) :: rows)

/-- Each row has a true guarded signed value and its actual test result.
The whole matrix snapshot retains row order and multiplicity. -/
def actualRows (f ρ : Nat → Nat) : List Row → Snapshot → Prop
  | [], [] => True
  | r :: rows, v :: values =>
    r.1.Admitted ∧ valueAt f ρ r.2.1 r.2.2 v.1 ∧ r.1.atPolarity v.2 v.1 ∧ actualRows f ρ rows values
  | _, _ => False

def CodeExact : Prop :=
  (∀ f : Nat → Nat, Computable f → Computable (sliceRowsCode f)) ∧
  (∀ (f : Nat → Nat) (p : Args), (sliceRowsCode f p).map Prod.fst = p.2.2.map Prod.fst) ∧
  ∀ (f : Nat → Nat) (rank a : Nat) (rows : List Row),
    sliceRowsCode f (rank,a,rows.map encodeRow) = (sliceRows f rank a rows).map encodeResult

def ResidualRowsExact : Prop :=
  ∀ (f : Nat → Nat) (rank a : Nat) (rows residual : List Row),
    HitRows (sliceRows f rank a rows) residual →
    residual.map Prod.fst = rows.map Prod.fst ∧
    residual.map (fun r => r.2.2) = rows.map (fun r => untouched rank r.2.2)

def ExactMatrixSnapshots : Prop :=
  ∀ (f ρ : Nat → Nat) (rank a : Nat) (rows : List Row), ρ rank = a →
    ∀ values : Snapshot,
      (actualRows f ρ rows values ↔
        ∃ residual : List Row, HitRows (sliceRows f rank a rows) residual ∧ actualRows f ρ residual values)

def ExactGuardedMatrixTests : Prop :=
  ∀ (f ρ : Nat → Nat) (rank a : Nat) (rows : List Row), ρ rank = a →
    ∀ (test : Snapshot → Prop) (positive : Bool),
      ((∃ values : Snapshot, actualRows f ρ rows values ∧
        (if positive then test values else ¬ test values)) ↔
        ∃ (residual : List Row) (values : Snapshot),
          HitRows (sliceRows f rank a rows) residual ∧ actualRows f ρ residual values ∧
            (if positive then test values else ¬ test values))

def FullHeterogeneousSignedMatrixSlice : Prop :=
  CodeExact ∧ ResidualRowsExact ∧ ExactMatrixSnapshots ∧ ExactGuardedMatrixTests

end LogicLineages.PermittedControl.HeterogeneousSignedMatrixSlice
