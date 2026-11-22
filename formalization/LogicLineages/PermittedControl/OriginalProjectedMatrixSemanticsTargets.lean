module
public import LogicLineages.PermittedControl.OriginalProjectedMatrixDecodeTargets
public import LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshotsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalProjectedMatrixSemantics
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperand PreparedTableTied PlainPreparedFormula lowerOperandRead)
open OriginalMatrixLinearLowerTable (Live)
open OriginalProjectedMatrixDecode (FitsOutput decode LiteralRow)
open OriginalNormalizedMatrixPositiveSnapshots (AllTrue)
open OriginalMixedTerminalTest (Test)
open OriginalPlainTerminalMatrix (snapshot accepts)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open SignedRowSliceValue (valueAt)

/-- One true read guard per literal retained table slot. Its coefficient
is one, and its nonnegative test is precisely true on its actual natural
read; an absent actual read cannot manufacture a Boolean false. -/
def availableRow (op : LowerOperand) : Row := (.nonnegative,0,[(1,op)])

def availabilityRows (ops : List LowerOperand) : List Row := ops.map availableRow

def ExactAvailabilityRows : Prop :=
  (∀ (f ρ : Nat → Nat) (op : LowerOperand) (value : Int),
    valueAt f ρ 0 (availableRow op).2.2 value ↔
      ∃ v : Nat, lowerOperandRead f ρ op = some (some v) ∧ value = (v : Int)) ∧
  (∀ (f ρ : Nat → Nat) (ops : List LowerOperand),
    Live f ρ ops ↔ ∃ guards : Snapshot, actualRows f ρ (availabilityRows ops) guards ∧ AllTrue guards) ∧
  ∀ (f ρ : Nat → Nat) (ops : List LowerOperand) (op : LowerOperand), op ∈ ops →
    (lowerOperandRead f ρ op = none ∨ lowerOperandRead f ρ op = some none) →
      ¬ ∃ guards : Snapshot, actualRows f ρ (availabilityRows ops) guards ∧ AllTrue guards

def ExactDecodedRowSnapshots : Prop :=
  ∀ (f ρ : Nat → Nat) (top : Nat) (ops : List LowerOperand) (ν : Nat → Nat),
    PreparedTableTied f top ρ ops ν →
    ∀ (p : NormalForm.Formula) (rows : List Row), decode ops p = some rows →
      ∀ values : Snapshot, actualRows f ρ rows values ↔ values = snapshot ν p

def ExactDecodedSuffix : Prop :=
  ∀ (f ρ : Nat → Nat) (top : Nat) (ops : List LowerOperand) (ν : Nat → Nat),
    PreparedTableTied f top ρ ops ν →
    ∀ (p : NormalForm.Formula), PlainPreparedFormula p →
      ∀ (rows : List Row), decode ops p = some rows → ∀ positive : Bool,
        (Test.rows p).atPolarity positive ν ↔
          ∃ values : Snapshot, actualRows f ρ rows values ∧ accepts p positive values

/-- Guards and tuple valuations stay positive outside the Boolean suffix. -/
def MatrixAccepts (f ρ : Nat → Nat) (ops : List LowerOperand)
    (p : NormalForm.Formula) (positive : Bool) (rows : List Row) : Prop :=
  ∃ guards values : Snapshot, guards.length = ops.length ∧ AllTrue guards ∧
    actualRows f ρ (availabilityRows ops ++ rows) (guards ++ values) ∧ accepts p positive values

def ExactResidualMatrixInterface : Prop :=
  ∀ (f ρ : Nat → Nat) (top : Nat) (ops : List LowerOperand) (ν : Nat → Nat)
    (p : NormalForm.Formula) (rows : List Row),
    (Live f ρ ops → PreparedTableTied f top ρ ops ν) →
    PlainPreparedFormula p → decode ops p = some rows → ∀ positive : Bool,
    ((Live f ρ ops ∧ (Test.rows p).atPolarity positive ν) ↔
      MatrixAccepts f ρ ops p positive rows)

def FullOriginalProjectedMatrixSemantics : Prop :=
  ExactAvailabilityRows ∧ ExactDecodedRowSnapshots ∧ ExactDecodedSuffix ∧ ExactResidualMatrixInterface

end LogicLineages.PermittedControl.OriginalProjectedMatrixSemantics
